//! Gap-guided search for pilot programs that crash an exact-rollout filter (`exact`, `fitted`, `exact-rollout`,
//! `exact-rollout-lean`);
//! `--verify F` re-flies them under F.
//! `cargo run --release --no-default-features --features jsb --bin adversary -- OUT_DIR FILTER [trials] [--threads N]`
use cityflight::envfilter::{self, check, Kind};
use cityflight::harness::par_map;
use cityflight::jsb::JsbPlant;
use cityflight::model::*;
use cityflight::sim::*;
use cityflight::world::*;
use std::sync::atomic::Ordering;

const GAPS: [&str; 6] = [
    "push",
    "zoom",
    "fast-dive",
    "slow-idle",
    "bank",
    "spiral",
];

#[derive(Clone, Debug)]
struct Prog {
    gap: usize,
    start: State,
    segs: Vec<(f64, Cmd)>,
}

impl Prog {
    fn cmd(&self, t: f64) -> Cmd {
        let mut acc = 0.0;
        for (d, u) in &self.segs {
            acc += d;
            if t < acc {
                return *u;
            }
        }
        [1.0, 0.0, 1.0]
    }
    fn dur(&self) -> f64 {
        self.segs.iter().map(|s| s.0).sum::<f64>() + 12.0
    }
    fn text(&self) -> String {
        let mut o = format!("gap {}\nstart", GAPS[self.gap]);
        for v in self.start {
            o += &format!(" {v}");
        }
        o += "\n";
        for (d, u) in &self.segs {
            o += &format!("seg {d} {} {} {}\n", u[0], u[1], u[2]);
        }
        o
    }
    fn parse(s: &str) -> Prog {
        let mut p = Prog { gap: 0, start: [0.0; 10], segs: Vec::new() };
        for line in s.lines() {
            let w: Vec<&str> = line.split_whitespace().collect();
            match w.first() {
                Some(&"gap") => p.gap = GAPS.iter().position(|g| *g == w[1]).unwrap_or(0),
                Some(&"start") => {
                    for i in 0..10 {
                        p.start[i] = w[i + 1].parse().unwrap();
                    }
                }
                Some(&"seg") => {
                    let f: Vec<f64> = w[1..].iter().map(|x| x.parse().unwrap()).collect();
                    p.segs.push((f[0], [f[1], f[2], f[3]]));
                }
                _ => {}
            }
        }
        p
    }
}

fn sample(rng: &mut Rng, gap: usize, start: State) -> Prog {
    let r = |rng: &mut Rng, a: f64, b: f64| rng.range(a, b);
    let p0 = |rng: &mut Rng| if rng.chance(0.5) { 0.0 } else { rng.range(-0.15, 0.15) };
    let segs = match gap {
        0 => vec![
            (r(rng, 0.5, 3.0), [1.0, p0(rng), r(rng, 0.4, 1.0)]),
            (r(rng, 0.4, 2.5), [r(rng, -0.3, 0.4), p0(rng), r(rng, 0.0, 1.0)]),
            (r(rng, 0.0, 2.0), [r(rng, 0.5, 1.0), 0.0, r(rng, 0.0, 1.0)]),
        ],
        1 => vec![
            (r(rng, 1.5, 4.0), [r(rng, 1.8, 2.8), p0(rng), r(rng, 0.0, 0.3)]),
            (r(rng, 0.5, 3.0), [r(rng, 0.0, 0.6), p0(rng), 0.0]),
            (r(rng, 0.0, 2.0), [r(rng, 0.6, 1.2), 0.0, r(rng, 0.0, 0.5)]),
        ],
        2 => vec![
            (r(rng, 2.0, 6.0), [r(rng, 0.1, 0.6), p0(rng), 1.0]),
            (r(rng, 0.0, 3.0), [r(rng, 0.7, 1.1), 0.0, 1.0]),
        ],
        3 => vec![
            (r(rng, 3.0, 10.0), [r(rng, 0.95, 1.15), p0(rng), 0.0]),
            (r(rng, 0.0, 3.0), [r(rng, 0.8, 1.0), 0.0, r(rng, 0.0, 0.3)]),
        ],
        4 => {
            let s = if rng.chance(0.5) { 1.0 } else { -1.0 };
            vec![
                (r(rng, 0.5, 1.4), [1.2, s * r(rng, 0.6, 1.0), r(rng, 0.3, 1.0)]),
                (r(rng, 1.0, 4.0), [r(rng, 1.4, 2.8), 0.0, r(rng, 0.3, 1.0)]),
                (r(rng, 0.0, 2.0), [r(rng, 0.3, 0.9), 0.0, r(rng, 0.0, 1.0)]),
            ]
        }
        // A descending spiral: roll in, hold the bank under-pulling, then tighten or roll out late.
        _ => {
            let s = if rng.chance(0.5) { 1.0 } else { -1.0 };
            vec![
                (r(rng, 0.6, 1.6), [1.0, s * r(rng, 0.5, 1.0), r(rng, 0.0, 0.6)]),
                (r(rng, 2.0, 8.0), [r(rng, 0.9, 1.3), 0.0, r(rng, 0.0, 0.6)]),
                (r(rng, 0.0, 3.0), [r(rng, 1.5, 2.6), s * r(rng, -0.3, 0.3), r(rng, 0.0, 1.0)]),
            ]
        }
    };
    Prog { gap, start, segs }
}

fn mutate(rng: &mut Rng, p: &Prog) -> Prog {
    let mut q = p.clone();
    for (d, u) in &mut q.segs {
        *d = (*d * rng.range(0.75, 1.3)).max(0.0);
        u[0] += rng.range(-0.15, 0.15);
        u[1] += rng.range(-0.05, 0.05);
        u[2] = (u[2] + rng.range(-0.15, 0.15)).clamp(0.0, 1.0);
    }
    q
}

fn fly(world: &World, p: &Prog) -> (f64, bool) {
    let cfg = SimCfg { filter_on: true, filter: cityflight::filter::FilterCfg { phase: cityflight::filter::Phase::P1, robust: false }, mismatch: false, seed: 0 };
    let mut sim = Sim::new(world, p.start, cfg);
    let mut started = None;
    for k in 0..(p.dur() / DT_F) as usize {
        sim.tick(p.cmd(k as f64 * DT_F));
        if started.is_none() {
            started = Some(sim.fs.mode != cityflight::filter::Mode::Commit);
        }
        if sim.crashed {
            break;
        }
    }
    (sim.min_true_clear, started.unwrap_or(false))
}

fn verified_start(world: &World, s: &State) -> bool {
    if cityflight::leangate::enabled() {
        return cityflight::leangate::LeanGate::new(s).start_ok;
    }
    let p = JsbPlant::new(s);
    match envfilter::kind() {
        Some(Kind::Gate) => envfilter::Gate::new(world, &p).witness.is_some(),
        Some(k) => check(world, k, &p).0.is_some(),
        None => true,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out = args[0].clone();
    let filt = envfilter::parse(&args[1]);
    let lean_arg = |f: &str| {
        if f == "exact-rollout-lean" {
            assert!(cityflight::jsb::fuel_freeze_default(), "--fuel-drain does not combine with exact-rollout-lean");
            cityflight::leangate::LEAN_GATE.store(true, Ordering::Relaxed);
        }
    };
    let trials: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(400);
    cityflight::jsb::parse_fuel_args(&args);
    cityflight::jsb::JSB_PLANT.store(true, Ordering::Relaxed);
    if let Some(l) = args.iter().position(|a| a == "--law").and_then(|i| args.get(i + 1)) {
        envfilter::LAW_SEL.store(envfilter::parse_law(l), std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(n) = args.iter().position(|a| a == "--escapes").and_then(|i| args.get(i + 1)?.parse().ok()) {
        envfilter::N_USED.store(n, Ordering::Relaxed);
    }
    let world = World::new(1337);
    let threads = args
        .iter()
        .position(|a| a == "--threads")
        .and_then(|i| args.get(i + 1)?.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
    if let Some(i) = args.iter().position(|a| a == "--verify") {
        lean_arg(&args[i + 1]);
        envfilter::ENV_FILTER.store(envfilter::parse(&args[i + 1]), Ordering::Relaxed);
        if matches!(envfilter::kind(), Some(Kind::Fitted { .. })) {
            envfilter::table();
        }
        let mut files: Vec<String> = std::fs::read_dir(&out).unwrap().filter_map(|e| e.ok()).map(|e| e.path().display().to_string()).filter(|p| p.ends_with(".prog")).collect();
        files.sort();
        let res = par_map(files, threads, |f| (f.clone(), fly(&world, &Prog::parse(&std::fs::read_to_string(f).unwrap())).0), |_, _| {});
        let n = res.iter().filter(|r| r.1 < 0.0).count();
        for (f, c) in &res {
            println!("{f}: min clearance {c:.1} m{}", if *c < 0.0 { "  CRASH" } else { "" });
        }
        println!("{n} / {} crash under {}", res.len(), args[i + 1]);
        return;
    }
    lean_arg(&args[1]);
    envfilter::ENV_FILTER.store(filt, Ordering::Relaxed);
    if matches!(envfilter::kind(), Some(Kind::Fitted { .. })) {
        envfilter::table();
    }
    std::fs::create_dir_all(&out).unwrap();
    let starts: Vec<State> = par_map(
        (0..(trials as u64 * 3)).collect(),
        threads,
        |&e| {
            let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xADE5);
            let s = random_start(&world, &mut rng);
            if verified_start(&world, &s) { Some(s) } else { None }
        },
        |_, _| {},
    )
    .into_iter()
    .flatten()
    .take(trials)
    .collect();
    println!("{} verified starts", starts.len());
    if args.iter().any(|a| a == "--debug") {
        for e in 0..10u64 {
            let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xADE5);
            let s = random_start(&world, &mut rng);
            let p = JsbPlant::new(&s);
            for esc in 0..envfilter::n_esc() {
                let r = envfilter::rollout(&world, &p, esc, usize::MAX);
                println!("{e}: z={:.0} v={:.1} {:8} {:?} at t={:.1} min clear {:.1}", s[Z], s[V], envfilter::ESCAPES[esc].name, r.outcome, r.t, r.min_clear);
            }
        }
    }
    for gap in 0..GAPS.len() {
        let jobs: Vec<(u64, State)> = starts.iter().enumerate().map(|(i, s)| (i as u64, *s)).collect();
        let mut res: Vec<(f64, Prog)> = par_map(
            jobs,
            threads,
            |(i, s)| {
                let mut rng = Rng::new(*i * 31 + gap as u64);
                let p = sample(&mut rng, gap, *s);
                let (c, ok) = fly(&world, &p);
                (if ok { c } else { f64::INFINITY }, p)
            },
            |_, _| {},
        );
        res.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let seeds: Vec<(u64, Prog)> = res.iter().take(40).enumerate().flat_map(|(i, (_, p))| (0..6).map(move |k| ((i * 6 + k) as u64, p.clone()))).collect();
        let more: Vec<(f64, Prog)> = par_map(
            seeds,
            threads,
            |(i, p)| {
                let mut rng = Rng::new(*i * 977 + 13 + gap as u64);
                let q = mutate(&mut rng, p);
                let (c, ok) = fly(&world, &q);
                (if ok { c } else { f64::INFINITY }, q)
            },
            |_, _| {},
        );
        res.extend(more);
        let crashes: Vec<&(f64, Prog)> = res.iter().filter(|r| r.0 < 0.0).collect();
        for (k, (_, p)) in crashes.iter().enumerate() {
            std::fs::write(format!("{out}/{}-{k:03}.prog", GAPS[gap]), p.text()).unwrap();
        }
        println!("gap {:10}: {} crashes from {} flights", GAPS[gap], crashes.len(), res.len());
    }
}
