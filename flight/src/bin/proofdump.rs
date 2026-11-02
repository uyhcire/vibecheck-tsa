//! `proofdump OUT RUN`: what the gate holds as verified, per tick, for drawing over `--record` footage (flight/README.md).
use cityflight::envfilter::{EndSet, Law, ESCAPES};
use cityflight::filter::*;
use cityflight::model::*;
use cityflight::pilot::*;
use cityflight::sim::*;
use cityflight::world::*;
use std::fmt::Write as _;
use std::io::Write as _;

enum P {
    Showcase(Showcase),
    Kamikaze(Kamikaze),
    Hostile(Hostile),
}

fn f3(v: &[f64; 3]) -> String {
    format!("[{:.2},{:.2},{:.2}]", v[0], v[1], v[2])
}

/// The tightest point under an end set's footprint: the smallest gap (m) between the floor the terminal test
/// requires (`R_BODY + MARGIN` under the climb) and a raw cell under the footprint, and that cell `[x, y, h]`.
fn tightest(world: &World, e: &EndSet) -> (f64, [f64; 3]) {
    let mut best = (f64::INFINITY, [0.0; 3]);
    let under = R_BODY + cityflight::envfilter::MARGIN;
    match *e {
        EndSet::Helix { c, r, m, z, .. } => {
            let (r0, r1) = ((r - m - R_BODY).max(0.0), r + m + R_BODY);
            let raw = &world.raw;
            let ((i0, j0), (i1, j1)) = (raw.cell(c[0] - r1, c[1] - r1), raw.cell(c[0] + r1, c[1] + r1));
            for j in j0..=j1 {
                for i in i0..=i1 {
                    let (x, y) = (raw.x0 + (i as f64 + 0.5) * CELL, raw.y0 + (j as f64 + 0.5) * CELL);
                    let d = (x - c[0]).hypot(y - c[1]);
                    let h = raw.v[j * raw.nx + i] as f64;
                    if d >= r0 && d <= r1 && z - under - h < best.0 {
                        best = (z - under - h, [x, y, h]);
                    }
                }
            }
        }
        EndSet::Ray { p, psi, grad, end } => {
            let (c, s) = (psi.cos(), psi.sin());
            let len = (end[0] - p[0]).hypot(end[1] - p[1]);
            let mut d = 0.0;
            while d <= len {
                let (x, y, floor) = (p[0] + d * c, p[1] + d * s, p[2] + d * grad - under);
                let w = R_BODY + 5.0 + 0.02 * d;
                let mut l = -w;
                while l <= w {
                    let h = world.surface(x - l * s, y + l * c);
                    if floor - h < best.0 {
                        best = (floor - h, [x - l * s, y + l * c, h]);
                    }
                    l += 0.5 * CELL;
                }
                d += 0.5 * CELL;
            }
        }
    }
    best
}

fn end_json(world: &World, e: &Option<EndSet>, detail: bool) -> String {
    let Some(e) = e else { return "null".into() };
    let tight = if detail {
        let (gap, at) = tightest(world, e);
        format!("\"gap\":{gap:.2},\"gap_at\":{}", f3(&at))
    } else {
        "\"gap\":null".into()
    };
    match e {
        EndSet::Ray { p, psi, grad, end } => {
            format!("{{\"kind\":\"ray\",\"p\":{},\"psi\":{psi:.6},\"grad\":{grad:.6},\"end\":{},{tight}}}", f3(p), f3(end))
        }
        EndSet::Helix { c, r, m, z, vz, vh, dir } => format!(
            "{{\"kind\":\"helix\",\"c\":[{:.2},{:.2}],\"r\":{r:.3},\"m\":{m:.3},\"z\":{z:.2},\"vz\":{vz:.4},\"vh\":{vh:.4},\"dir\":{dir},{tight}}}",
            c[0], c[1]
        ),
    }
}

fn settle(world: &World, plant: &cityflight::jsb::JsbPlant, law: Law, secs: f64) -> String {
    let mut q = plant.fork();
    let mut law = law;
    let n = (secs / cityflight::jsb::DT_JSB).round() as usize;
    let mut rows = Vec::with_capacity(n / 8 + 1);
    let mut psi_prev = f64::NAN;
    for k in 0..=n {
        if k > 0 {
            law.step(world, &mut q);
        }
        if k % cityflight::envfilter::SAMPLE == 0 {
            let s = q.state();
            let o = &q.obs;
            let mut psi = o.vned[0].atan2(o.vned[1]);
            if !psi_prev.is_nan() {
                psi = psi_prev + (psi - psi_prev + std::f64::consts::PI).rem_euclid(2.0 * std::f64::consts::PI) - std::f64::consts::PI;
            }
            psi_prev = psi;
            let vh = o.vned[0].hypot(o.vned[1]);
            rows.push(format!(
                "[{:.4},{:.2},{:.2},{:.2},{:.4},{:.4},{:.5},{:.5},{:.4}]",
                k as f64 * cityflight::jsb::DT_JSB,
                s[X],
                s[Y],
                s[Z],
                o.vt,
                -o.vned[2],
                o.phi,
                psi,
                vh
            ));
        }
    }
    rows.join(",")
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out = std::path::PathBuf::from(args.first().expect("usage: proofdump OUT RUN [--secs S] [--settle-secs S]"));
    let name = args.get(1).cloned().unwrap_or_else(|| "showcase".into());
    let num = |k: &str, d: f64| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(d);
    let (dur, settle_secs) = (num("--secs", 60.0), num("--settle-secs", 40.0));
    // The footprint scan in `tightest` is slow for long rays, so only ticks from `--detail-from` (s) get it.
    let detail_from = num("--detail-from", 0.0);
    // `--fan T1,T2,...`: at those tick times, every candidate flown to its own verdict, in `fan.jsonl`.
    let fan_at: Vec<f64> = args.iter().position(|a| a == "--fan").and_then(|i| args.get(i + 1)).map_or(Vec::new(), |s| s.split(',').filter_map(|x| x.parse().ok()).collect());
    cityflight::jsb::parse_fuel_args(&args);
    cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    cityflight::envfilter::ENV_FILTER.store(cityflight::envfilter::parse("exact-rollout"), std::sync::atomic::Ordering::Relaxed);
    cityflight::envfilter::TIME_CAP_MS.store(0, std::sync::atomic::Ordering::Relaxed);
    // Matches the GUI, so the verdicts are the full-horizon ones a `--record` of the same run flies.
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get().saturating_sub(1)).clamp(1, cityflight::envfilter::N_ESC);
    cityflight::envfilter::CHECK_THREADS.store(threads, std::sync::atomic::Ordering::Relaxed);
    let world = World::new(1337);

    let (s0, seed, mut pilot) = if name == "showcase" {
        (scenario_start(&world, 4), 3, P::Showcase(Showcase::new(street_x(GAP_STREET))))
    } else {
        let e: u64 = name.trim_start_matches("ep").parse().expect("RUN: showcase or ep<N>");
        if e >= 1000 {
            (scenario_start(&world, ((e - 1000) as usize).min(SCENARIOS.len() - 1)), e, P::Kamikaze(Kamikaze::new(e)))
        } else {
            let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xE915);
            let s0 = random_start(&world, &mut rng);
            (s0, e, if e % 4 == 3 { P::Kamikaze(Kamikaze::new(e)) } else { P::Hostile(Hostile::new(e)) })
        }
    };
    // `--pilot hostile:N` or `kamikaze:N`: the run's start with another pilot (one start, many pilots).
    if let Some(p) = args.iter().position(|a| a == "--pilot").and_then(|i| args.get(i + 1)) {
        let (kind, n) = p.split_once(':').expect("--pilot hostile:N or kamikaze:N");
        let n: u64 = n.parse().expect("--pilot KIND:N");
        pilot = if kind == "kamikaze" { P::Kamikaze(Kamikaze::new(n)) } else { P::Hostile(Hostile::new(n)) };
    }
    let cfg = SimCfg { filter_on: true, filter: FilterCfg { phase: Phase::P1, robust: false }, wind: false, model_error: false, seed };
    let mut sim = Sim::new(&world, s0, cfg);
    if args.iter().any(|a| a == "--off") {
        sim.set_filter(false);
    }
    let mut fbw = Fbw::from_state(&s0);

    std::fs::create_dir_all(&out).expect("proofdump: cannot create OUT");
    let open = |f: &str| std::io::BufWriter::new(std::fs::File::create(out.join(f)).expect("proofdump: cannot write"));
    let (mut ticks, mut paths, mut settles) = (open("ticks.jsonl"), open("paths.jsonl"), open("settle.jsonl"));
    let mut fans = open("fan.jsonl");
    let bx: Vec<String> = world.boxes.iter().map(|b| format!("[{:.1},{:.1},{:.1},{:.1},{:.1},{:.1}]", b.x0, b.x1, b.y0, b.y1, b.z0, b.z1)).collect();
    std::fs::write(out.join("boxes.json"), format!("[{}]\n", bx.join(","))).expect("proofdump: cannot write boxes.json");
    let mut last_path: Vec<[f64; 3]> = Vec::new();
    let mut held_id: i64 = -1;
    let mut path_id: i64 = -1;
    let mut last_failed: Vec<[f64; 3]> = Vec::new();
    let mut failed_id: i64 = -1;
    let mut prev_mode = Mode::Free;
    let n = (dur / DT_F).round() as u64;
    let mut takeovers = 0;
    for k in 0..n {
        match &mut pilot {
            P::Showcase(p) => p.update(&sim.s, &mut fbw, DT_F),
            P::Kamikaze(p) => p.update(&world, &sim.s, &mut fbw, DT_F),
            P::Hostile(p) => p.update(&mut fbw, DT_F),
        }
        let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
        let t_next = (k + 1) as f64 * DT_F;
        cityflight::envfilter::FAN.store(fan_at.iter().any(|t| (t - t_next).abs() < 0.005), std::sync::atomic::Ordering::Relaxed);
        sim.tick(u);
        if let Some(f) = sim.env_gate.as_ref().and_then(|g| g.fan.as_ref()).filter(|_| cityflight::envfilter::FAN.load(std::sync::atomic::Ordering::Relaxed)) {
            let cands: Vec<String> = f
                .laws
                .iter()
                .zip(&f.rolls)
                .enumerate()
                .map(|(i, (l, r))| {
                    let pts: Vec<String> = r.path.iter().chain(&r.tail).map(|q| format!("[{:.1},{:.1},{:.1}]", q[0], q[1], q[2])).collect();
                    format!(
                        "{{\"order\":{i},\"escape\":\"{}\",\"resumed\":{},\"outcome\":\"{:?}\",\"min_clear\":{:.3},\"t\":{:.3},\"tail\":{},\"path\":[{}]}}",
                        ESCAPES[l.esc].name,
                        l.t > 0.0,
                        r.outcome,
                        r.min_clear.min(9999.0),
                        r.t,
                        r.tail.len(),
                        pts.join(",")
                    )
                })
                .collect();
            writeln!(
                fans,
                "{{\"t\":{:.2},\"holding\":{},\"cand_clear\":{},\"found\":{},\"accepted\":{},\"mode\":\"{}\",\"cands\":[{}]}}",
                sim.time(),
                f.holding,
                f.cand_clear,
                f.found.map_or("null".into(), |i| i.to_string()),
                f.accepted,
                if sim.fs.mode == Mode::Commit { "escape" } else { "pilot" },
                cands.join(",")
            )
            .unwrap();
        }
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        let Some(g) = sim.env_gate.as_ref() else {
            let s = &sim.s;
            writeln!(
                ticks,
                "{{\"k\":{k},\"t\":{:.2},\"mode\":\"off\",\"pos\":{},\"phi\":{:.4},\"clear\":{:.3},\"crashed\":{},\"escape\":null,\"path\":-1,\"failed\":-1,\"end\":null}}",
                sim.time(),
                f3(&[s[X], s[Y], s[Z]]),
                s[PHI],
                sim.true_clear.min(9999.0),
                sim.crashed
            )
            .unwrap();
            if sim.crashed {
                break;
            }
            continue;
        };
        let mode = sim.fs.mode;
        let committed = g.law.is_some();
        let (path, end) = if committed { (&g.committed_path, g.committed_end) } else { (&g.witness_path, g.witness_end) };
        if *path != last_path {
            path_id += 1;
            held_id = path_id;
            last_path = path.clone();
            let pts: Vec<String> = path.iter().map(|q| format!("[{:.2},{:.2},{:.2}]", q[0], q[1], q[2])).collect();
            writeln!(paths, "{{\"id\":{path_id},\"t\":{:.2},\"path\":[{}]}}", sim.time(), pts.join(",")).unwrap();
        }
        // `shown` is the last rollout that failed when none verified: the pilot's input followed by an escape.
        let failed = if g.shown_ok || g.shown.is_empty() {
            -1
        } else {
            if g.shown != last_failed {
                path_id += 1;
                failed_id = path_id;
                last_failed = g.shown.clone();
                let pts: Vec<String> = g.shown.iter().map(|q| format!("[{:.2},{:.2},{:.2}]", q[0], q[1], q[2])).collect();
                writeln!(paths, "{{\"id\":{path_id},\"t\":{:.2},\"failed\":true,\"path\":[{}]}}", sim.time(), pts.join(",")).unwrap();
            }
            failed_id
        };
        let esc = g.law.or(g.witness).map(|l| ESCAPES[l.esc].name);
        let mode_s = match mode {
            Mode::Off => "off",
            Mode::Free => "pilot",
            Mode::Blend => "blend",
            Mode::Commit => "escape",
        };
        let s = &sim.s;
        let o = sim.jsb.as_ref().map(|p| p.obs);
        let (vz, vt, track) = o.map_or((f64::NAN, f64::NAN, f64::NAN), |o| (-o.vned[2], o.vt, o.vned[0].atan2(o.vned[1])));
        let mut line = String::new();
        write!(
            line,
            "{{\"k\":{k},\"t\":{:.2},\"mode\":\"{mode_s}\",\"pos\":{},\"v\":{vt:.3},\"vz\":{vz:.3},\"phi\":{:.4},\"track\":{track:.5},\"clear\":{:.3},\"escape\":{},\"path\":{held_id},\"failed\":{failed},\"end\":{}}}",
            sim.time(),
            f3(&[s[X], s[Y], s[Z]]),
            s[PHI],
            sim.true_clear.min(9999.0),
            esc.map_or("null".to_string(), |e| format!("\"{e}\"")),
            end_json(&world, &end, sim.time() >= detail_from)
        )
        .unwrap();
        writeln!(ticks, "{line}").unwrap();
        if mode == Mode::Commit && prev_mode != Mode::Commit {
            if let (Some(law), Some(p)) = (g.law, sim.jsb.as_ref()) {
                takeovers += 1;
                writeln!(
                    settles,
                    "{{\"k\":{k},\"t\":{:.2},\"escape\":\"{}\",\"path\":{held_id},\"end\":{},\"cols\":[\"dt\",\"x\",\"y\",\"z\",\"v\",\"vz\",\"phi\",\"track\",\"vh\"],\"rows\":[{}]}}",
                    sim.time(),
                    ESCAPES[law.esc].name,
                    end_json(&world, &end, sim.time() >= detail_from),
                    settle(&world, p, law, settle_secs)
                )
                .unwrap();
            }
        }
        prev_mode = mode;
        if sim.crashed {
            break;
        }
    }
    for w in [&mut ticks, &mut paths, &mut settles, &mut fans] {
        w.flush().unwrap();
    }
    eprintln!(
        "{name}: {:.2} s, {} ticks with the gate flying, {takeovers} takeovers, min clearance {:.2} m{}; wrote {}",
        sim.time(),
        sim.commit_ticks,
        sim.min_true_clear,
        if sim.crashed { ", CRASHED" } else { "" },
        out.display()
    );
}
