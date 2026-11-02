//! End-test falsifier: verified escapes from `hunt forever`'s perturbed starts, flown on past their verdict.
use cityflight::envfilter::{law_params, rollout, Law, LawP, ESCAPES, STREET};
use cityflight::harness::par_map;
use cityflight::jsb::{JsbPlant, DT_JSB};
use cityflight::model::*;
use cityflight::sim::random_start;
use cityflight::world::{Rng, World, R_BODY};

fn rand_seg(rng: &mut Rng) -> (f64, [f64; 4]) {
    let side = if rng.chance(0.5) { -1.0 } else { 1.0 };
    let d = rng.range(0.1, 3.0);
    let u = match (rng.f() * 6.0) as u32 {
        0 => [rng.range(-1.0, -0.4), side * rng.range(0.6, 1.0), 0.0, rng.range(0.0, 1.0)],
        1 => [rng.range(0.3, 1.0), side * rng.range(0.0, 0.6), 0.0, rng.range(0.0, 1.0)],
        2 => [rng.range(-0.3, 0.3), side * 1.0, side * rng.range(-1.0, 1.0), rng.range(0.0, 1.0)],
        3 => [rng.range(-1.0, 1.0), rng.range(-1.0, 1.0), rng.range(-1.0, 1.0), if rng.chance(0.5) { 0.0 } else { 1.0 }],
        4 => [rng.range(-0.1, 0.15), rng.range(-0.1, 0.1), 0.0, rng.range(0.3, 1.0)],
        _ => [rng.range(-1.0, -0.6), 0.0, side * rng.range(0.5, 1.0), 0.0],
    };
    (d, u)
}

fn perturbed(world: &World, i: u64, seed: u64) -> JsbPlant {
    let mut rng = Rng::new(seed.wrapping_mul(1_000_003) ^ i);
    let s0 = random_start(world, &mut Rng::new((i + seed * 100_000).wrapping_mul(7919) ^ 0xE915));
    let mut p = JsbPlant::new(&s0);
    let (d, u) = rand_seg(&mut rng);
    for _ in 0..((d * 0.5).min(1.5) / DT_JSB) as usize {
        p.frame_raw(u[0], u[1], u[2], u[3]);
    }
    p
}

struct After {
    min: f64,
    t_min: f64,
    end: &'static str,
    z_min: f64,
    side: (f64, f64),
}

fn continue_escape(world: &World, p: &JsbPlant, esc: usize, t_ok: f64, secs: f64, every: Option<usize>, stop_above: bool) -> After {
    let mut q = p.fork();
    let mut law = Law::new(esc);
    let mut a = After { min: f64::INFINITY, t_min: 0.0, end: "timeout", z_min: f64::INFINITY, side: (0.0, 0.0) };
    for k in 1..=(secs / DT_JSB) as usize {
        law.step(world, &mut q);
        let s = q.state();
        let t = k as f64 * DT_JSB;
        if (t - t_ok).abs() < 0.5 * DT_JSB {
            a.side.0 = law.side;
        }
        if every.is_some_and(|e| k % e == 0) {
            let o = &q.obs;
            println!(
                "t {:6.1} x {:8.1} y {:8.1} z {:7.1} v {:5.1} vz {:5.2} trk {:7.2} phi {:6.2} alpha {:5.3} elev {:6.3} ia {:6.3} clr {:8.1}",
                t, s[X], s[Y], s[Z], o.vt, -o.vned[2], o.vned[1].atan2(o.vned[0]).to_degrees(), o.phi.to_degrees(), o.alpha, q.surf[0], law.ia,
                world.airframe_clearance(&s, 200.0)
            );
        }
        if stop_above && s[Z] - R_BODY - 8.0 > world.raw_top {
            a.end = "above-top";
            break;
        }
        if t > t_ok {
            a.z_min = a.z_min.min(s[Z]);
            let c = world.airframe_clearance(&s, 200.0);
            if c < a.min {
                (a.min, a.t_min) = (c, t);
            }
        }
    }
    a.side.1 = law.side;
    a
}

/// Mean airspeed, climb rate and alpha over the last 20 s of `secs` of law `law` from a level start at `v0`, `z0`.
fn settle(law: Law, v0: f64, z0: f64, secs: f64) -> (f64, f64, f64) {
    settle_from(law, &trimmed(0.0, 0.0, z0, v0, 0.0, 0.0, 1.0), secs)
}

fn settle_from(mut law: Law, s0: &State, secs: f64) -> (f64, f64, f64) {
    let mut q = JsbPlant::new(s0);
    let n = (secs / DT_JSB) as usize;
    let n0 = n - (20.0 / DT_JSB) as usize;
    let mut acc = [0.0; 3];
    for k in 1..=n {
        law.frame(&mut q);
        if k > n0 {
            acc[0] += q.obs.vt;
            acc[1] -= q.obs.vned[2];
            acc[2] += q.obs.alpha;
        }
    }
    let m = (n - n0) as f64;
    (acc[0] / m, acc[1] / m, acc[2] / m)
}

fn trim_cmd(args: &[String]) {
    let z0: f64 = arg(args, "--alt").unwrap_or(200.0);
    println!("Full-throttle power curve at {z0} m: a stiff speed hold (no alpha cap) at bank 0 / 0.52 / 0.7 rad");
    for v in (26..=50).step_by(2) {
        let mut line = format!("v_ref {v:2}:");
        for (esc, bank) in [(0usize, 0.0), (1, 0.52), (3, 0.7)] {
            let mut p = LawP { v_eas_t: [0.0; 4], h_level: f64::INFINITY, ..law_params() };
            p.v_ref = [v as f64; 6];
            (p.kv, p.gc_lo, p.gc_hi, p.amax) = (0.3, -0.4, 0.4, 0.4);
            let (vt, vz, a) = settle(Law::with_turn(esc, p, if bank == 0.0 { 0.0 } else { -1.0 }, bank), v as f64, z0, 90.0);
            line += &format!("  [{vt:5.2} m/s vz {vz:6.2} a {a:.3}]");
        }
        println!("{line}");
    }
    let old = LawP { v_eas_t: [0.0; 4], h_level: f64::INFINITY, ..law_params() };
    for (name, p) in [("gate law", old), ("terminal law", law_params())] {
        println!("{name}: settled (last 20 of 120 s) from 72 starts at {z0} m per turn escape; post-stall = alpha > 0.2");
        for esc in 1..5 {
            let mut res = Vec::new();
            for v0 in [24.0, 28.0, 32.0, 36.0, 42.0, 55.0] {
                for gam in [-0.3, 0.0, 0.35] {
                    for phi in [-0.9, 0.0, 0.5, 1.1] {
                        let mut s0 = trimmed(0.0, 0.0, z0, v0, gam, 0.0, 1.0);
                        s0[PHI] = phi;
                        res.push(settle_from(Law::with(esc, p), &s0, 120.0));
                    }
                }
            }
            let (st, ok): (Vec<_>, Vec<_>) = res.iter().partition(|r| r.2 > 0.2);
            let rng = |v: &Vec<&(f64, f64, f64)>, k: usize| v.iter().fold((f64::INFINITY, f64::NEG_INFINITY), |a, r| { let x = [r.0, r.1, r.2][k]; (a.0.min(x), a.1.max(x)) });
            println!(
                "  {:8}: {:2} post-stall (v {:?} vz {:?}), {:2} normal (v {:?} vz {:?} alpha {:?})",
                ESCAPES[esc].name, st.len(), rng(&st, 0), rng(&st, 1), ok.len(), rng(&ok, 0), rng(&ok, 1), rng(&ok, 2)
            );
        }
    }
    // Recovery from the post-stall branch itself: the gate law from a post-stall-prone start, then each law.
    let world = World::new(1337);
    println!("From post-stall states (gate law flown until alpha > 0.26 with ia at its clamp), 120 s more of each law:");
    for i in 0..400u64 {
        let p0 = perturbed(&world, i, 1);
        for esc in 1..5 {
            let mut q = p0.fork();
            let mut law = Law::with(esc, old);
            let mut stalled = false;
            for _ in 0..(40.0 / DT_JSB) as usize {
                law.frame(&mut q);
                if law.turning() && q.obs.alpha > 0.26 && law.ia <= -0.399 && law.t > 12.0 {
                    stalled = true;
                    break;
                }
            }
            if !stalled || q.state()[Z] < 300.0 {
                continue;
            }
            let mut line = format!("  random {i:3} {:8} at v {:5.2} alpha {:.3} z {:6.1}:", ESCAPES[esc].name, q.obs.vt, q.obs.alpha, q.state()[Z]);
            for (name, p) in [("gate", old), ("terminal", law_params())] {
                let (mut r, mut l) = (q.fork(), Law { p, ..law });
                let (mut acc, mut nacc) = ([0.0; 3], 0.0);
                for k in 0..(120.0 / DT_JSB) as usize {
                    l.frame(&mut r);
                    if k as f64 * DT_JSB > 100.0 {
                        (acc[0], acc[1], acc[2], nacc) = (acc[0] + r.obs.vt, acc[1] - r.obs.vned[2], acc[2] + r.obs.alpha, nacc + 1.0);
                    }
                }
                line += &format!("  {name} v {:5.2} vz {:5.2} alpha {:.3}", acc[0] / nacc, acc[1] / nacc, acc[2] / nacc);
            }
            println!("{line}");
        }
    }
    println!("The escapes' own laws, settled after 150 s, from level starts at {z0} m:");
    for v0 in [25.0, 30.0, 35.0, 40.0, 50.0, 60.0] {
        let mut line = format!("start {v0:2}:");
        for esc in 0..5 {
            let (vt, vz, a) = settle(Law::new(esc), v0, z0, 150.0);
            line += &format!("  {}[{vt:5.2} vz {vz:5.2} a {a:.3}]", ESCAPES[esc].name);
        }
        println!("{line}");
    }
}

/// Level-off ending: random starts above `Z_LEVEL`, every verified escape flown on; the lowest point after the verdict.
fn high(world: &World, n: u64, secs: f64, threads: usize) {
    let res = par_map(
        (0..n).collect(),
        threads,
        |&i| {
            let mut r = Rng::new(i ^ 0x41617);
            let s0: State = [r.range(-2500.0, 2500.0), r.range(-2500.0, 2500.0), r.range(960.0, 2500.0), r.range(25.0, 90.0), r.range(-0.6, 0.5), r.range(-3.1, 3.1), r.range(-1.3, 1.3), 0.0, 1.0, r.range(0.0, 1.0)];
            let p = JsbPlant::new(&s0);
            (0..ESCAPES.len())
                .filter_map(|esc| {
                    let ro = rollout(world, &p, esc, usize::MAX);
                    ro.ok().then(|| (i, esc, ro.t, continue_escape(world, &p, esc, ro.t, secs, None, false)))
                })
                .collect::<Vec<_>>()
        },
        |_, _| {},
    );
    let all: Vec<_> = res.into_iter().flatten().collect();
    let worst = all.iter().min_by(|a, b| a.3.min.total_cmp(&b.3.min));
    let low = all.iter().map(|a| a.3.z_min).fold(f64::INFINITY, f64::min);
    println!("{} verified escapes from {n} starts above 960 m; lowest altitude after a verdict {low:.1} m (map top {:.1} m)", all.len(), world.raw_top);
    if let Some(w) = worst {
        println!("lowest clearance after a verdict: {:.2} m (random {}, {}, verdict {:.1} s, at {:.1} s)", w.3.min, w.0, ESCAPES[w.1].name, w.2, w.3.t_min);
    }
}

/// Rollout outcomes per escape from the perturbed starts, failures by the end test's last reason.
fn why(world: &World, n: u64, seed: u64, threads: usize) {
    let res = par_map(
        (0..n).collect(),
        threads,
        |&i| {
            let p = perturbed(world, i, seed);
            (0..ESCAPES.len())
                .map(|esc| {
                    let r = rollout(world, &p, esc, usize::MAX);
                    let w = format!("{:?}", r.why);
                    (esc, format!("{:?} {}", r.outcome, w.split(|c| c == ' ' || c == '{').next().unwrap_or("")))
                })
                .collect::<Vec<_>>()
        },
        |_, _| {},
    );
    let mut tally = std::collections::BTreeMap::new();
    for (esc, k) in res.into_iter().flatten() {
        *tally.entry((ESCAPES[esc].name, k)).or_insert(0) += 1;
    }
    for ((e, k), c) in tally {
        println!("{e:8} {k:30} {c}");
    }
}

fn arg<T: std::str::FromStr>(args: &[String], name: &str) -> Option<T> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)?.parse().ok())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let secs: f64 = arg(&args, "--secs").unwrap_or(200.0);
    let world = World::new(1337);
    if args.first().map(|s| s.as_str()) == Some("high") {
        return high(&world, arg(&args, "--n").unwrap_or(200), secs, arg(&args, "--threads").unwrap_or(3));
    }
    if args.first().map(|s| s.as_str()) == Some("trim") {
        return trim_cmd(&args);
    }
    if args.first().map(|s| s.as_str()) == Some("scen") {
        let p = JsbPlant::new(&cityflight::sim::scenario_start(&world, args[1].parse().unwrap()));
        for esc in 0..ESCAPES.len() {
            let r = rollout(&world, &p, esc, usize::MAX);
            let e = r.end;
            println!("{:8} {:?} at {:5.2} s ({:?}), min clearance {:.2} m, end v {:.1} z {:.1} at ({:.0}, {:.0})", ESCAPES[esc].name, r.outcome, r.t, r.why, r.min_clear, e[V], e[Z], e[X], e[Y]);
        }
        if let Some(esc) = args.get(2).and_then(|s| s.parse::<usize>().ok()) {
            continue_escape(&world, &p, esc, 0.0, arg(&args, "--secs").unwrap_or(20.0), Some(64), true);
        }
        return;
    }
    if args.first().map(|s| s.as_str()) == Some("why") {
        return why(&world, arg(&args, "--n").unwrap_or(150), arg(&args, "--seed").unwrap_or(1), arg(&args, "--threads").unwrap_or(3));
    }
    if args.first().map(|s| s.as_str()) == Some("trace") {
        let (i, seed, esc): (u64, u64, usize) = (args[1].parse().unwrap(), args[2].parse().unwrap(), args[3].parse().unwrap());
        let p = perturbed(&world, i, seed);
        let r = rollout(&world, &p, esc, usize::MAX);
        println!("random {i} seed {seed} {}: {:?} at t {:.2} s ({:?}), min clearance {:.2} m", ESCAPES[esc].name, r.outcome, r.t, r.why, r.min_clear);
        let a = continue_escape(&world, &p, esc, if r.ok() { r.t } else { 0.0 }, secs, Some(128), true);
        println!("after the verdict: min {:.2} m at t {:.1} s, end {}", a.min, a.t_min, a.end);
        return;
    }
    let n: u64 = args.first().and_then(|s| s.parse().ok()).unwrap_or(150);
    let seed: u64 = arg(&args, "--seed").unwrap_or(1);
    let threads: usize = arg(&args, "--threads").unwrap_or(3);
    let res = par_map(
        (0..n).collect(),
        threads,
        |&i| {
            let p = perturbed(&world, i, seed);
            (0..ESCAPES.len())
                .filter_map(|esc| {
                    let r = rollout(&world, &p, esc, usize::MAX);
                    r.ok().then(|| (i, esc, r.t, continue_escape(&world, &p, esc, r.t, secs, None, true)))
                })
                .collect::<Vec<_>>()
        },
        |_, _| {},
    );
    let all: Vec<_> = res.into_iter().flatten().collect();
    let mut per = [[0usize; 3]; 6];
    for (_, esc, _, a) in &all {
        per[*esc][0] += 1;
        per[*esc][1] += (a.min <= 0.0) as usize;
        per[*esc][2] += (a.end == "timeout") as usize;
    }
    println!("seed {seed}: {} verified escapes from {n} perturbed starts, {secs} s continuations", all.len());
    for (esc, p) in per.iter().enumerate() {
        println!("  {:8}: {:4} verified, {:3} contacts after the verdict, {:3} still below the top at the end", ESCAPES[esc].name, p[0], p[1], p[2]);
    }
    let switched = all.iter().filter(|(_, e, _, a)| *e == STREET && a.side.0 != a.side.1).count();
    println!("  street escapes whose end-set kind changed after the verdict: {switched}");
    let mut worst: Vec<_> = all.iter().collect();
    worst.sort_by(|a, b| a.3.min.total_cmp(&b.3.min));
    for (i, esc, t, a) in worst.iter().take(8) {
        println!("  random {i} seed {seed} {:8} verdict {:5.1} s: min after {:7.2} m at {:6.1} s, end {}", ESCAPES[*esc].name, t, a.min, a.t_min, a.end);
    }
    for (i, esc, t, a) in all.iter().filter(|a| a.3.end == "timeout").take(8) {
        println!("  still below the top: random {i} seed {seed} {:8} verdict {:5.1} s, min after {:7.2} m", ESCAPES[*esc].name, t, a.min);
    }
    let bad = per.iter().map(|p| p[1]).sum::<usize>();
    println!("contacts after a verified end: {bad}");
}
