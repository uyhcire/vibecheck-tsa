//! Escape-law lab on the JSBSim plant: frame cost, control signs, climb performance, escape traces.
//! `cargo run --release --no-default-features --features jsb --bin esclab -- [speed|signs|cover N|sweep N|scen N|ep N|trace [START] [-v]] [--law cegis1|cegis2|lawfirst]`
use cityflight::envfilter::*;
use cityflight::jsb::*;
use cityflight::model::*;
use std::f64::consts::{FRAC_PI_2, PI};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let what = args.first().map_or("trace", |s| s.as_str());
    if let Some(l) = args.iter().position(|a| a == "--law").and_then(|i| args.get(i + 1)) {
        LAW_SEL.store(parse_law(l), std::sync::atomic::Ordering::Relaxed);
    }
    match what {
        "speed" => {
            let p = JsbPlant::new(&trimmed(0.0, 0.0, 300.0, 45.0, 0.0, 0.0, 0.7));
            let mut q = p.fork();
            let t = Instant::now();
            let n = 128 * 200;
            for _ in 0..n {
                q.frame_raw(-0.05, 0.0, 0.0, 0.7);
            }
            println!("{:.2} us/frame wall", t.elapsed().as_secs_f64() * 1e6 / n as f64);
            let c0 = cityflight::envfilter::thread_cpu();
            for _ in 0..n {
                q.frame_raw(-0.05, 0.0, 0.0, 0.7);
            }
            println!("{:.2} us/frame thread-cpu", (cityflight::envfilter::thread_cpu() - c0) * 1e6 / n as f64);
            let t = Instant::now();
            for _ in 0..1000 {
                let _ = p.fork();
            }
            println!("{:.2} us/fork", t.elapsed().as_secs_f64() * 1e3);
            // Checked frames: every escape from the Tower gap start and a tower-run start, thread CPU.
            let world = cityflight::world::World::new(1337);
            for id in [4, 0] {
                let p = JsbPlant::new(&cityflight::sim::scenario_start(&world, id));
                let (mut fr, c0) = (0usize, cityflight::envfilter::thread_cpu());
                for _ in 0..20 {
                    for esc in 0..N_ESC {
                        fr += rollout(&world, &p, esc, usize::MAX).frames;
                    }
                }
                println!("scenario {}: {:.2} us/checked frame thread-cpu over {fr} frames", id + 1, (cityflight::envfilter::thread_cpu() - c0) * 1e6 / fr as f64);
                for esc in 0..N_ESC {
                    let (mut fr, c0) = (0usize, cityflight::envfilter::thread_cpu());
                    for _ in 0..20 {
                        fr += rollout(&world, &p, esc, usize::MAX).frames;
                    }
                    println!("  {:8}: {:.2} us/checked frame over {fr}", ESCAPES[esc].name, (cityflight::envfilter::thread_cpu() - c0) * 1e6 / fr.max(1) as f64);
                }
            }
        }
        "signs" => {
            for (name, e, a, r) in [("rud+", 0.0, 0.0, 0.3), ("ail+", 0.0, 0.3, 0.0), ("elev+", 0.1, 0.0, 0.0)] {
                let mut p = JsbPlant::new(&trimmed(0.0, 0.0, 300.0, 45.0, 0.0, 0.0, 0.7));
                let e0 = p.surf[0];
                for k in 0..128 {
                    p.frame_raw(e0 + e, a, r, 0.7);
                    if k % 32 == 31 {
                        let o = p.obs;
                        println!("{name} t={:.2} beta={:.3} p={:.3} q={:.3} r={:.3} phi={:.3} theta={:.3} psi={:.3}", (k + 1) as f64 / 128.0, o.beta, o.pqr[0], o.pqr[1], o.pqr[2], o.phi, o.theta, o.psi);
                    }
                }
            }
        }
        "cover" => {
            let world = cityflight::world::World::new(1337);
            let n: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(400);
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(4);
            cover(&world, n, threads, law_params(), &format!("{:?}", law_params().kind));
        }
        "sweep" => {
            let world = cityflight::world::World::new(1337);
            let n: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(400);
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(4);
            let base = law_params();
            cover(&world, n, threads, base, "base");
            cover(&world, n, threads, LawP { keep_bank: true, ..base }, "keep_bank");
            cover(&world, n, threads, LawP { t_pull_min: [1.5, 1.5, 1.5, 0.0, 0.0, 1.5], ..base }, "40deg immediate");
            cover(&world, n, threads, LawP { keep_bank: true, t_pull_min: [1.5, 1.5, 1.5, 0.0, 0.0, 1.5], ..base }, "both");
        }
        "gaps" => {
            let world = cityflight::world::World::new(1337);
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(6);
            gaps(&world, threads);
        }
        "at" => {
            // esclab at X Y AGL PSI_DEG [V]: every escape from a level state there.
            let world = cityflight::world::World::new(1337);
            let f = |i: usize, d: f64| args.get(i).and_then(|s| s.parse::<f64>().ok()).unwrap_or(d);
            let (x, y) = (f(1, 0.0), f(2, 0.0));
            let s0 = trimmed(x, y, world.terrain(x, y) + f(3, 60.0), f(5, 45.0), 0.0, f(4, 90.0).to_radians(), 0.7);
            let p = JsbPlant::new(&s0);
            for esc in 0..N_ESC {
                let r = rollout(&world, &p, esc, usize::MAX);
                let last = r.path.last().unwrap();
                let tl = r.tail.last().copied().unwrap_or(*last);
                println!("{:8}: {:?} at t={:.1} min clear {:.1} end {:.0} {:.0} {:.0} surface {:.0} tail end {:.0} {:.0} {:.0} ({} tail pts)", ESCAPES[esc].name, r.outcome, r.t, r.min_clear, last[0], last[1], last[2], world.surface(last[0], last[1]), tl[0], tl[1], tl[2], r.tail.len());
            }
        }
        "approach" => {
            // esclab approach X0 Y0 PSI_DEG LEN: street escape along a line, per street v_ref.
            let world = cityflight::world::World::new(1337);
            let f = |i: usize, d: f64| args.get(i).and_then(|s| s.parse::<f64>().ok()).unwrap_or(d);
            let (x0, y0, psi, len) = (f(1, 0.0), f(2, 0.0), f(3, -90.0).to_radians(), f(4, 600.0));
            let base = law_params();
            for vr in [base.v_ref[STREET]] {
                let mut lp = base;
                lp.v_ref[STREET] = vr;
                let rows: Vec<String> = cityflight::harness::par_map(
                    (0..=(len / 30.0) as usize).collect(),
                    6,
                    |&i| {
                        let d = i as f64 * 30.0;
                        let (x, y) = (x0 + d * psi.cos(), y0 + d * psi.sin());
                        let mut o = format!("v_ref {vr} d={d:4.0} ({x:5.0},{y:5.0})");
                        for agl in [50.0, 70.0, 90.0] {
                            let p = JsbPlant::new(&trimmed(x, y, world.terrain(x, y) + agl, 45.0, 0.0, psi, 0.7));
                            let r = rollout_law(&world, &p, Law::with(STREET, lp), usize::MAX, None);
                            o += &format!("  {agl:2.0}: {:7} {:4.1}s", format!("{:?}", r.outcome), r.t);
                        }
                        o
                    },
                    |_, _| {},
                );
                for r in rows {
                    println!("{r}");
                }
            }
        }
        "showcase" => {
            // The scripted Tower gap flight under the gate filter, every 0.25 s.
            use cityflight::pilot::{Fbw, Showcase};
            use cityflight::sim::*;
            ENV_FILTER.store(parse("gate"), std::sync::atomic::Ordering::Relaxed);
            JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
            let world = cityflight::world::World::new(1337);
            let s0 = scenario_start(&world, 4);
            let mut sim = Sim::new(&world, s0, SimCfg::default());
            let mut fbw = Fbw::from_state(&sim.s);
            let mut show = Showcase::new(cityflight::world::street_x(GAP_STREET));
            for k in 0..(30.0 / DT_F) as usize {
                show.update(&sim.s, &mut fbw, DT_F);
                let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
                sim.tick(u);
                fbw.resync(&sim.s, sim.fs.lam, DT_F);
                let g = sim.env_gate.as_ref().unwrap();
                if k % 12 == 0 || sim.crashed {
                    let s = sim.s;
                    let e = g.law.map(|l| l.esc).or(g.witness).map_or("-", |i| ESCAPES[i].name);
                    println!("t={:5.2} x={:6.1} y={:6.1} z={:5.1} agl={:5.1} psi={:6.1} phi={:6.1} phase={} {:?} esc {e} side {:?} clear {:.1}", sim.time(), s[X], s[Y], s[Z], s[Z] - world.terrain(s[X], s[Y]), s[PSI].to_degrees(), s[PHI].to_degrees(), show.phase(), sim.fs.mode, g.law.map(|l| l.side), sim.true_clear);
                }
                if sim.crashed {
                    break;
                }
            }
        }
        "streettrace" => {
            // esclab streettrace X Y AGL PSI_DEG: the street escape's flight, every 0.5 s.
            let world = cityflight::world::World::new(1337);
            let f = |i: usize, d: f64| args.get(i).and_then(|s| s.parse::<f64>().ok()).unwrap_or(d);
            let (x, y) = (f(1, 0.0), f(2, 0.0));
            let p = JsbPlant::new(&trimmed(x, y, world.terrain(x, y) + f(3, 60.0), 45.0, 0.0, f(4, 90.0).to_radians(), 0.7));
            let mut q = p.fork();
            let mut law = Law::new(STREET);
            for k in 1..=(16.0 / DT_JSB) as usize {
                law.step(&world, &mut q);
                if law.side != 0.0 && k % 16 == 0 && args.iter().any(|a| a == "-v") {
                    let o = q.obs;
                    println!("    t={:5.2} phi={:6.1} p={:6.3} r={:6.3} beta={:6.3} ail={:6.3} rud={:6.3} iphi={:6.3} ib={:6.3}", k as f64 * DT_JSB, o.phi.to_degrees(), o.pqr[0], o.pqr[2], o.beta, q.surf[1], q.surf[2], law.iphi, law.ib);
                }
                if k % 64 == 0 {
                    let s = q.state();
                    println!("t={:5.1} ({:6.0},{:6.0},{:5.0}) surf {:4.0} V={:4.1} psi={:6.1} phi={:6.1} side {} clear {:.1}", k as f64 * DT_JSB, s[X], s[Y], s[Z], world.surface(s[X], s[Y]), s[V], s[PSI].to_degrees(), s[PHI].to_degrees(), law.side, world.airframe_clearance(&s, 50.0));
                }
            }
        }
        "scen" | "ep" => {
            use cityflight::world::World;
            let world = World::new(1337);
            let id: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2);
            let s0 = if what == "ep" {
                // The crash recorder's episode starts.
                let mut rng = cityflight::world::Rng::new((id as u64).wrapping_mul(7919) ^ 0xE915);
                cityflight::sim::random_start(&world, &mut rng)
            } else {
                cityflight::sim::scenario_start(&world, id)
            };
            let p = JsbPlant::new(&s0);
            println!("start {:?} top {:.0}", p.state(), top(&world));
            for esc in 0..N_ESC {
                let r = rollout(&world, &p, esc, usize::MAX);
                let last = r.path.last().unwrap();
                println!("{:8}: {:?} at t={:.1} min clear {:.1} end {:.0} {:.0} {:.0} surface {:.0}", ESCAPES[esc].name, r.outcome, r.t, r.min_clear, last[0], last[1], last[2], world.surface(last[0], last[1]));
            }
        }
        _ => {
            let verbose = args.iter().any(|a| a == "-v");
            let only: Option<&str> = args.get(1).map(|s| s.as_str()).filter(|s| !s.starts_with('-'));
            for (name, s0) in starts() {
                if only.map_or(false, |o| o != name) {
                    continue;
                }
                for esc in 0..N_ESC {
                    trace(name, &s0, esc, verbose);
                }
            }
        }
    }
}

/// Verified fraction of random states near obstacles (not filtered for safety), per escape and in total.
fn cover(world: &cityflight::world::World, n: u64, threads: usize, lp: LawP, label: &str) {
    use cityflight::world::Rng;
    let res = cityflight::harness::par_map(
        (0..n).collect(),
        threads,
        |&e| {
            let mut rng = Rng::new(e.wrapping_mul(104729) ^ 0xC0FE);
            let s = loop {
                let (x, y) = if rng.chance(0.65) { (rng.range(-1250.0, 1250.0), rng.range(-1250.0, 1250.0)) } else { (rng.range(-2300.0, 2300.0), rng.range(-2300.0, 2300.0)) };
                let z = world.surface(x, y).max(world.terrain(x, y)) + rng.range(12f64.ln(), 120f64.ln()).exp();
                let (v, gam, phi) = (rng.range(28.0, 65.0), rng.range(-35.0, 5.0).to_radians(), rng.range(-60.0, 60.0).to_radians());
                if world.true_clearance([x, y, z]) >= 8.0 {
                    break [x, y, z, v, gam, rng.range(0.0, 6.283), phi, 0.0, gam.cos() / phi.cos(), rng.range(0.2, 1.0)];
                }
            };
            let p = JsbPlant::new(&s);
            let rs: Vec<Roll> = (0..N_ESC).map(|k| rollout_law(world, &p, Law::with(k, lp), usize::MAX, None)).collect();
            let latest = rs.iter().filter(|r| r.outcome == Outcome::Hit).map(|r| r.t).fold(0.0, f64::max);
            let other = rs.iter().any(|r| matches!(r.outcome, Outcome::Horizon | Outcome::Budget));
            (rs.iter().map(|r| r.ok()).collect::<Vec<bool>>(), latest, other)
        },
        |_, _| {},
    );
    let unv: Vec<&(Vec<bool>, f64, bool)> = res.iter().filter(|r| !r.0.iter().any(|&b| b)).collect();
    let hist: Vec<usize> = [2.0, 4.0, 6.0, 9.0, 99.0].iter().scan(0.0, |lo, &hi| { let c = unv.iter().filter(|r| !r.2 && r.1 >= *lo && r.1 < hi).count(); *lo = hi; Some(c) }).collect();
    println!("  unverified {}: all hit, latest hit <2 s {}, 2-4 s {}, 4-6 s {}, 6-9 s {}, >9 s {}; some escape reached no terminal set {}", unv.len(), hist[0], hist[1], hist[2], hist[3], hist[4], unv.iter().filter(|r| r.2).count());
    let res: Vec<Vec<bool>> = res.into_iter().map(|r| r.0).collect();
    let any3 = res.iter().filter(|o| o[..3].iter().any(|&b| b)).count();
    let any5 = res.iter().filter(|o| o.iter().any(|&b| b)).count();
    let per: Vec<usize> = (0..N_ESC).map(|k| res.iter().filter(|o| o[k]).count()).collect();
    println!("{label:32}: verified {any5}/{n} (5 escapes), {any3}/{n} (3); per escape {per:?} sum {}", per.iter().sum::<usize>());
}

/// Start states (point-mass convention: bank positive left wing down) at 600 m, clear of everything.
fn starts() -> Vec<(&'static str, State)> {
    let st = |v: f64, gam: f64, phi: f64, thr: f64| -> State { [0.0, 0.0, 600.0, v, gam, 0.3, phi, 0.0, gam.cos() / phi.cos(), thr] };
    vec![
        ("slow", st(27.0, 0.0, 0.0, 0.2)),
        ("cruise", st(45.0, 0.0, 0.0, 0.6)),
        ("fast", st(60.0, -0.1, 0.0, 1.0)),
        ("steep", st(50.0, -0.55, 0.0, 0.3)),
        ("steep-fast", st(62.0, -0.8, 0.3, 0.0)),
        ("nose-high", st(36.0, 0.4, 0.0, 0.8)),
        ("nose-high-slow", st(29.0, 0.3, -0.3, 0.3)),
        ("banked-l", st(45.0, -0.1, 1.0, 0.6)),
        ("banked-r", st(40.0, -0.2, -1.1, 0.4)),
        ("slow-banked", st(31.0, -0.05, 0.6, 0.3)),
    ]
}

fn trace(name: &str, s0: &State, esc: usize, verbose: bool) {
    static WORLD: std::sync::OnceLock<cityflight::world::World> = std::sync::OnceLock::new();
    let world = WORLD.get_or_init(|| cityflight::world::World::new(1337));
    let p = JsbPlant::new(s0);
    let mut q = p.fork();
    let mut law = Law::new(esc);
    let n = (40.0 / DT_JSB) as usize;
    let (mut zmin, mut amax, mut nmax, mut vmin) = (f64::MAX, 0f64, 0f64, f64::MAX);
    let mut psi_prev = q.state()[PSI];
    let mut psi_unw = psi_prev;
    let mut hist: Vec<(f64, f64, f64, f64)> = Vec::new();
    for k in 1..=n {
        law.step(world, &mut q);
        let s = q.state();
        let o = q.obs;
        psi_unw += (s[PSI] - psi_prev + std::f64::consts::PI).rem_euclid(2.0 * std::f64::consts::PI) - std::f64::consts::PI;
        psi_prev = s[PSI];
        zmin = zmin.min(s[Z]);
        amax = amax.max(o.alpha);
        nmax = nmax.max(o.nz);
        vmin = vmin.min(o.vt);
        if k % 16 == 0 {
            hist.push((k as f64 * DT_JSB, s[Z], psi_unw, (o.vned[0].powi(2) + o.vned[1].powi(2)).sqrt()));
        }
        if verbose && k % 128 == 0 {
            println!(
                "   t={:4.1} V={:5.1} vz={:6.2} gam={:6.3} a={:6.3} th={:6.3} phi={:6.3} beta={:6.3} nz={:5.2} q={:6.3} r={:6.3} el={:6.3} ail={:6.3} rud={:6.3} ia={:6.3} ib={:6.3} turn={}",
                k as f64 * DT_JSB, o.vt, -o.vned[2], s[GAM], o.alpha, o.theta, o.phi, o.beta, o.nz, o.pqr[1], o.pqr[2], q.surf[0], q.surf[1], q.surf[2], law.ia, law.ib, law.turning()
            );
        }
    }
    // Settled climb and turn radius over the last 10 s.
    let m = hist.len();
    let (a, b) = (hist[m - 81], hist[m - 1]);
    let vz = (b.1 - a.1) / (b.0 - a.0);
    let om = (b.2 - a.2) / (b.0 - a.0);
    let r = if om.abs() > 1e-3 { b.3 / om.abs() } else { f64::INFINITY };
    let o = q.obs;
    println!(
        "{name:15} {:8}: settled vz={vz:5.2} m/s R={r:7.0} m  V={:5.1} phi={:6.3} beta={:6.3} | dz_min={:6.1} a_max={amax:.3} n_max={nmax:.2} V_min={vmin:.1}",
        ESCAPES[esc].name, o.vt, o.phi, o.beta, zmin - s0[Z]
    );
}

/// Street gaps flanked by tall buildings on both sides: which escapes verify from the street centreline
/// mid-gap, at several heights below the lower roof, flying either way along the street.
fn gaps(world: &cityflight::world::World, threads: usize) {
    use cityflight::world::{street_x, CITY_HALF};
    let mut cands = Vec::new();
    for ns in [true, false] {
        for k in 1..20usize {
            let hw = world.street_w[k] / 2.0;
            for j in 0..20usize {
                let (a0, a1) = (street_x(j) + world.street_w[j] / 2.0, street_x(j + 1) - world.street_w[j + 1] / 2.0);
                let c = street_x(k);
                // Tallest roof on each side within 35 m of the street edge, along this block.
                let mut side = [0f64; 2];
                for b in &world.boxes {
                    let (u0, u1, v0, v1) = if ns { (b.y0, b.y1, b.x0, b.x1) } else { (b.x0, b.x1, b.y0, b.y1) };
                    if u1 < a0 || u0 > a1 {
                        continue;
                    }
                    if v1 <= c - hw + 0.1 && v1 > c - hw - 35.0 {
                        side[0] = side[0].max(b.z1);
                    }
                    if v0 >= c + hw - 0.1 && v0 < c + hw + 35.0 {
                        side[1] = side[1].max(b.z1);
                    }
                }
                let lo = side[0].min(side[1]);
                if lo > 110.0 {
                    cands.push((ns, k, j, 0.5 * (a0 + a1), side));
                }
            }
        }
    }
    let _ = CITY_HALF;
    println!("{} candidate gaps", cands.len());
    let res = cityflight::harness::par_map(
        cands,
        threads,
        |&(ns, k, j, u, side)| {
            let mut out = String::new();
            let lo = side[0].min(side[1]);
            for dirn in [1.0f64, -1.0] {
                for agl in [40.0, 60.0, 80.0, 100.0] {
                    let (x, y) = if ns { (street_x(k), u) } else { (u, street_x(k)) };
                    let z = world.terrain(x, y) + agl;
                    if z > lo - 10.0 {
                        continue;
                    }
                    let psi = if ns { if dirn > 0.0 { FRAC_PI_2 } else { -FRAC_PI_2 } } else if dirn > 0.0 { 0.0 } else { PI };
                    let p = JsbPlant::new(&trimmed(x, y, z, 45.0, 0.0, psi, 0.7));
                    let ok: Vec<&str> = (0..N_ESC).filter(|&e| rollout(world, &p, e, usize::MAX).ok()).map(|e| ESCAPES[e].name).collect();
                    out += &format!("{} k={k:2} j={j:2} {:+} agl {agl:3.0} roofs {:3.0}/{:3.0} at ({x:6.0},{y:6.0}) ok {:?}\n", if ns { "NS" } else { "EW" }, dirn, side[0], side[1], ok);
                }
            }
            out
        },
        |_, _| {},
    );
    for r in res {
        print!("{r}");
    }
}
