//! Records the crashes of the hostile-pilot harness episodes (P1 filter on) as JSON for plotting.
//! `cargo run --release --no-default-features --features jsb --bin crashes -- OUT_DIR [episodes] [--pm]
//!   [--safety-filter exact|fitted|fitted25|exact-rollout|exact-rollout-lean] [--escapes 3|5|6] [--law cegis1|cegis2|lawfirst] [--budget FRAMES] [--time-cap MS] [--threads N] [--only EPISODE]
//!   [--check-threads N [--verify-seeds]] [--margin M [--check-every K]] [--swept] [--handback-extra M] [--scenario K [--pilot hostile|kamikaze|mixed]]`
//! (`--pm` flies the point-mass model instead of JSBSim.) `--scenario K` starts every episode at scenario K
//! (1-5) instead of a random start; with K = 5 (Tower gap) the scripted showcase pilot flies one more.
//! `--check-threads N` (N ≥ 1) has the gate check every escape to its full horizon on N threads
//! (`envfilter::CHECK_THREADS`; 0, the default, is the budgeted sequential check); `--verify-seeds` re-flies
//! every worker rollout on the calling thread and stops on any difference. `summary.csv`'s `digest` column
//! hashes each episode's states, modes and commands, so two runs can be compared tick for tick.
use cityflight::escape::*;
use cityflight::filter::*;
use cityflight::harness::par_map;
use cityflight::model::*;
use cityflight::pilot::*;
use cityflight::sim::*;
use cityflight::world::*;
use std::fmt::Write;

struct Rec {
    t: f64,
    s: State,
    alpha: f64,
    mode: u8,
    lam: f64,
    esc: i32,
    u: Cmd,
    up: Cmd,
    clear: f64,
}

fn mode_code(m: Mode) -> u8 {
    match m {
        Mode::Free => 0,
        Mode::Blend => 1,
        Mode::Commit => 2,
        _ => 3,
    }
}

/// Filter statistics of one episode.
#[derive(Default)]
struct Stats {
    first_accept: bool,
    ticks: u64,
    commit_ticks: u64,
    blind_ticks: u64,
    outcomes: [[u64; 4]; cityflight::envfilter::N_ESC],
    runs: u64,
    short_runs: u64,
    cpu_ms: Vec<f32>,
    wall_ms: Vec<f32>,
    frames: Vec<u32>,
    /// Smoothness: switches into or out of a commit, re-commits that reverse the turn direction, flight
    /// time (s), and per tick the total variation and largest single-frame change of the surfaces applied
    /// to JSBSim (elevator, aileron, throttle).
    switches: u64,
    reversals: u64,
    blend_ticks: u64,
    secs: f64,
    tv: Vec<[f32; 3]>,
    jump: Vec<[f32; 3]>,
    frames_all: Vec<u32>,
    cpu_workers_ms: Vec<f32>,
    /// `digest` of the episode's records.
    digest: u64,
    /// Lowest flown airframe clearance (m).
    min_clear: f64,
}

/// FNV-1a over every tick's state, mode and applied command: equal digests mean the same closed-loop run.
fn digest(recs: &[Rec]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    let mut eat = |x: u64| {
        for b in x.to_le_bytes() {
            h = (h ^ b as u64).wrapping_mul(0x100000001b3);
        }
    };
    for r in recs {
        r.s.iter().chain(r.u.iter()).for_each(|v| eat(v.to_bits()));
        eat(r.mode as u64);
    }
    h
}

#[derive(Clone, Copy, PartialEq)]
enum PilotKind {
    Hostile,
    Kamikaze,
    Showcase,
}

fn run(world: &World, e: u64, s0: State, pk: PilotKind, dur: f64) -> (bool, Vec<Rec>, Vec<(f64, Vec<[f32; 3]>)>, Stats) {
    let cfg = SimCfg { filter_on: true, filter: FilterCfg { phase: Phase::P1, robust: false }, mismatch: false, seed: e };
    let mut sim = Sim::new(world, s0, cfg);
    let mut fbw = Fbw::from_state(&s0);
    let mut hostile = Hostile::new(e);
    let mut kami = Kamikaze::new(e);
    let mut show = Showcase::new(street_x(GAP_STREET));
    let mut recs = Vec::new();
    let mut plans = Vec::new();
    let mut last_mode = Mode::Free;
    let (mut switches, mut tvs, mut jumps) = (0u64, Vec::new(), Vec::new());
    let mut tv0 = sim.jsb.as_ref().map(|p| p.tv).or(sim.lean.as_ref().map(|g| g.tv)).unwrap_or([0.0; 4]);
    for _ in 0..(dur / DT_F).round() as u64 {
        match pk {
            PilotKind::Kamikaze => kami.update(world, &sim.s, &mut fbw, DT_F),
            PilotKind::Hostile => hostile.update(&mut fbw, DT_F),
            PilotKind::Showcase => show.update(&sim.s, &mut fbw, DT_F),
        }
        let up = fbw.cmd(&sim.prm_ctrl, &sim.s);
        sim.tick(up);
        let metrics = match (sim.jsb.as_mut(), sim.lean.as_mut()) {
            (Some(p), _) => Some((&mut p.tv, &mut p.jump)),
            (None, Some(g)) => Some((&mut g.tv, &mut g.jump)),
            _ => None,
        };
        if let Some((tv, jump)) = metrics {
            let sel = |a: [f64; 4]| [a[0] as f32, a[1] as f32, a[3] as f32];
            let d = [tv[0] - tv0[0], tv[1] - tv0[1], tv[2] - tv0[2], tv[3] - tv0[3]];
            tvs.push(sel(d));
            jumps.push(sel(*jump));
            tv0 = *tv;
            *jump = [0.0; 4];
        }
        if (sim.fs.mode == Mode::Commit) != (last_mode == Mode::Commit) {
            switches += 1;
        }
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        let alpha = sim.jsb.as_ref().map(|p| p.obs.alpha).or(sim.lean.as_ref().map(|g| g.obs.alpha)).unwrap_or(f64::NAN);
        let esc = sim.fs.plan.map_or(-1, |p| p.esc as i32);
        recs.push(Rec {
            t: sim.time(),
            s: sim.s,
            alpha,
            mode: mode_code(sim.fs.mode),
            lam: sim.fs.lam,
            esc,
            u: sim.applied,
            up,
            clear: sim.true_clear,
        });
        if sim.fs.mode == Mode::Commit && last_mode != Mode::Commit && cityflight::envfilter::kind().is_some() {
            plans.push((sim.time(), sim.env_pred.iter().map(|q| [q[0] as f32, q[1] as f32, q[2] as f32]).collect()));
        } else if sim.fs.mode == Mode::Commit && last_mode != Mode::Commit {
            if let Some(pl) = sim.fs.plan {
                let pred = Pred { accept: false, ..sim.pred() };
                let mut p = Vec::new();
                let (hold, te) = pl.tail(sim.k);
                pred.rollout(&sim.s, hold, pl.esc, te, pl.psi0, f64::NEG_INFINITY, Some(&mut p));
                plans.push((sim.time(), p));
            }
        }
        last_mode = sim.fs.mode;
        if sim.crashed {
            break;
        }
    }
    let mut st = Stats { first_accept: sim.started_safe, ticks: sim.ticks, commit_ticks: sim.commit_ticks, ..Default::default() };
    (st.switches, st.secs, st.tv, st.jump) = (switches, sim.time(), tvs, jumps);
    st.min_clear = sim.min_true_clear;
    if let Some(g) = sim.lean.take() {
        st.first_accept = g.start_ok;
        st.wall_ms = g.wall_ms.clone();
    }
    if let Some(g) = sim.env_gate.take() {
        st.first_accept = g.first_accept.unwrap_or(false);
        (st.reversals, st.blend_ticks) = (g.reversals, g.blend_ticks);
        st.blind_ticks = g.blind_ticks;
        st.outcomes = g.outcomes;
        (st.runs, st.short_runs) = (g.runs, g.short_runs);
        (st.cpu_ms, st.wall_ms, st.frames) = (g.cpu_ms, g.wall_ms, g.frames);
        (st.frames_all, st.cpu_workers_ms) = (g.frames_all, g.cpu_workers_ms);
    }
    (sim.crashed, recs, plans, st)
}

fn pct(v: &mut [f32], q: f64) -> f32 {
    if v.is_empty() {
        return f32::NAN;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[((v.len() - 1) as f64 * q).round() as usize]
}

fn json(world: &World, name: &str, e: u64, kamikaze: bool, recs: &[Rec], plans: &[(f64, Vec<[f32; 3]>)]) -> String {
    let mut o = String::new();
    let last = recs.last().unwrap();
    let hit = if world.surface(last.s[X], last.s[Y]) > world.terrain(last.s[X], last.s[Y]) + 1.0 { "building" } else { "terrain" };
    write!(o, "{{\"name\":\"{name}\",\"episode\":{e},\"kamikaze\":{kamikaze},\"hit\":\"{hit}\",\"recs\":[").unwrap();
    for (i, r) in recs.iter().enumerate() {
        let s = &r.s;
        write!(
            o,
            "{}[{:.2},{:.2},{:.2},{:.2},{:.3},{:.4},{:.4},{:.4},{:.3},{:.4},{},{:.3},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.2}]",
            if i > 0 { "," } else { "" },
            r.t, s[X], s[Y], s[Z], s[V], s[GAM], s[PSI], s[PHI], s[N], r.alpha, r.mode, r.lam, r.esc, r.u[0], r.u[1], r.up[0], r.up[1], r.u[2], r.clear
        )
        .unwrap();
    }
    o += "],\"plans\":[";
    for (i, (t, p)) in plans.iter().enumerate() {
        write!(o, "{}{{\"t\":{t:.2},\"path\":[", if i > 0 { "," } else { "" }).unwrap();
        for (j, q) in p.iter().enumerate() {
            write!(o, "{}[{:.1},{:.1},{:.1}]", if j > 0 { "," } else { "" }, q[0], q[1], q[2]).unwrap();
        }
        o += "]}";
    }
    // Surface heights around the last 20 s of flight, 4 m grid.
    let tail: Vec<&Rec> = recs.iter().filter(|r| r.t >= last.t - 20.0).collect();
    let (mut x0, mut x1, mut y0, mut y1) = (f64::MAX, f64::MIN, f64::MAX, f64::MIN);
    for r in &tail {
        x0 = x0.min(r.s[X]);
        x1 = x1.max(r.s[X]);
        y0 = y0.min(r.s[Y]);
        y1 = y1.max(r.s[Y]);
    }
    for (_, p) in plans.iter().filter(|(t, _)| *t >= last.t - 20.0) {
        for q in p.iter().take(150) {
            x0 = x0.min(q[0] as f64);
            x1 = x1.max(q[0] as f64);
            y0 = y0.min(q[1] as f64);
            y1 = y1.max(q[1] as f64);
        }
    }
    let pad = 80.0;
    let side = (x1 - x0).max(y1 - y0) + 2.0 * pad;
    let (cx, cy) = (0.5 * (x0 + x1), 0.5 * (y0 + y1));
    let step = (side / 220.0).max(2.0);
    let n = (side / step) as usize;
    let (gx, gy) = (cx - 0.5 * side, cy - 0.5 * side);
    write!(o, "],\"grid\":{{\"x0\":{gx:.1},\"y0\":{gy:.1},\"step\":{step:.2},\"n\":{n},\"h\":[").unwrap();
    for j in 0..n {
        for i in 0..n {
            let h = world.surface(gx + i as f64 * step, gy + j as f64 * step);
            write!(o, "{}{:.1}", if i + j > 0 { "," } else { "" }, h).unwrap();
        }
    }
    o += "]}}";
    o
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out = args.first().cloned().unwrap_or("/tmp/crashes".into());
    let episodes: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200);
    let only: Option<u64> = args.iter().position(|a| a == "--only").and_then(|i| args.get(i + 1)?.parse().ok());
    let secs: f64 = args.iter().position(|a| a == "--secs").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(60.0);
    cityflight::jsb::parse_fuel_args(&args);
    if !args.iter().any(|a| a == "--pm") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(l) = args.iter().position(|a| a == "--law").and_then(|i| args.get(i + 1)) {
        cityflight::envfilter::LAW_SEL.store(cityflight::envfilter::parse_law(l), std::sync::atomic::Ordering::Relaxed);
    }
    cityflight::envfilter::check_flags(&args);
    if let Some(ms) = args.iter().position(|a| a == "--time-cap").and_then(|i| args.get(i + 1)?.parse().ok()) {
        cityflight::envfilter::TIME_CAP_MS.store(ms, std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(b) = args.iter().position(|a| a == "--budget").and_then(|i| args.get(i + 1)?.parse().ok()) {
        cityflight::envfilter::BUDGET.store(b, std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(n) = args.iter().position(|a| a == "--escapes").and_then(|i| args.get(i + 1)?.parse().ok()) {
        cityflight::envfilter::N_USED.store(n, std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(i) = args.iter().position(|a| a == "--safety-filter") {
        if args.get(i + 1).is_some_and(|s| s == "exact-rollout-lean") {
            assert!(cityflight::jsb::fuel_freeze_default(), "--fuel-drain does not combine with exact-rollout-lean (the Lean gate always rolls out with fuel freeze)");
            cityflight::leangate::LEAN_GATE.store(true, std::sync::atomic::Ordering::Relaxed);
        }
        let k = cityflight::envfilter::parse(args.get(i + 1).map_or("", |s| s.as_str()));
        cityflight::envfilter::ENV_FILTER.store(k, std::sync::atomic::Ordering::Relaxed);
        if matches!(cityflight::envfilter::kind(), Some(cityflight::envfilter::Kind::Fitted { .. })) {
            cityflight::envfilter::table();
        }
    }
    if let Some(n) = args.iter().position(|a| a == "--check-threads").and_then(|i| args.get(i + 1)?.parse().ok()) {
        cityflight::envfilter::CHECK_THREADS.store(n, std::sync::atomic::Ordering::Relaxed);
    }
    if args.iter().any(|a| a == "--verify-seeds") {
        cityflight::envfilter::VERIFY_SEEDS.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    std::fs::create_dir_all(&out).unwrap();
    let world = World::new(1337);
    let scen: Option<usize> = args.iter().position(|a| a == "--scenario").and_then(|i| args.get(i + 1)?.parse::<usize>().ok()).map(|k| k.clamp(1, SCENARIOS.len()) - 1);
    let pilot_arg = args.iter().position(|a| a == "--pilot").and_then(|i| args.get(i + 1)).map_or("mixed", |s| s.as_str());
    let mut jobs: Vec<(String, u64, State, PilotKind, f64)> = Vec::new();
    match scen {
        None => {
            for e in (0..episodes).filter(|e| only.map_or(true, |o| o == *e)) {
                let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xE915);
                let pk = if e % 4 == 3 { PilotKind::Kamikaze } else { PilotKind::Hostile };
                jobs.push((format!("ep{e:03}"), e, random_start(&world, &mut rng), pk, secs));
            }
            for id in 0..SCENARIOS.len() {
                jobs.push((format!("kamikaze-{}", SCENARIOS[id].replace(' ', "_")), 1000 + id as u64, scenario_start(&world, id), PilotKind::Kamikaze, secs));
            }
        }
        Some(id) => {
            let s0 = scenario_start(&world, id);
            for e in (0..episodes).filter(|e| only.map_or(true, |o| o == *e)) {
                let pk = match pilot_arg {
                    "hostile" => PilotKind::Hostile,
                    "kamikaze" => PilotKind::Kamikaze,
                    _ if e % 2 == 1 => PilotKind::Kamikaze,
                    _ => PilotKind::Hostile,
                };
                let tag = if pk == PilotKind::Kamikaze { "kamikaze" } else { "ep" };
                jobs.push((format!("{tag}-s{}-{e:03}", id + 1), 2000 + e, s0, pk, secs));
            }
            if id == 4 {
                jobs.push(("showcase".into(), 3000, s0, PilotKind::Showcase, secs));
            }
        }
    }
    let threads = args
        .iter()
        .position(|a| a == "--threads")
        .and_then(|i| args.get(i + 1)?.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
    let res = par_map(
        jobs,
        threads,
        |(name, e, s0, pk, dur)| {
            let (crashed, recs, plans, st) = run(&world, *e, *s0, *pk, *dur);
            if crashed {
                std::fs::write(format!("{out}/{name}.json"), json(&world, name, *e, *pk == PilotKind::Kamikaze, &recs, &plans)).unwrap();
            }
            let st = Stats { digest: digest(&recs), ..st };
            let off = recs.iter().any(|r| r.s[X].abs() > MAP_HALF || r.s[Y].abs() > MAP_HALF);
            (name.clone(), crashed, recs.last().map_or(0.0, |r| r.t), st, off)
        },
        |_, _| {},
    );
    let mut rows = String::from("name,crashed,t_end,first_accept,ticks,commit_ticks,blind_ticks,digest\n");
    for (name, crashed, t, st, _) in &res {
        if *crashed {
            println!("{name} crashed at t={t:.1} ({} start)", if st.first_accept { "verified" } else { "unverified" });
        }
        writeln!(rows, "{name},{crashed},{t:.2},{},{},{},{},{:016x}", st.first_accept, st.ticks, st.commit_ticks, st.blind_ticks, st.digest).unwrap();
    }
    std::fs::write(format!("{out}/summary.csv"), rows).unwrap();
    let count = |f: &dyn Fn(&(String, bool, f64, Stats, bool)) -> bool| res.iter().filter(|r| f(r)).count();
    if let Some(r) = res.iter().filter(|r| r.3.first_accept).min_by(|a, b| a.3.min_clear.total_cmp(&b.3.min_clear)) {
        println!("lowest flown clearance (verified starts): {:.2} m ({})", r.3.min_clear, r.0);
    }
    let off: Vec<&str> = res.iter().filter(|r| r.4).map(|r| r.0.as_str()).collect();
    println!("left the map: {} {:?}", off.len(), off);
    let (eps, kam) = (|r: &(String, bool, f64, Stats, bool)| r.0.starts_with("ep"), |r: &(String, bool, f64, Stats, bool)| r.0.starts_with("kamikaze"));
    println!(
        "episodes: {} crashes / {} ({} from verified starts / {}, {} from unverified / {})",
        count(&|r| eps(r) && r.1),
        count(&|r| eps(r)),
        count(&|r| eps(r) && r.1 && r.3.first_accept),
        count(&|r| eps(r) && r.3.first_accept),
        count(&|r| eps(r) && r.1 && !r.3.first_accept),
        count(&|r| eps(r) && !r.3.first_accept)
    );
    println!(
        "kamikaze: {} crashes / {} ({} from verified starts / {})",
        count(&|r| kam(r) && r.1),
        count(&|r| kam(r)),
        count(&|r| kam(r) && r.1 && r.3.first_accept),
        count(&|r| kam(r) && r.3.first_accept)
    );
    if let Some(r) = res.iter().find(|r| r.0 == "showcase") {
        println!("showcase: {} ({} start), {} of {} ticks committed", if r.1 { "CRASHED" } else { "no crash" }, if r.3.first_accept { "verified" } else { "unverified" }, r.3.commit_ticks, r.3.ticks);
    }
    let (ticks, commits, blind): (u64, u64, u64) = res.iter().fold((0, 0, 0), |a, r| (a.0 + r.3.ticks, a.1 + r.3.commit_ticks, a.2 + r.3.blind_ticks));
    println!("intervention: {:.2}% of {} ticks committed ({} committed with no witness)", 100.0 * commits as f64 / ticks.max(1) as f64, ticks, blind);
    let (runs, short): (u64, u64) = res.iter().fold((0, 0), |a, r| (a.0 + r.3.runs, a.1 + r.3.short_runs));
    println!("commit runs: {runs}, {short} released within {} ticks", cityflight::envfilter::SHORT_RUN);
    for esc in 0..cityflight::envfilter::n_esc() {
        let o: Vec<u64> = (0..4).map(|k| res.iter().map(|r| r.3.outcomes[esc][k]).sum()).collect();
        println!("rollouts {:8}: ok {} hit {} horizon {} budget {}", cityflight::envfilter::ESCAPES[esc].name, o[0], o[1], o[2], o[3]);
    }
    let (sw, rev, blend, secs) = res.iter().fold((0, 0, 0, 0.0), |a, r| (a.0 + r.3.switches, a.1 + r.3.reversals, a.2 + r.3.blend_ticks, a.3 + r.3.secs));
    println!(
        "smoothness: {:.1} commit switches/min, {rev} direction reversals on re-commit, {:.2}% of ticks blended",
        sw as f64 / (secs / 60.0).max(1e-9),
        100.0 * blend as f64 / ticks.max(1) as f64
    );
    for (k, name) in ["elevator", "aileron", "throttle"].iter().enumerate() {
        let mut tv: Vec<f32> = res.iter().flat_map(|r| r.3.tv.iter().map(move |v| v[k])).collect();
        let mut jp: Vec<f32> = res.iter().flat_map(|r| r.3.jump.iter().map(move |v| v[k])).collect();
        let mean = tv.iter().map(|&x| x as f64).sum::<f64>() / tv.len().max(1) as f64;
        println!(
            "surface {name:8}: per-tick variation mean {mean:.4} p95 {:.4} p99 {:.4} | frame jump p99 {:.4} max {:.4}",
            pct(&mut tv, 0.95),
            pct(&mut tv, 0.99),
            pct(&mut jp, 0.99),
            pct(&mut jp, 1.0)
        );
    }
    let mut cpu: Vec<f32> = res.iter().flat_map(|r| r.3.cpu_ms.iter().copied()).collect();
    let mut wall: Vec<f32> = res.iter().flat_map(|r| r.3.wall_ms.iter().copied()).collect();
    let mut fr: Vec<f32> = res.iter().flat_map(|r| r.3.frames.iter().map(|&f| f as f32)).collect();
    // All threads: the calling thread's CPU plus the pool workers'; all frames, including discarded rollouts.
    let mut cpu_all: Vec<f32> = res.iter().flat_map(|r| r.3.cpu_ms.iter().zip(&r.3.cpu_workers_ms).map(|(a, b)| a + b)).collect();
    let mut fr_all: Vec<f32> = res.iter().flat_map(|r| r.3.frames_all.iter().map(|&f| f as f32)).collect();
    if !cpu.is_empty() {
        let parallel = cityflight::envfilter::CHECK_THREADS.load(std::sync::atomic::Ordering::Relaxed) > 1;
        let mut rows: Vec<(&str, &mut Vec<f32>)> = vec![("thread CPU ms", &mut cpu), ("wall ms", &mut wall), ("JSBSim frames", &mut fr)];
        if parallel {
            rows.push(("CPU all thr. ms", &mut cpu_all));
            rows.push(("frames all", &mut fr_all));
        }
        for (label, v) in rows {
            let mean = v.iter().map(|&x| x as f64).sum::<f64>() / v.len() as f64;
            println!("check {label:14}: median {:.2}  mean {mean:.2}  p99 {:.2}  p99.9 {:.2}  max {:.2}", pct(v, 0.5), pct(v, 0.99), pct(v, 0.999), pct(v, 1.0));
        }
    }
}
