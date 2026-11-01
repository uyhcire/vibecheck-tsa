//! Headless acceptance harness: hostile-pilot episodes with the filter on and
//! off (same seeds), mismatch measurements, Phase 1 vs Phase 2, kamikaze
//! endurance per scenario, and a no-nuisance check.

use crate::filter::*;
use crate::model::*;
use crate::pilot::*;
use crate::sim::*;
use crate::world::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

#[derive(Clone, Copy, Debug)]
pub struct EpCfg {
    pub filter_on: bool,
    pub phase: Phase,
    pub robust: bool,
    pub mismatch: bool,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct EpResult {
    pub crashed: bool,
    pub crash_t: f64,
    pub min_clear: f64,
    pub ticks: u64,
    pub active: u64,
    pub commit: u64,
    pub inv_viol: u64,
    pub tail_fail: u64,
    pub ms_sum: f64,
    pub ms_max: f64,
    pub du_sum: f64,
    pub kamikaze: bool,
    pub started_safe: bool,
}

pub enum PilotSel {
    Hostile,
    Kamikaze,
}

pub fn run_episode(world: &World, cfg: EpCfg, seed: u64, start: Option<State>, pilot: PilotSel, dur: f64) -> EpResult {
    let mut rng = Rng::new(seed.wrapping_mul(7919) ^ 0xE915);
    let s0 = start.unwrap_or_else(|| random_start(world, &mut rng));
    let scfg = SimCfg {
        filter_on: cfg.filter_on,
        filter: FilterCfg { phase: cfg.phase, robust: cfg.robust },
        mismatch: cfg.mismatch,
        seed,
    };
    let mut sim = Sim::new(world, s0, scfg);
    let mut fbw = Fbw::from_state(&s0);
    let kamikaze = matches!(pilot, PilotSel::Kamikaze);
    let mut hostile = Hostile::new(seed);
    let mut kami = Kamikaze::new(seed);
    let n = (dur / DT_F).round() as u64;
    for _ in 0..n {
        if kamikaze {
            kami.update(world, &sim.s, &mut fbw, DT_F);
        } else {
            hostile.update(&mut fbw, DT_F);
        }
        let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
        sim.tick(u);
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        if sim.crashed {
            break;
        }
    }
    EpResult {
        crashed: sim.crashed,
        crash_t: sim.time(),
        min_clear: sim.min_true_clear,
        ticks: sim.ticks,
        active: sim.active_ticks,
        commit: sim.commit_ticks,
        inv_viol: sim.inv_viol,
        tail_fail: sim.tail_fail,
        ms_sum: sim.ms_sum,
        ms_max: sim.ms_max,
        du_sum: sim.du_sum,
        kamikaze,
        started_safe: sim.started_safe,
    }
}

/// Run `jobs` in parallel on `threads` threads; `progress` gets (done, total).
pub fn par_map<T: Send + Sync, R: Send>(jobs: Vec<T>, threads: usize, f: impl Fn(&T) -> R + Sync, progress: impl Fn(usize, usize) + Sync) -> Vec<R> {
    let n = jobs.len();
    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let out: Mutex<Vec<Option<R>>> = Mutex::new((0..n).map(|_| None).collect());
    std::thread::scope(|sc| {
        for _ in 0..threads.max(1) {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                if i >= n {
                    break;
                }
                let r = f(&jobs[i]);
                out.lock().unwrap()[i] = Some(r);
                let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                progress(d, n);
            });
        }
    });
    out.into_inner().unwrap().into_iter().map(|r| r.unwrap()).collect()
}

#[derive(Clone, Debug, Default)]
pub struct Summary {
    pub name: String,
    pub episodes: usize,
    pub crashes: usize,
    pub inv_viol_eps: usize,
    pub inv_viol_ticks: u64,
    pub tail_fail_ticks: u64,
    pub min_clear: f64,
    pub median_min_clear: f64,
    pub active_share: f64,
    pub commit_share: f64,
    pub ms_mean: f64,
    pub ms_max: f64,
    pub du_per_active_tick: f64,
    pub filter_on: bool,
}

pub fn summarize(name: &str, filter_on: bool, rs: &[EpResult]) -> Summary {
    let mut mins: Vec<f64> = rs.iter().map(|r| r.min_clear).collect();
    mins.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let ticks: u64 = rs.iter().map(|r| r.ticks).sum();
    let active: u64 = rs.iter().map(|r| r.active).sum();
    Summary {
        name: name.to_string(),
        episodes: rs.len(),
        crashes: rs.iter().filter(|r| r.crashed).count(),
        inv_viol_eps: rs.iter().filter(|r| r.inv_viol > 0).count(),
        inv_viol_ticks: rs.iter().map(|r| r.inv_viol).sum(),
        tail_fail_ticks: rs.iter().map(|r| r.tail_fail).sum(),
        min_clear: mins.first().copied().unwrap_or(0.0),
        median_min_clear: mins.get(mins.len() / 2).copied().unwrap_or(0.0),
        active_share: active as f64 / ticks.max(1) as f64,
        commit_share: rs.iter().map(|r| r.commit).sum::<u64>() as f64 / ticks.max(1) as f64,
        ms_mean: rs.iter().map(|r| r.ms_sum).sum::<f64>() / ticks.max(1) as f64,
        ms_max: rs.iter().map(|r| r.ms_max).fold(0.0, f64::max),
        du_per_active_tick: rs.iter().map(|r| r.du_sum).sum::<f64>() / active.max(1) as f64,
        filter_on,
    }
}

/// How much of street-level flight the filter can verify: random states on
/// street centrelines, 20-90 m above the ground, flying along the street.
#[derive(Clone, Copy, Debug, Default)]
pub struct Coverage {
    pub total: usize,
    pub safe: usize,
    pub below_roof: usize,
    pub below_roof_safe: usize,
}

fn below_roof(world: &World, x: f64, y: f64, z: f64) -> bool {
    let ground = world.terrain(x, y);
    let mut roof: f64 = 0.0;
    for a in -5..=5 {
        for b in -5..=5 {
            roof = roof.max(world.surface(x + a as f64 * 5.0, y + b as f64 * 5.0) - ground);
        }
    }
    z - ground < roof
}

/// `heading_err_deg`: the aircraft points this far off the street axis
/// (random sign), as a keyboard pilot always does a little.
pub fn street_coverage(world: &World, n: usize, threads: usize, heading_err_deg: f64) -> Coverage {
    use crate::escape::{Pred, ESC_ORDER};
    let rs = par_map(
        (0..n as u64).collect(),
        threads,
        |&i| {
            let mut rng = Rng::new(i ^ 0x57EE7);
            loop {
                let k = 1 + (rng.f() * 19.0) as usize;
                let along = rng.range(-1100.0, 1100.0);
                let lat = street_x(k) + rng.range(-2.0, 2.0);
                let dir = if rng.chance(0.5) { 1.0 } else { -1.0 };
                let herr = heading_err_deg.to_radians() * if rng.chance(0.5) { 1.0 } else { -1.0 };
                let (x, y, psi0) = if rng.chance(0.5) {
                    (lat, along, if dir > 0.0 { std::f64::consts::FRAC_PI_2 } else { -std::f64::consts::FRAC_PI_2 })
                } else {
                    (along, lat, if dir > 0.0 { 0.0 } else { std::f64::consts::PI })
                };
                let psi = psi0 + herr;
                let ground = world.terrain(x, y);
                let agl = rng.range(20.0, 90.0);
                let s = trimmed(x, y, ground + agl, rng.range(40.0, 50.0), 0.0, psi, 0.64);
                if world.true_clearance([x, y, s[2]]) <= 0.0 {
                    continue;
                }
                let below = below_roof(world, x, y, s[2]);
                let pred = Pred { world, prm: Params::nominal(), wind: [0.0; 3], robust: false, swept: true, accept: true };
                let h = pred.best(&s, None, &ESC_ORDER, 0.0).0;
                return (h >= 0.0, below);
            }
        },
        |_, _| {},
    );
    let mut c = Coverage { total: rs.len(), ..Default::default() };
    for (safe, below) in rs {
        c.safe += safe as usize;
        c.below_roof += below as usize;
        c.below_roof_safe += (safe && below) as usize;
    }
    c
}

/// A street-following autopilot tries to hold 40 m above the ground on the
/// centreline of six streets for 30 s each. Returns (share of time below
/// rooftop height, mean intervention, crashes).
pub fn street_pilot(world: &World, filter_on: bool, phase: Phase) -> (f64, f64, usize) {
    use std::f64::consts::PI;
    let streets: [(usize, bool, f64); 6] = [(4, true, 1.0), (7, true, 1.0), (13, false, -1.0), (16, false, 1.0), (8, false, 1.0), (12, true, -1.0)];
    let (mut below, mut total, mut lam, mut crashes) = (0usize, 0usize, 0.0, 0usize);
    for &(k, ns, dir) in &streets {
        let lat = street_x(k);
        let start = -1100.0 * dir;
        let psi = if ns { if dir > 0.0 { PI / 2.0 } else { -PI / 2.0 } } else if dir > 0.0 { 0.0 } else { PI };
        let (x, y) = if ns { (lat, start) } else { (start, lat) };
        let s0 = trimmed(x, y, world.terrain(x, y) + 40.0, 45.0, 0.0, psi, 0.6);
        let cfg = SimCfg { filter_on, filter: FilterCfg { phase, robust: false }, mismatch: false, seed: k as u64 };
        let mut sim = Sim::new(world, s0, cfg);
        let mut fbw = Fbw::from_state(&s0);
        for _ in 0..(30.0 / DT_F) as usize {
            let st = sim.s;
            let off = if ns { st[X] - lat } else { st[Y] - lat };
            let lat_err = if ns { -off * dir } else { off * dir };
            let herr = (psi - st[PSI] + PI).rem_euclid(2.0 * PI) - PI + (-0.02 * lat_err).clamp(-0.3, 0.3);
            fbw.phi_ref = (1.5 * herr).clamp(-0.5, 0.5);
            let agl = st[Z] - world.terrain(st[X], st[Y]);
            fbw.g_ref = (0.02 * (40.0 - agl)).clamp(-0.2, 0.2);
            fbw.thr = 0.65;
            let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
            sim.tick(u);
            total += 1;
            lam += if sim.fs.mode == crate::filter::Mode::Commit { 1.0 } else { sim.fs.lam };
            if below_roof(world, sim.s[X], sim.s[Y], sim.s[Z]) {
                below += 1;
            }
            if sim.crashed {
                crashes += 1;
                break;
            }
        }
    }
    (below as f64 / total.max(1) as f64, lam / total.max(1) as f64, crashes)
}

pub struct Report {
    pub coverage: Coverage,
    pub coverage_4deg: Coverage,
    pub street: Vec<(String, (f64, f64, usize))>,
    pub rows: Vec<Summary>,
    pub kamikaze: Vec<(String, EpResult)>,
    pub nuisance_blend_ticks: u64,
    pub nuisance_ticks: u64,
    pub checks: Vec<(String, bool, String)>,
}

pub struct HarnessOpts {
    pub episodes: usize,
    pub threads: usize,
    pub kamikaze_secs: f64,
    pub extended: bool,
}

/// Straight, level flights well above everything nearby.
pub fn nuisance_starts(world: &World) -> Vec<State> {
    let mut v = Vec::new();
    for (k, (x, y, psi)) in [(-1100.0, -600.0, 0.0), (-1100.0, 500.0, 0.0), (-600.0, -1100.0, 1.5708), (500.0, -1100.0, 1.5708)]
        .iter()
        .enumerate()
    {
        let mut top: f64 = 0.0;
        for i in 0..60 {
            let d = i as f64 * 40.0;
            for o in [-200.0, 0.0, 200.0] {
                let px = x + d * f64::cos(*psi) - o * f64::sin(*psi);
                let py = y + d * f64::sin(*psi) + o * f64::cos(*psi);
                top = top.max(world.surface(px, py));
            }
        }
        let alt = if k % 2 == 0 { 180.0 } else { 250.0 };
        let thr = 0.64;
        v.push(trimmed(*x, *y, top + alt, 50.0, 0.0, *psi, thr));
    }
    v
}

pub fn run_harness(world: &World, o: &HarnessOpts, progress: &(dyn Fn(&str, usize, usize) + Sync)) -> Report {
    let p1 = EpCfg { filter_on: true, phase: Phase::P1, robust: false, mismatch: false };
    let mut configs: Vec<(&str, EpCfg)> = vec![
        ("P1 filter ON", p1),
        ("filter OFF", EpCfg { filter_on: false, ..p1 }),
        ("P1 ON + mismatch", EpCfg { mismatch: true, ..p1 }),
        ("OFF + mismatch", EpCfg { filter_on: false, mismatch: true, ..p1 }),
    ];
    if o.extended {
        configs.push(("P2 closed-form ON", EpCfg { phase: Phase::P2, ..p1 }));
        configs.push(("Permissive ON", EpCfg { phase: Phase::Permissive, ..p1 }));
        configs.push(("P1+P3 robust + mismatch", EpCfg { robust: true, mismatch: true, ..p1 }));
        configs.push(("P2+P3 robust + mismatch", EpCfg { phase: Phase::P2, robust: true, mismatch: true, ..p1 }));
    }
    // Same random starts for every configuration.
    let starts: Vec<State> = par_map(
        (0..o.episodes as u64).collect(),
        o.threads,
        |&e| {
            let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xE915);
            random_start(world, &mut rng)
        },
        |d, n| progress("starts", d, n),
    );
    let mut rows = Vec::new();
    for (name, cfg) in &configs {
        let jobs: Vec<(u64, State)> = starts.iter().enumerate().map(|(e, s)| (e as u64, *s)).collect();
        let rs = par_map(
            jobs,
            o.threads,
            |(e, s)| {
                let pilot = if e % 4 == 3 { PilotSel::Kamikaze } else { PilotSel::Hostile };
                run_episode(world, *cfg, *e, Some(*s), pilot, 60.0)
            },
            |d, n| progress(name, d, n),
        );
        rows.push(summarize(name, cfg.filter_on, &rs));
    }
    // Kamikaze endurance per scenario.
    let kjobs: Vec<usize> = (0..4).collect();
    let kres = par_map(
        kjobs,
        o.threads,
        |&id| run_episode(world, p1, 1000 + id as u64, Some(scenario_start(world, id)), PilotSel::Kamikaze, o.kamikaze_secs),
        |d, n| progress("kamikaze", d, n),
    );
    let kamikaze: Vec<(String, EpResult)> = kres.into_iter().enumerate().map(|(i, r)| (SCENARIOS[i].to_string(), r)).collect();
    // No nuisance.
    let mut nb = 0;
    let mut nt = 0;
    for s0 in nuisance_starts(world) {
        let mut sim = Sim::new(world, s0, SimCfg::default());
        let fbw = Fbw::from_state(&s0);
        for _ in 0..(40.0 / DT_F) as usize {
            let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
            sim.tick(u);
            nt += 1;
            if sim.fs.mode != crate::filter::Mode::Free {
                nb += 1;
            }
        }
    }
    let r_on = &rows[0];
    let r_off = &rows[1];
    let mut checks = vec![
        (
            "Filter on, no mismatch: zero crashes and zero invariant violations".to_string(),
            r_on.crashes == 0 && r_on.inv_viol_eps == 0,
            format!("{} crashes, {} episodes with violations / {}", r_on.crashes, r_on.inv_viol_eps, r_on.episodes),
        ),
        (
            "Filter off: most hostile episodes crash".to_string(),
            r_off.crashes * 2 > r_off.episodes,
            format!("{} / {} crashed", r_off.crashes, r_off.episodes),
        ),
        (
            format!("Kamikaze with filter on survives {:.0} s in every scenario", o.kamikaze_secs),
            kamikaze.iter().all(|(_, r)| !r.crashed),
            kamikaze
                .iter()
                .map(|(n, r)| format!("{}: {} (min {:.1} m)", n, if r.crashed { "CRASH" } else { "ok" }, r.min_clear))
                .collect::<Vec<_>>()
                .join(", "),
        ),
        (
            "No nuisance: straight flight well above obstacles shows zero blending".to_string(),
            nb == 0,
            format!("{} / {} ticks blended", nb, nt),
        ),
        (
            "Phase 1 filter averages under 3 ms per tick".to_string(),
            r_on.ms_mean < 3.0,
            format!("{:.3} ms mean, {:.2} ms max", r_on.ms_mean, r_on.ms_max),
        ),
    ];
    checks.push((
        "Mismatch results reported alongside the main results".to_string(),
        rows.len() >= 4,
        format!("P1 + mismatch: {} / {} crashed", rows[2].crashes, rows[2].episodes),
    ));
    let coverage = street_coverage(world, 2000, o.threads, 0.0);
    let coverage_4deg = street_coverage(world, 2000, o.threads, 4.0);
    let modes = [("filter OFF", false, Phase::P1), ("P1", true, Phase::P1), ("P2", true, Phase::P2), ("Permissive", true, Phase::Permissive)];
    let street = par_map(
        modes.to_vec(),
        o.threads,
        |&(n, on, ph)| (n.to_string(), street_pilot(world, on, ph)),
        |d, n| progress("street pilot", d, n),
    );
    Report { coverage, coverage_4deg, street, rows, kamikaze, nuisance_blend_ticks: nb, nuisance_ticks: nt, checks }
}

pub fn format_coverage(c: &Coverage, label: &str) -> String {
    format!(
        "Street coverage{label}: {:.1}% of {} street states have a verified escape; {:.1}% of the {} below rooftop height\n",
        100.0 * c.safe as f64 / c.total.max(1) as f64,
        c.total,
        100.0 * c.below_roof_safe as f64 / c.below_roof.max(1) as f64,
        c.below_roof
    )
}

pub fn format_report(r: &Report) -> String {
    let mut s = String::new();
    s += &format!(
        "{:<26} {:>5} {:>8} {:>9} {:>10} {:>10} {:>8} {:>8} {:>9} {:>8} {:>8}\n",
        "config", "eps", "crashes", "inv.viol", "min clr m", "med clr m", "active", "commit", "ms/tick", "ms max", "|du|/tk"
    );
    for row in &r.rows {
        if row.filter_on {
            s += &format!(
                "{:<26} {:>5} {:>8} {:>9} {:>10.1} {:>10.1} {:>7.1}% {:>7.1}% {:>9.3} {:>8.2} {:>8.4}\n",
                row.name,
                row.episodes,
                row.crashes,
                row.inv_viol_eps,
                row.min_clear,
                row.median_min_clear,
                100.0 * row.active_share,
                100.0 * row.commit_share,
                row.ms_mean,
                row.ms_max,
                row.du_per_active_tick
            );
        } else {
            s += &format!(
                "{:<26} {:>5} {:>8} {:>9} {:>10.1} {:>10.1} {:>8} {:>8} {:>9} {:>8} {:>8}\n",
                row.name, row.episodes, row.crashes, "-", row.min_clear, row.median_min_clear, "-", "-", "-", "-", "-"
            );
        }
    }
    s += "\n";
    s += &format_coverage(&r.coverage, "");
    s += &format_coverage(&r.coverage_4deg, " (4 deg heading error)");
    s += "Street autopilot (holds 40 m on 6 streets, 30 s each): time below rooftops\n";
    for (n, (b, l, c)) in &r.street {
        s += &format!("  {:<11} {:>5.1}%   mean intervention {:.2}   crashes {}\n", n, 100.0 * b, l, c);
    }
    s += "\nKamikaze endurance (filter on):\n";
    for (n, k) in &r.kamikaze {
        s += &format!(
            "  {:<14} {:>6.0} s  {}  min clearance {:.1} m, active {:.1}%\n",
            n,
            k.crash_t,
            if k.crashed { "CRASHED" } else { "survived" },
            k.min_clear,
            100.0 * k.active as f64 / k.ticks.max(1) as f64
        );
    }
    s += "\nAcceptance:\n";
    for (name, ok, detail) in &r.checks {
        s += &format!("  [{}] {}  ({})\n", if *ok { "x" } else { " " }, name, detail);
    }
    s
}
