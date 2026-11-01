//! Tower gap entry: verdicts along the gap street's approach (`docs/gap-entry`).
//! `cargo run --release --no-default-features --features jsb --bin gapentry -- survey`
use cityflight::envfilter::*;
use cityflight::jsb::*;
use cityflight::model::*;
use cityflight::regimes::*;
use cityflight::world::*;
use std::f64::consts::FRAC_PI_2;

/// The scenario's height, speed and heading on the gap street's centreline at `y`.
fn start(w: &World, y: f64) -> State {
    let x = -120.0;
    trimmed(x, y, w.terrain(x, y) + 88.0, 45.0, 0.0, FRAC_PI_2, 0.7)
}

/// Highest roof above the street level within 40 m beyond each kerb at `y` (west, east).
fn walls(w: &World, y: f64) -> (f64, f64) {
    let side = |x0: f64, x1: f64| {
        let mut m = 0f64;
        let mut x = x0;
        while x <= x1 {
            m = m.max(w.surface(x, y) - w.terrain(x, y));
            x += 1.25;
        }
        m
    };
    (side(-174.0, -134.5), side(-105.5, -66.0))
}

/// Exact flight of the street escape from `s`, airframe clearance checked at every frame, until the airframe is
/// 10 m above the highest point anywhere (`top`) and climbing.
struct Witness {
    ok: bool,
    min_clear: f64,
    t_min: f64,
    t_roll: f64,
    roll_at: [f64; 3],
    side: f64,
    t_end: f64,
    z_end: f64,
}

fn witness(w: &World, s: &State, max_secs: f64) -> Witness {
    let mut q = JsbPlant::new(s);
    let mut law = Law::new(STREET);
    let top = cityflight::envfilter::top(w);
    let mut r = Witness { ok: false, min_clear: f64::INFINITY, t_min: 0.0, t_roll: f64::NAN, roll_at: [0.0; 3], side: 0.0, t_end: 0.0, z_end: s[Z] };
    for k in 0..=(max_secs / DT_JSB) as usize {
        if k > 0 {
            law.step(w, &mut q);
        }
        let st = q.state();
        let c = w.airframe_clearance(&st, 50.0);
        if c < r.min_clear {
            r.min_clear = c;
            r.t_min = k as f64 * DT_JSB;
        }
        if law.side != 0.0 && r.t_roll.is_nan() {
            r.t_roll = k as f64 * DT_JSB;
            r.roll_at = [st[X], st[Y], st[Z]];
            r.side = law.side;
        }
        r.t_end = k as f64 * DT_JSB;
        r.z_end = st[Z];
        if c <= 0.0 {
            return r;
        }
        if st[Z] - 10.0 > top && q.obs.vned[2] <= 0.0 {
            r.ok = true;
            return r;
        }
    }
    r
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let what = args.first().map_or("survey", |s| s.as_str());
    let world = World::new(1337);
    JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    ENV_FILTER.store(parse("exact-rollout"), std::sync::atomic::Ordering::Relaxed);
    if let Some(n) = args.iter().position(|a| a == "--check-threads").and_then(|i| args.get(i + 1)?.parse().ok()) {
        CHECK_THREADS.store(n, std::sync::atomic::Ordering::Relaxed);
    }
    let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(3);
    match what {
        "survey" => {
            let (y0, y1, dy) = (-1100.0, 100.0, 20.0);
            let ys: Vec<f64> = (0..=((y1 - y0) / dy) as usize).map(|k| y0 + k as f64 * dy).collect();
            let rows = cityflight::harness::par_map(ys, threads, |&y| {
                let s = start(&world, y);
                let g = gate_verdict(&world, &s);
                let c = contact_verdict(&world, &s);
                let long = rollout_cfg(&world, &JsbPlant::new(&s), Law::new(STREET), usize::MAX, None, &RollCfg { horizon: 90.0, ..CONTACT });
                let (ww, we) = walls(&world, y);
                let per: Vec<String> = g.per_esc.iter().map(|e| format!("{}@{:.1}", e.cause.short(), e.t)).collect();
                format!("y {y:7.1} walls {ww:4.0}/{we:4.0} gate {} contact {} street90 {}@{:.1}s min {:.1} | {}", g.ok as u8, c.ok as u8, long.ok() as u8, long.t, long.min_clear, per.join(" "))
            }, |_, _| {});
            for r in rows {
                println!("{r}");
            }
        }
        "verdict" => {
            // The verdict map: every 5 m along the approach.
            let top = cityflight::envfilter::top(&world);
            println!("top of the map (terrain and roofs) {top:.1} m");
            let (y0, y1, dy) = (-1100.0, 100.0, 5.0);
            let ys: Vec<f64> = (0..=((y1 - y0) / dy) as usize).map(|k| y0 + k as f64 * dy).collect();
            let hz = |cfg: &RollCfg, s: &State| rollout_cfg(&world, &JsbPlant::new(s), Law::new(STREET), usize::MAX, None, cfg);
            let rows = cityflight::harness::par_map(ys, threads, |&y| {
                let s = start(&world, y);
                let g = gate_verdict(&world, &s);
                let gesc = g.per_esc.iter().position(|e| e.outcome == Outcome::Ok);
                let gate_cfg = RollCfg::filter();
                let g24 = verdict_cfg(&world, &JsbPlant::new(&s), &RollCfg { street_horizon: 24.0, ..gate_cfg });
                let c = contact_verdict(&world, &s);
                let need_c = hz(&RollCfg { street_horizon: 90.0, ..CONTACT }, &s);
                let need_g = hz(&RollCfg { street_horizon: 90.0, ..gate_cfg }, &s);
                let wt = witness(&world, &s, 900.0);
                let ob = outer_bound(&world, &s);
                format!("{y:7.1} | gate {} {} | gate24 {} | lib-contact {} | street needs {:.1}s contact, {:.1}s at 4 m | witness {} min {:.2} m at {:.1}s roll-in {:.1}s top at {:.0}s z {:.0} | unsafe {}",
                    g.ok as u8, gesc.map_or("-", |e| ESCAPES[e].name), g24.ok as u8, c.ok as u8,
                    if need_c.ok() { need_c.t } else { f64::NAN }, if need_g.ok() { need_g.t } else { f64::NAN },
                    if wt.ok { "SAFE" } else { "fail" }, wt.min_clear, wt.t_min, wt.t_roll, wt.t_end, wt.z_end, ob.map_or("-".into(), |b| format!("{}@{:.2}", b.test, b.t)))
            }, |_, _| {});
            for r in rows {
                println!("{r}");
            }
        }
        "demo" => {
            // gapentry demo Y0 SECS: the sticks-released flight from the centreline at Y0, gate default and with
            // a 24 s street horizon, plus filter off.
            let y0: f64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(-700.0);
            let secs: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40.0);
            let s0 = start(&world, y0);
            println!("--start {}", start_arg(&s0));
            for (name, sh, b, on) in [("gate", HORIZON, BUDGET_FRAMES, true), ("gate --street-horizon 24", 24.0, 4400, true), ("off", HORIZON, BUDGET_FRAMES, false)] {
                set_street_horizon(sh);
                BUDGET.store(b, std::sync::atomic::Ordering::Relaxed);
                let r = demo_run(&world, &s0, on, secs);
                println!("{name}: crashed {} min clear {:.2} at {:.1}s, first takeover {:?}, release {:?}, takeovers {}, committed ticks {} of {}, first accept {}", r.crashed, r.min_clear, r.t_min, r.first_commit, r.release, r.commit_runs, r.commit_ticks, r.ticks, r.first_accept);
            }
            set_street_horizon(HORIZON);
        }
        "trace" => {
            // gapentry trace Y0 SECS HORIZON BUDGET: each takeover of the sticks-released flight, and why.
            use cityflight::filter::Mode;
            use cityflight::pilot::Fbw;
            use cityflight::sim::{Sim, SimCfg};
            let f = |i: usize, d: f64| args.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            let (y0, secs, sh, budget) = (f(1, -700.0), f(2, 40.0), f(3, 24.0), f(4, BUDGET_FRAMES as f64));
            set_street_horizon(sh);
            BUDGET.store(budget as usize, std::sync::atomic::Ordering::Relaxed);
            let s0 = start(&world, y0);
            let mut sim = Sim::new(&world, s0, SimCfg::default());
            let mut fbw = Fbw::from_state(&sim.s);
            let mut was = Mode::Free;
            let mut fr: Vec<u32> = Vec::new();
            for _ in 0..(secs / cityflight::model::DT_F).round() as usize {
                fbw.sticks(0.0, 0.0, cityflight::model::DT_F);
                let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
                let pre = sim.jsb.as_ref().unwrap().fork();
                sim.tick(u);
                fbw.resync(&sim.s, sim.fs.lam, cityflight::model::DT_F);
                if sim.fs.mode == Mode::Commit && was != Mode::Commit {
                    let st = pre.state();
                    let v = verdict_cfg(&world, &pre, &RollCfg::filter());
                    let per: Vec<String> = v.per_esc.iter().map(|e| format!("{}@{:.1}", e.cause.short(), e.t)).collect();
                    println!("t {:5.2} x {:7.2} y {:7.1} z {:6.1} hdg {:6.2} bank {:5.2} | from pre-tick state: ok {} | {}", sim.time(), st[X], st[Y], st[Z], st[PSI].to_degrees(), st[PHI].to_degrees(), v.ok as u8, per.join(" "));
                }
                was = sim.fs.mode;
                if sim.crashed {
                    println!("crashed at {:.2}", sim.time());
                    break;
                }
            }
            if let Some(g) = sim.env_gate.as_ref() {
                fr.extend(g.frames.iter());
                fr.sort();
                println!("ticks {} committed {} frames/tick median {} p99 {} max {}", sim.ticks, sim.commit_ticks, fr[fr.len() / 2], fr[fr.len() * 99 / 100], fr[fr.len() - 1]);
            }
        }
        "witness" => {
            // gapentry witness Y: the proven-safe program from the centreline state at Y, flown exactly.
            let y: f64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(-480.0);
            let s = start(&world, y);
            let wt = witness(&world, &s, 900.0);
            println!("start --start {}", start_arg(&s));
            println!("program: the gate's street escape (Law::new(STREET)), full throttle, from the first frame");
            println!("verdict {}: min airframe clearance {:.2} m at t = {:.2} s; rolls into a {} 40° climbing helix at t = {:.2} s at ({:.0}, {:.0}, {:.0}); 10 m above the map's top ({:.1} m) and climbing at t = {:.1} s",
                if wt.ok { "SAFE" } else { "FAIL" }, wt.min_clear, wt.t_min, if wt.side < 0.0 { "left" } else { "right" }, wt.t_roll, wt.roll_at[0], wt.roll_at[1], wt.roll_at[2], cityflight::envfilter::top(&world), wt.t_end);
        }
        "grid" => {
            // Acceptance around the slice: offsets from the centreline, heights and headings, y from -700 to -60.
            let mut jobs = Vec::new();
            for k in 0..=32 {
                for dx in [-6.0, -3.0, 0.0, 3.0, 6.0] {
                    for agl in [70.0, 88.0, 105.0] {
                        for dh in [-3.0, 0.0, 3.0] {
                            jobs.push((-700.0 + 20.0 * k as f64, dx, agl, dh));
                        }
                    }
                }
            }
            let rows = cityflight::harness::par_map(jobs, threads, |&(y, dx, agl, dh): &(f64, f64, f64, f64)| {
                let x = -120.0 + dx;
                let s = trimmed(x, y, world.terrain(x, y) + agl, 45.0, 0.0, FRAC_PI_2 + f64::to_radians(dh), 0.7);
                let g = gate_verdict(&world, &s).ok;
                let g24 = verdict_cfg(&world, &JsbPlant::new(&s), &RollCfg { street_horizon: 24.0, ..RollCfg::filter() }).ok;
                (y, dx, agl, dh, g, g24)
            }, |_, _| {});
            type R = (f64, f64, f64, f64, bool, bool);
            for agl in [70.0, 88.0, 105.0] {
                let n = |f: &dyn Fn(&R) -> bool| rows.iter().filter(|r| r.2 == agl && f(r)).count();
                println!("agl {agl}: states {} gate accepts {} street-horizon-24 accepts {}; in -480..-60: {} / {} / {}", n(&|_| true), n(&|r| r.4), n(&|r| r.5), n(&|r| r.0 >= -480.0), n(&|r| r.0 >= -480.0 && r.4), n(&|r| r.0 >= -480.0 && r.5));
            }
            for r in rows.iter().filter(|r| !r.5) {
                println!("rejected by street-horizon-24: y {:.0} dx {:.0} agl {:.0} dh {:.0}", r.0, r.1, r.2, r.3);
            }
        }
        "ends" => {
            // How each prototype acceptance ends: the street escape's helix terminal set, never by leaving the map.
            let (mut helix, mut offmap, mut fail) = (0, 0, 0);
            for k in 0..=240 {
                let s = start(&world, -1100.0 + 5.0 * k as f64);
                let r = rollout_cfg(&world, &JsbPlant::new(&s), Law::new(STREET), usize::MAX, None, &RollCfg { street_horizon: 24.0, ..RollCfg::filter() });
                let e = r.end;
                match (r.ok(), r.tail.is_empty()) {
                    (true, false) => helix += 1,
                    (true, true) => { offmap += 1; println!("off-map end at y {:.0}: ({:.0}, {:.0})", s[Y], e[X], e[Y]); }
                    _ => fail += 1,
                }
            }
            println!("street escape, 24 s, 4 m: helix {helix}, off-map {offmap}, not verified {fail}");
        }
        "why" => {
            // gapentry why FILE: for states listed as `rejected by street-horizon-24` lines, the street escape's
            // needed horizon (4 m margin) and the exact witness.
            let txt = std::fs::read_to_string(&args[1]).unwrap();
            let jobs: Vec<[f64; 4]> = txt.lines().filter(|l| l.starts_with("rejected")).map(|l| {
                let w: Vec<f64> = l.split_whitespace().filter_map(|t| t.parse().ok()).collect();
                [w[0], w[1], w[2], w[3]]
            }).collect();
            let rows = cityflight::harness::par_map(jobs, threads, |&[y, dx, agl, dh]: &[f64; 4]| {
                let x = -120.0 + dx;
                let s = trimmed(x, y, world.terrain(x, y) + agl, 45.0, 0.0, FRAC_PI_2 + f64::to_radians(dh), 0.7);
                let r = rollout_cfg(&world, &JsbPlant::new(&s), Law::new(STREET), usize::MAX, None, &RollCfg { street_horizon: 90.0, ..RollCfg::filter() });
                let wt = witness(&world, &s, 900.0);
                format!("y {y:.0} dx {dx:.0} agl {agl:.0} dh {dh:.0} | street 90 s at 4 m: {:?} at {:.1} s min {:.1} | witness {} min {:.2}", r.outcome, r.t, r.min_clear, if wt.ok { "SAFE" } else { "fail" }, wt.min_clear)
            }, |_, _| {});
            for r in rows {
                println!("{r}");
            }
        }
        "north" => {
            // Gate verdicts on the rest of the street, north of the gap.
            let ys: Vec<f64> = (0..=50).map(|k| 100.0 + 20.0 * k as f64).collect();
            let rows = cityflight::harness::par_map(ys, threads, |&y| {
                let s = start(&world, y);
                let g = gate_verdict(&world, &s);
                let g24 = verdict_cfg(&world, &JsbPlant::new(&s), &RollCfg { street_horizon: 24.0, ..RollCfg::filter() });
                let (ww, we) = walls(&world, y);
                format!("{y:7.1} walls {ww:4.0}/{we:4.0} gate {} gate24 {}", g.ok as u8, g24.ok as u8)
            }, |_, _| {});
            for r in rows {
                println!("{r}");
            }
        }
        _ => {}
    }
}
