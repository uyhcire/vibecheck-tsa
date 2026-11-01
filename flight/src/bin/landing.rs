//! Landing tests for funnel mode.
//! `cargo run --release --no-default-features --features jsb --bin landing -- grid` flies the autoland from a grid of
//! landing-funnel states (the funnel assumption's evidence); `-- forced [LB]` flies the gate with LB lb of fuel per
//! tank (default 1.5) and a hostile pilot from a city start until it lands, crashes or runs dry.
use cityflight::autoland::*;
use cityflight::envfilter::Law;
use cityflight::jsb::*;
use cityflight::model::*;
use cityflight::pilot::*;
use cityflight::runway::*;
use cityflight::sim::*;
use cityflight::world::*;
use std::sync::atomic::Ordering;

fn grid(world: &World) {
    set_fuel_lb(LOW_FUEL_LB);
    let mut rows = Vec::new();
    for d in [FUN_D0 + 20.0, 1200.0, FUN_D1 - 50.0] {
        let lat_max = FUN_LAT_FLOOR.max(FUN_LAT_DEG.to_radians().tan() * d) * 0.85;
        let (h_lo, h_hi) = (FUN_GS_LO_DEG.to_radians().tan() * d, FUN_GS_HI_DEG.to_radians().tan() * d);
        for lat in [-lat_max, 0.0, lat_max] {
            for hf in [0.1, 0.5, 0.9] {
                for v in [37.0, 45.0] {
                    let h = h_lo + hf * (h_hi - h_lo);
                    let gam = -3f64.to_radians();
                    let s = trimmed(RWY_X0 - d, RWY_YC + lat, RWY_Z + TCH + h, v, gam, 0.0, 0.45);
                    rows.push((d, lat, h, v, fly(world, &s)));
                }
            }
        }
    }
    // Track and bank corners (±8°) at the near and far ends, mid height, 41 m/s.
    for d in [FUN_D0 + 20.0, FUN_D1 - 50.0] {
        let h = 0.5 * (FUN_GS_LO_DEG.to_radians().tan() + FUN_GS_HI_DEG.to_radians().tan()) * d;
        for (trk, bank) in [(8.0, 0.0), (-8.0, 0.0), (0.0, 8.0), (0.0, -8.0)] {
            let mut s = trimmed(RWY_X0 - d, RWY_YC, RWY_Z + TCH + h, 41.0, -3f64.to_radians(), f64::to_radians(trk), 0.45);
            s[PHI] = f64::to_radians(bank);
            rows.push((d, 0.0, h, 41.0, fly(world, &s)));
        }
    }
    let n = rows.len();
    let landed = rows.iter().filter(|r| r.4.landed).count();
    let not_in = rows.iter().filter(|r| !r.4.started_in).count();
    println!("funnel grid: {landed} / {n} landed and stopped on the runway ({not_in} starts not in the funnel)");
    for r in rows.iter().filter(|r| !r.4.landed) {
        println!("  FAIL d={:.0} lat={:.1} h={:.1} v={:.0}: {}", r.0, r.1, r.2, r.3, r.4.why);
    }
    let td: Vec<&Outcome> = rows.iter().map(|r| &r.4).filter(|o| o.td_x.is_finite()).collect();
    let mx = |f: &dyn Fn(&Outcome) -> f64| td.iter().map(|o| f(o)).fold(f64::NEG_INFINITY, f64::max);
    let mn = |f: &dyn Fn(&Outcome) -> f64| td.iter().map(|o| f(o)).fold(f64::INFINITY, f64::min);
    println!(
        "touchdown: sink max {:.2} m/s (limit {TD_SINK_MAX}), |bank| max {:.1} deg, x {:.0}..{:.0} m, |y - centre| max {:.1} m; stop x {:.0}..{:.0} m (runway {RWY_X0}..{RWY_X1})",
        mx(&|o| o.td_sink), mx(&|o| o.td_bank), mn(&|o| o.td_x), mx(&|o| o.td_x), mx(&|o| o.td_y), mn(&|o| o.stop_x), mx(&|o| o.stop_x)
    );
}

struct Outcome {
    started_in: bool,
    landed: bool,
    why: String,
    td_sink: f64,
    td_bank: f64,
    td_x: f64,
    td_y: f64,
    stop_x: f64,
}

/// Fly the autoland (variant 0; in the funnel every variant flies the same final) from `s`.
fn fly(world: &World, s: &State) -> Outcome {
    let mut q = JsbPlant::new(s);
    let started_in = in_funnel(&q);
    let mut law = Law::new(0);
    let mut o = Outcome { started_in, landed: false, why: String::new(), td_sink: f64::NAN, td_bank: f64::NAN, td_x: f64::NAN, td_y: f64::NAN, stop_x: f64::NAN };
    for k in 0..(200.0 / DT_JSB) as usize {
        law.step(world, &mut q);
        let st = q.state();
        match landing_contact(world, &q) {
            Some(Contact::Crash) => {
                o.why = format!("crash (contact rule) at t={:.1} s, x={:.0}, z={:.1}, sink {:.2}", k as f64 * DT_JSB, st[X], st[Z], -q.obs.vned[2]);
                return o;
            }
            Some(Contact::Rolling) | Some(Contact::Landed) if o.td_x.is_nan() => {
                (o.td_sink, o.td_bank) = (-q.obs.vned[2], q.obs.phi.abs().to_degrees());
                (o.td_x, o.td_y) = (st[X], (st[Y] - RWY_YC).abs());
                o.td_sink = o.td_sink.min(0.0).abs();
            }
            _ => {}
        }
        if landing_contact(world, &q) == Some(Contact::Landed) {
            o.landed = true;
            o.stop_x = st[X];
            return o;
        }
        if landing_contact(world, &q).is_none() && world.airframe_clearance(&st, 200.0) < 0.0 {
            o.why = format!("crash (clearance) at t={:.1} s, x={:.0}, z={:.1}", k as f64 * DT_JSB, st[X], st[Z]);
            return o;
        }
    }
    o.why = "no stop within 200 s".into();
    o
}

fn forced(world: &World, lb: f64) {
    set_fuel_lb(lb);
    cityflight::envfilter::ENV_FILTER.store(4, Ordering::Relaxed);
    let s0 = trimmed(-700.0, -900.0, 200.0, 45.0, 0.0, 3.0, 0.7);
    let cfg = SimCfg { filter_on: true, filter: cityflight::filter::FilterCfg { phase: cityflight::filter::Phase::P1, robust: false }, mismatch: false, seed: 7 };
    let mut sim = Sim::new(world, s0, cfg);
    let mut fbw = Fbw::from_state(&s0);
    let mut hostile = Hostile::new(7);
    let start_ok = sim.env_gate.as_ref().is_some_and(|g| g.witness.is_some());
    let mut empty_at = f64::NAN;
    while sim.time() < 900.0 && !sim.crashed && !sim.landed {
        hostile.update(&mut fbw, DT_F);
        let up = fbw.cmd(&sim.prm_ctrl, &sim.s);
        sim.tick(up);
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        if empty_at.is_nan() && sim.jsb.as_ref().is_some_and(|p| p.fuel() < 0.0) {
            empty_at = sim.time();
        }
    }
    let fuel = sim.jsb.as_ref().map_or(f64::NAN, |p| p.fuel());
    println!(
        "forced landing ({lb} lb per tank, start {}): {} at t={:.1} s, fuel left {:.2} lb, engine stopped at {:.1} s, {:.1}% of ticks committed",
        if start_ok { "verified" } else { "unverified" },
        if sim.landed { "LANDED (stopped on the runway)" } else if sim.crashed { "CRASHED" } else { "still flying" },
        sim.time(),
        fuel,
        empty_at,
        100.0 * sim.commit_ticks as f64 / sim.ticks.max(1) as f64
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    JSB_PLANT.store(true, Ordering::Relaxed);
    FUNNEL.store(true, Ordering::Relaxed);
    cityflight::envfilter::N_USED.store(N_AUTO as u8, Ordering::Relaxed);
    cityflight::envfilter::CHECK_THREADS.store(N_AUTO, Ordering::Relaxed);
    let world = World::new(1337);
    match args.first().map(|s| s.as_str()) {
        Some("forced") => forced(&world, args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1.5)),
        _ => grid(&world),
    }
}
