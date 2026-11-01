//! Display smoothness: how far the drawn aircraft moves from one screen frame to the next in straight flight,
//! drawing `Sim::s` directly versus `Drawn` (between the last two ticks, at sim time). The frame loop is the
//! demo's (`App::step`: a 50 Hz tick accumulator), at exact display rates, with the filter off.
//! `cargo run --release --no-default-features --features jsb --bin drawstep -- [FPS ...] [--pm]`
//! (`--pm` flies the point-mass model instead of JSBSim.)
use cityflight::model::*;
use cityflight::pilot::*;
use cityflight::sim::*;
use cityflight::world::*;

fn stats(name: &str, d: &[f64], expect: f64) {
    let n = d.len() as f64;
    let mean = d.iter().sum::<f64>() / n;
    let sd = (d.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / n).sqrt();
    let (lo, hi) = d.iter().fold((f64::INFINITY, f64::NEG_INFINITY), |(a, b), &x| (a.min(x), b.max(x)));
    let jump = d.windows(2).map(|w| (w[1] - w[0]).abs()).fold(0.0, f64::max);
    println!("  {name:10} mean {mean:.4} m  sd {sd:.4} m ({:.1}%)  min {lo:.4}  max {hi:.4}  max frame-to-frame change {jump:.4}  (V·dt {expect:.4})", 100.0 * sd / mean);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    #[cfg(feature = "jsb")]
    cityflight::jsb::parse_fuel_args(&args);
    #[cfg(feature = "jsb")]
    if !args.iter().any(|a| a == "--pm") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let mut rates: Vec<f64> = args.iter().filter_map(|a| a.parse().ok()).collect();
    if rates.is_empty() {
        rates = vec![60.0, 120.0];
    }
    let world = World::new(1337);
    // Scenario 1's trimmed state, moved 150 m above the tallest roof so that straight flight hits nothing.
    let mut s0 = scenario_start(&world, 0);
    s0[Z] = world.raw_top + 150.0;
    let pos = |s: &State| [s[X], s[Y], s[Z]];
    for fps in rates {
        let mut sim = Sim::new(&world, s0, SimCfg { filter_on: false, ..SimCfg::default() });
        let mut fbw = Fbw::from_state(&s0);
        let mut drawn = Drawn::new(&sim);
        let dt = 1.0 / fps;
        let mut acc = 0.0;
        let (mut raw, mut smooth, mut v) = (Vec::new(), Vec::new(), Vec::new());
        // 1 s to settle, then 4 s measured.
        for f in 0..(5.0 * fps) as usize {
            acc += dt;
            let mut n = 0;
            while acc >= DT_F && n < 10 {
                acc -= DT_F;
                n += 1;
                fbw.sticks(0.0, 0.0, DT_F);
                let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
                sim.tick(u);
                drawn.push(&sim);
                fbw.resync(&sim.s, sim.fs.lam, DT_F);
            }
            if acc > DT_F {
                acc = 0.0;
            }
            if f as f64 >= fps {
                raw.push(pos(&sim.s));
                smooth.push(pos(&drawn.at(acc / DT_F)));
                v.push(sim.s[V] * sim.s[GAM].cos());
            }
        }
        let step = |p: &[[f64; 3]]| p.windows(2).map(|w| ((w[1][0] - w[0][0]).powi(2) + (w[1][1] - w[0][1]).powi(2) + (w[1][2] - w[0][2]).powi(2)).sqrt()).collect::<Vec<f64>>();
        let expect = v.iter().sum::<f64>() / v.len() as f64 * dt;
        assert!(!sim.crashed, "crashed during the measurement");
        println!("{fps} Hz display, {} frames, {}:", raw.len(), if sim.jsb.is_some() { "JSBSim plant" } else { "point-mass plant" });
        stats("Sim::s", &step(&raw), expect);
        stats("Drawn", &step(&smooth), expect);
    }
}
