//! Fly-by-wire tuning on the JSBSim plant. The target is the point-mass model's own response: load factor and
//! roll rate follow their commands through first-order lags (`tau_n`, `tau_p`), load factor capped by lift.
//! `cargo run --release --no-default-features --features jsb --bin jsbtune [-- search | -v]`
use cityflight::jsb::*;
use cityflight::model::*;

/// Mean tracking errors (load factor, roll rate) against the lagged commands, and the worst alpha.
fn score(g: Gains, v: f64, verbose: bool) -> (f64, f64, f64) {
    let prm = Params::nominal();
    let s0 = trimmed(0.0, 0.0, 600.0, v, 0.0, 0.0, 0.7);
    let mut p = JsbPlant::new(&s0);
    p.gains = g;
    let (mut nref, mut pref) = (1.0, 0.0);
    let (mut en, mut ep, mut amax) = (0.0, 0.0, 0.0f64);
    let (mut cn, mut cp) = (0, 0);
    for k in 0..(128 * 12) {
        let t = k as f64 * DT_JSB;
        let s = p.state();
        let nc = if (2.0..4.0).contains(&t) { 2.0 } else if (6.0..7.0).contains(&t) { 0.4 } else { s[GAM].cos() };
        let pc = if (8.0..8.8).contains(&t) { 0.6 } else if (8.8..9.6).contains(&t) { -0.6 } else { -1.5 * s[PHI] };
        let ncl = nc.min(n_lift(&prm, s[V]));
        nref += (ncl - nref) * DT_JSB / prm.tau_n;
        pref += (pc - pref) * DT_JSB / prm.tau_p;
        p.frame(&[nc, pc, 0.7]);
        let s = p.state();
        if t > 1.0 && t < 7.5 {
            en += (s[N] - nref).abs();
            cn += 1;
        }
        if t > 7.5 {
            ep += (s[P] - pref).abs();
            cp += 1;
        }
        amax = amax.max(p.obs.alpha);
        if verbose && k % 16 == 0 {
            println!(
                "t={t:.2} nc={nc:.2} nref={nref:.2} n={:.2} pc={pc:.2} pref={pref:.2} p={:.2} phi={:.2} v={:.1} elev={:.2} ail={:.2} a={:.3}",
                s[N], s[P], s[PHI], s[V], p.surf[0], p.surf[1], p.obs.alpha
            );
        }
    }
    (en / cn as f64, ep / cp as f64, amax)
}

fn total(g: Gains) -> f64 {
    [32.0, 45.0, 58.0].iter().map(|&v| {
        let (a, b, am) = score(g, v, false);
        a + b + 5.0 * (am - 0.30).max(0.0)
    }).sum()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut best = GAINS;
    if args.iter().any(|a| a == "search") {
        let mut bt = total(best);
        for round in 0..4 {
            for f in 0..7 {
                for &m in &[0.5, 0.7, 1.4, 2.0] {
                    let mut g = best;
                    let x = match f { 0 => &mut g.kn_p, 1 => &mut g.kn_i, 2 => &mut g.kq, 3 => &mut g.kp_p, 4 => &mut g.kp_i, 5 => &mut g.kb, _ => &mut g.ka };
                    *x *= m;
                    let t = total(g);
                    if t < bt { bt = t; best = g; }
                }
            }
            println!("round {round}: {bt:.4} {best:?}");
        }
    }
    for &v in &[32.0, 45.0, 58.0] {
        let (a, b, am) = score(best, v, false);
        println!("v={v}: mean |n err|={a:.3}  mean |p err|={b:.3}  max alpha={am:.3}");
    }
    if args.iter().any(|a| a == "-v") {
        score(best, 45.0, true);
    }
}
