//! The plant's fuel-freeze setting against `JsbExact.step`: flies `JsbPlant` (default flags: fuel freeze on;
//! `--fuel-drain`: off) over pseudo-random surfaces and prints the FNV-1a hash of every frame's observation bits,
//! with the start parameters. `lake exe fuelfreezecheck <the printed args>` prints the hash `JsbExact.step`
//! gives with `fuelFreeze` true and false; the line for this run's setting must match.
//! `fuelcheck [FRAMES] [--fuel-drain]`
use cityflight::jsb::*;
use cityflight::model::*;
use std::f64::consts::PI;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    parse_fuel_args(&args);
    let frames: usize = args.iter().find_map(|a| a.parse().ok()).unwrap_or(5000);
    let s0 = trimmed(0.0, 0.0, 800.0, 50.0, 0.0, 0.3, 0.7);
    let mut p = JsbPlant::new(&s0);
    let (v, alpha) = (s0[V].max(20.0), alpha_for(s0[N].max(0.5), s0[V].max(20.0)));
    let init = p.surf;
    let b = |x: f64| x.to_bits();
    println!(
        "args {} {} {} {} {} {} {} {} {} {} {}",
        b(s0[Z]), b(v), b(s0[GAM]), b(PI / 2.0 - s0[PSI]), b(-s0[PHI]), b(alpha), b(init[0]), b(init[1]), b(init[2]), b(init[3]), frames
    );
    let mut x: u64 = 12345;
    let mut h: u64 = 14695981039346656037;
    let mut u = || {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (x >> 11) as f64 / 9007199254740992.0
    };
    for _ in 0..frames {
        let (e, a, r, t) = (-1.0 + 2.0 * u(), -1.0 + 2.0 * u(), -0.5 + 1.0 * u(), 0.0 + 1.0 * u());
        p.frame_raw(e, a, r, t);
        let o = &p.obs;
        let all = [o.north, o.east, o.h, o.vned[0], o.vned[1], o.vned[2], o.vt, o.phi, o.theta, o.psi, o.pqr[0], o.pqr[1], o.pqr[2], o.alpha, o.beta, o.nz, o.agl, o.qbar, o.rpm, o.ecef[0], o.ecef[1], o.ecef[2]];
        for v in all {
            h = (h ^ v.to_bits()).wrapping_mul(1099511628211);
        }
    }
    println!("{} {}", if p.fuel_freeze() { "freeze" } else { "drain" }, h);
}
