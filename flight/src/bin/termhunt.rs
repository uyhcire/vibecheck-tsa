//! `termhunt [SEED N [SECS]] [--only I]`: escapes that verify from sampled states, flown on until above everything; exits 1 on any contact.
use cityflight::envfilter::{rollout, Law, ESCAPES};
use cityflight::jsb::{JsbPlant, DT_JSB};
use cityflight::model::*;
use cityflight::world::{Rng, World};
use std::f64::consts::PI;

/// Float stand-in for the Lean `Crash` (6 m cube around the reference point): contact iff ≤ 0.
fn cube_margin(world: &World, s: &State) -> f64 {
    let (x, y, z) = (s[X], s[Y], s[Z]);
    let mut m = f64::INFINITY;
    for i in 0..25 {
        for j in 0..25 {
            m = m.min(z - 6.0 - world.terrain(x - 6.0 + 0.5 * i as f64, y - 6.0 + 0.5 * j as f64));
        }
    }
    for b in &world.boxes {
        let dx = (b.x0 - x).max(x - b.x1).max(0.0);
        let dy = (b.y0 - y).max(y - b.y1).max(0.0);
        let dz = (b.z0 - z).max(z - b.z1).max(0.0);
        m = m.min(dx.max(dy).max(dz) - 6.0);
    }
    m
}

fn main() {
    let all: Vec<String> = std::env::args().skip(1).collect();
    cityflight::jsb::parse_fuel_args(&all);
    let only: Option<usize> = all.iter().position(|a| a == "--only").and_then(|i| all.get(i + 1)?.parse().ok());
    let args: Vec<&String> = all.iter().enumerate().filter(|(i, a)| !a.starts_with("--") && (*i == 0 || all[i - 1] != "--only")).map(|x| x.1).collect();
    let seed: u64 = args.first().map_or(22, |s| s.parse().unwrap());
    let n: usize = args.get(1).map_or(3000, |s| s.parse().unwrap());
    let secs: f64 = args.get(2).map_or(400.0, |s| s.parse().unwrap());
    let world = World::new(1337);
    let top = cityflight::envfilter::top(&world);
    let tall: Vec<_> = world.boxes.iter().filter(|b| b.z1 - b.z0 >= 100.0).collect();
    let mut rng = Rng::new(seed);
    let (mut passed, mut best, mut hits) = (0, f64::INFINITY, 0);
    for i in 0..n {
        let kind = rng.range(0.0, 3.0);
        let mut psi = rng.range(-PI, PI);
        let (x, y, z);
        if kind < 1.0 {
            let b = tall[(rng.f() * tall.len() as f64) as usize];
            let (d, a) = (rng.range(15.0, 150.0), rng.range(-PI, PI));
            let (cx, cy) = (0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1));
            let half = 0.5 * (b.x1 - b.x0).max(b.y1 - b.y0);
            x = cx + (half + d) * a.cos();
            y = cy + (half + d) * a.sin();
            z = b.z0 + rng.range(0.4, 1.15) * (b.z1 - b.z0);
            psi = (cy - y).atan2(cx - x) + rng.range(-1.2, 1.2);
        } else if kind < 2.0 {
            let side = (rng.f() * 4.0) as u32;
            let (along, m) = (rng.range(-3000.0, 3000.0), rng.range(2450.0, 3060.0));
            (x, y) = match side { 0 => (m, along), 1 => (-m, along), 2 => (along, m), _ => (along, -m) };
            z = world.terrain(x, y) + rng.range(10.0, 220.0);
        } else {
            x = rng.range(-2800.0, 2800.0);
            y = rng.range(-2800.0, 2800.0);
            z = world.surface(x, y) + rng.range(20.0, 400.0);
        }
        let v = if rng.f() < 0.3 { rng.range(22.0, 30.0) } else { rng.range(30.0, 70.0) };
        let (gam, phi, thr) = (rng.range(-0.4, 0.3), rng.range(-1.2, 1.2), rng.f());
        let pre = (rng.f() * 192.0) as usize;
        let u: [f64; 4] = [rng.range(-1.0, 1.0), rng.range(-1.0, 1.0), rng.range(-1.0, 1.0), rng.f()];
        let esc = (rng.f() * 6.0) as usize % 6;
        let s0: State = [x, y, z, v, gam, psi, phi, 0.0, gam.cos() / phi.cos(), thr];
        if only.is_some_and(|o| o != i) {
            continue;
        }
        let mut p = JsbPlant::new(&s0);
        for _ in 0..pre {
            p.frame_raw(u[0], u[1], u[2], u[3]);
        }
        let r = rollout(&world, &p, esc, usize::MAX);
        if !r.ok() {
            continue;
        }
        passed += 1;
        let mut q = p.fork();
        let mut law = Law::new(esc);
        let (mut m_cube, mut m_sph, mut t_min, mut pos) = (f64::INFINITY, f64::INFINITY, 0.0, [0.0; 3]);
        let mut first_hit = None;
        let mut ending = "timeout";
        for k in 1..=(secs / DT_JSB) as usize {
            law.step(&world, &mut q);
            let s = q.state();
            if s[Z] - 6.0 > top + 20.0 {
                ending = "above-top";
                break;
            }
            let t = k as f64 * DT_JSB;
            if t <= r.t {
                continue;
            }
            let c = cube_margin(&world, &s);
            m_sph = m_sph.min(world.airframe_clearance(&s, 200.0));
            if c < m_cube {
                (m_cube, t_min, pos) = (c, t, [s[X], s[Y], s[Z]]);
            }
            if c <= 0.0 && first_hit.is_none() {
                first_hit = Some(t);
            }
            if c < -20.0 {
                ending = "deep-contact";
                break;
            }
        }
        if first_hit.is_some() {
            hits += 1;
        }
        if first_hit.is_some() || m_cube < best {
            best = best.min(m_cube);
            println!(
                "{} i={i} esc={} verdict t {:.2}: cube margin {m_cube:.2} (sphere {m_sph:.2}) at t {t_min:.1} pos [{:.0}, {:.0}, {:.0}] end {ending}\n  start {s0:?} pre {pre} u {u:?}",
                if first_hit.is_some() { "HIT" } else { "near" }, ESCAPES[esc].name, r.t, pos[0], pos[1], pos[2]
            );
        }
    }
    println!("seed {seed}: {n} cases, {passed} passed the end test, {hits} hit, closest {best:.2}");
    if hits > 0 {
        std::process::exit(1);
    }
}
