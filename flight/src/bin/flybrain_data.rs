//! Training data for the fly brain, and closed-loop evaluation of it.
//!
//! `flybrain_data OUT EPISODES [--brain] [--beta B]`: dogfights of 60 s against a player that circles, weaves,
//! flies straight or flies a random stick. Each tick records the bandit's observation and what
//! `combat::pursuit_law` commands (the label). The bandit flies the law's command with noise injected (so the
//! data covers the states a slightly-wrong pilot reaches), or with `--brain`, the loaded fly brain's command
//! with probability B (DAgger). Writes little-endian f32 rows of `NOBS + NACT`.
//!
//! `flybrain_data --eval EPISODES [--brain]`: no data; prints time to first hit, kills of the player, rounds
//! fired and bandit crashes, for the law or the brain flying.

use cityflight::combat::*;
use cityflight::flybrain::Brain;
use cityflight::model::*;
use cityflight::pilot::{Fbw, Hostile};
use cityflight::world::{Rng, World};
use std::io::Write;

struct EpOut {
    rows: Vec<f32>,
    first_hit: Option<f64>,
    killed: Option<f64>,
    hits: u32,
    rounds: u32,
    crashes: u32,
}

fn episode(w: &World, e: u64, brain: Option<&mut Brain>, beta: f64, record: bool) -> EpOut {
    let mut brain = brain;
    let mut rng = Rng::new(e.wrapping_mul(0x9E37) ^ 0xF17);
    let prm = Params::nominal();
    let mut s = trimmed(rng.range(-1500.0, 1500.0), rng.range(-1500.0, 1500.0), 0.0, 50.0, 0.0, rng.range(-3.2, 3.2), 0.7);
    s[Z] = w.surface(s[X], s[Y]) + rng.range(250.0, 600.0);
    let mut fbw = Fbw::from_state(&s);
    fbw.thr = rng.range(0.5, 1.0);
    let mode = e % 4;
    let bank = rng.range(15.0, 60.0f64).to_radians() * if rng.chance(0.5) { 1.0 } else { -1.0 };
    let (amp, om) = (rng.range(20.0, 60.0f64).to_radians(), rng.range(0.15, 0.6));
    let mut hostile = Hostile::new(e);
    let mut b = Bandit::spawn(w, &s, &mut rng);
    let mut out = EpOut { rows: Vec::new(), first_hit: None, killed: None, hits: 0, rounds: 0, crashes: 0 };
    let (mut noise, mut noise_t) = ([0.0f64; 3], 0.0);
    let mut player_hits = 0u32;
    let mut bullets: Vec<([f64; 3], [f64; 3], f64)> = Vec::new();
    for k in 0..3000 {
        let t = k as f64 * DT_F;
        // The player.
        match mode {
            0 => fbw.phi_ref = bank,
            1 => fbw.phi_ref = amp * (om * t).sin(),
            2 => fbw.phi_ref = 0.0,
            _ => hostile.update(&mut fbw, DT_F),
        }
        let agl = s[Z] - w.surface(s[X], s[Y]);
        fbw.g_ref = if agl < 200.0 { 10f64.to_radians() } else { fbw.g_ref.clamp(-5f64.to_radians(), 8f64.to_radians()) };
        if s[X].abs() > 2300.0 || s[Y].abs() > 2300.0 {
            let back = (-s[Y]).atan2(-s[X]);
            fbw.phi_ref = (1.5 * ((back - s[PSI] + 9.0 * std::f64::consts::PI) % (2.0 * std::f64::consts::PI) - std::f64::consts::PI)).clamp(-0.8, 0.8);
        }
        let prev = s;
        for _ in 0..STEPS_PER_TICK {
            rk4(&prm, &mut s, DT, &[0.0; 3], |st, _| fbw.cmd(&prm, st));
        }
        // The bandit.
        let (obs, law) = b.sense(&s, DT_F);
        if record {
            out.rows.extend_from_slice(&obs);
            out.rows.extend(law.iter().map(|&x| x as f32));
        }
        let mut act = match brain.as_deref_mut() {
            Some(br) if rng.chance(beta) => br.act(&obs),
            _ => law,
        };
        if record {
            noise_t -= DT_F;
            if noise_t <= 0.0 {
                noise_t = rng.range(0.3, 1.5);
                noise = if rng.chance(0.4) { [0.0; 3] } else { [rng.range(-0.35, 0.35), rng.range(-0.12, 0.12), rng.range(-0.2, 0.2)] };
            }
            for i in 0..3 {
                act[i] += noise[i];
            }
        }
        if b.command(w, act, DT_F) && k % 4 == 0 {
            out.rounds += 1;
            let f = dir(&b.s);
            let p = pos(&b.s);
            bullets.push(([p[0] + 4.0 * f[0], p[1] + 4.0 * f[1], p[2] + 4.0 * f[2]], std::array::from_fn(|i| vel(&b.s)[i] + MUZZLE_V * f[i]), 0.0));
        }
        b.fly();
        // Bullets against the player, swept like `Dogfight::tick` (no dispersion).
        let (q0, q1) = (pos(&prev), pos(&s));
        bullets.retain_mut(|(p, v, age)| {
            let p0 = *p;
            v[2] -= G * DT_F;
            *p = std::array::from_fn(|i| p0[i] + v[i] * DT_F);
            *age += DT_F;
            let a: [f64; 3] = std::array::from_fn(|i| p0[i] - q0[i]);
            let ab: [f64; 3] = std::array::from_fn(|i| p[i] - q1[i] - a[i]);
            let tt = (-(a[0] * ab[0] + a[1] * ab[1] + a[2] * ab[2]) / (ab[0] * ab[0] + ab[1] * ab[1] + ab[2] * ab[2]).max(1e-12)).clamp(0.0, 1.0);
            let c: [f64; 3] = std::array::from_fn(|i| a[i] + ab[i] * tt);
            if (c[0] * c[0] + c[1] * c[1] + c[2] * c[2]).sqrt() < HIT_R {
                player_hits += 1;
                return false;
            }
            *age < BULLET_LIFE
        });
        if player_hits > out.hits {
            out.hits = player_hits;
            out.first_hit.get_or_insert(t);
            if player_hits >= HITS_TO_KILL && out.killed.is_none() {
                out.killed = Some(t);
            }
        }
        let d = norm3(pos(&b.s), pos(&s));
        if w.true_clearance(pos(&b.s)) < 0.0 || d > 4000.0 {
            out.crashes += (d <= 4000.0) as u32;
            b = Bandit::spawn(w, &s, &mut rng);
        }
    }
    out
}

fn norm3(a: [f64; 3], b: [f64; 3]) -> f64 {
    ((a[0] - b[0]).powi(2) + (a[1] - b[1]).powi(2) + (a[2] - b[2]).powi(2)).sqrt()
}

fn main() {
    let (mut eval, mut use_brain, mut beta, mut pos) = (false, false, 1.0, Vec::new());
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--eval" => eval = true,
            "--brain" => use_brain = true,
            "--beta" => beta = args.next().and_then(|s| s.parse().ok()).unwrap_or(1.0),
            _ => pos.push(a),
        }
    }
    let (out_path, n): (Option<&String>, u64) = if eval {
        (None, pos.first().and_then(|s| s.parse().ok()).unwrap_or(40))
    } else {
        (pos.first(), pos.get(1).and_then(|s| s.parse().ok()).unwrap_or(200))
    };
    let world = World::new(1337);
    if use_brain && Brain::load_default().is_none() {
        eprintln!("no fly brain at {}", cityflight::flybrain::DEFAULT_PATH);
        std::process::exit(1);
    }
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()).saturating_sub(1).max(1);
    let next = std::sync::atomic::AtomicU64::new(0);
    let t0 = std::time::Instant::now();
    let results: Vec<(u64, EpOut)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                sc.spawn(|| {
                    let mut brain = if use_brain { Brain::load_default() } else { None };
                    let mut mine = Vec::new();
                    loop {
                        let e = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if e >= n {
                            break;
                        }
                        let seed = if eval { 900_000 + e } else { e + if use_brain { 500_000 } else { 0 } };
                        mine.push((e, episode(&world, seed, brain.as_mut(), beta, !eval)));
                    }
                    mine
                })
            })
            .collect();
        let mut all: Vec<_> = hs.into_iter().flat_map(|h| h.join().unwrap()).collect();
        all.sort_by_key(|r| r.0);
        all
    });
    if let Some(p) = out_path {
        let mut f = std::io::BufWriter::new(std::fs::File::create(p).unwrap());
        let mut rows = 0;
        for (_, r) in &results {
            for x in &r.rows {
                f.write_all(&x.to_le_bytes()).unwrap();
            }
            rows += r.rows.len() / (NOBS + NACT);
        }
        eprintln!("{rows} rows from {n} episodes in {:.1} s -> {p}", t0.elapsed().as_secs_f64());
    }
    if eval {
        let k = results.len() as f64;
        let killed: Vec<f64> = results.iter().filter_map(|r| r.1.killed).collect();
        let hit: Vec<f64> = results.iter().filter_map(|r| r.1.first_hit).collect();
        let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len().max(1) as f64;
        println!(
            "{}: player killed in {}/{} ({:.0}%), mean time to kill {:.1} s, first hit in {} (mean {:.1} s), {:.0} rounds/ep, {:.1} hits/ep, {} bandit crashes, {:.1} s",
            if use_brain { "fly brain" } else { "pursuit law" },
            killed.len(),
            results.len(),
            100.0 * killed.len() as f64 / k,
            mean(&killed),
            hit.len(),
            mean(&hit),
            results.iter().map(|r| r.1.rounds as f64).sum::<f64>() / k,
            results.iter().map(|r| r.1.hits as f64).sum::<f64>() / k,
            results.iter().map(|r| r.1.crashes).sum::<u32>(),
            t0.elapsed().as_secs_f64()
        );
    }
}
