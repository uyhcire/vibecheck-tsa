//! Rust side of the Rust/Lean escape-law and end-test comparison (`Tools/GateFaith.lean` writes the same lines).
use cityflight::envfilter::{law_params, terminal_ok, Hist, Law, LawP, N_ESC, SAMPLE, TERM_EVERY, T_TERM};
use cityflight::harness::par_map;
use cityflight::jsb::{JsbPlant, DT_JSB, JSB_PLANT};
use cityflight::model::*;
use cityflight::sim::random_start;
use cityflight::world::{Rng, World};
use std::fmt::Write;

const FNV0: u64 = 0xcbf29ce484222325;

fn fnv(h: &mut u64, x: f64) {
    let b = if x.is_nan() { 0x7ff8000000000000u64 } else { x.to_bits() };
    for b in b.to_le_bytes() {
        *h = (*h ^ b as u64).wrapping_mul(0x100000001b3);
    }
}

fn hx(x: f64) -> String {
    format!("{:016x}", x.to_bits())
}

fn unhx(s: &str) -> f64 {
    f64::from_bits(u64::from_str_radix(s, 16).expect("hex f64"))
}

/// A state dump and its map origin, from `JsbPlant::new` on 9 start numbers plus a hold of raw surfaces.
struct Start {
    id: usize,
    origin: [f64; 2],
    dump: Vec<f64>,
    frames: usize,
}

fn plant(st: &Start) -> JsbPlant {
    JsbPlant::from_dump_origin(&st.dump, st.origin).expect("state dump")
}

fn starts(out: &str, n: u64) {
    let world = World::new(1337);
    let mut o = String::new();
    let mut id = 0;
    let mut put = |o: &mut String, s: [f64; 9], pre: usize, u: [f64; 4], frames: usize| {
        let mut p = JsbPlant::new(&[s[0], s[1], s[2], s[3], s[4], s[5], s[6], 0.0, s[7], s[8]]);
        for _ in 0..pre {
            p.frame_raw(u[0], u[1], u[2], u[3]);
        }
        let (dump, origin) = p.dump_next(p.surf);
        write!(o, "S {id} {frames} {} {} {}", hx(origin[0]), hx(origin[1]), dump.len()).unwrap();
        dump.iter().for_each(|&v| write!(o, " {}", hx(v)).unwrap());
        o.push('\n');
        id += 1;
    };
    put(&mut o, [0.0, 0.0, 150.0, 30.0, -0.1, 1.570796, 0.4, 1.0, 1.0], 0, [0.0; 4], 2048);
    put(&mut o, [0.0, 0.0, 950.0, 40.0, 0.1, 1.570796, 0.0, 1.0, 1.0], 0, [0.0; 4], 5120);
    for e in 0..n {
        let s0 = random_start(&world, &mut Rng::new(e.wrapping_mul(7919) ^ 0xE915));
        let mut rng = Rng::new(e ^ 0xFA17);
        let u = [rng.range(-0.6, 0.3), rng.range(-1.0, 1.0), rng.range(-0.5, 0.5), rng.range(0.0, 1.0)];
        let pre = (rng.range(0.0, 1.5) / DT_JSB) as usize;
        put(&mut o, [s0[X], s0[Y], s0[Z], s0[V], s0[GAM], s0[PSI], s0[PHI], s0[N], s0[THR]], pre, u, 2560);
    }
    std::fs::write(out, &o).unwrap();
    println!("{id} starts to {out}");
}

fn read_starts(path: &str) -> Vec<Start> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter(|l| l.starts_with("S "))
        .map(|l| {
            let w: Vec<&str> = l.split_whitespace().collect();
            let n: usize = w[5].parse().unwrap();
            Start { id: w[1].parse().unwrap(), frames: w[2].parse().unwrap(), origin: [unhx(w[3]), unhx(w[4])], dump: w[6..6 + n].iter().map(|s| unhx(s)).collect() }
        })
        .collect()
}

fn law_vals(l: &Law) -> [f64; 9] {
    [l.t, l.ia, l.ib, l.iphi, l.psi_ref, l.axis, l.side, l.next_try, l.captured as u8 as f64]
}

/// End-test verdicts follow `rollout_law`'s schedule but continue past the first pass.
fn fly(world: &World, st: &Start, esc: usize) -> (Vec<u64>, Vec<(usize, bool)>) {
    let mut q = plant(st);
    let mut law = Law::new(esc);
    law.capture(&q.obs);
    let (mut hs, mut ts, mut hist, mut psi_prev) = (Vec::new(), Vec::new(), Vec::new(), f64::NAN);
    hist.push(Hist::of(&q, 0.0, &mut psi_prev));
    let k_term = (T_TERM / DT_JSB).round() as usize;
    for k in 1..=st.frames {
        law.step(world, &mut q);
        let mut h = FNV0;
        q.surf.iter().chain(&q.obs.to_array()).chain(&law_vals(&law)).for_each(|&v| fnv(&mut h, v));
        hs.push(h);
        if k % SAMPLE == 0 {
            hist.push(Hist::of(&q, k as f64 * DT_JSB, &mut psi_prev));
            if hist.len() > 65 {
                hist.remove(0);
            }
            if k >= k_term && k % TERM_EVERY == 0 && law.turning() {
                ts.push((k, terminal_ok(world, law.dir(), law.kind(), &hist)));
            }
        }
    }
    (hs, ts)
}

fn laws(sp: &str, out: &str, threads: usize) {
    let world = World::new(1337);
    let st = read_starts(sp);
    let jobs: Vec<(usize, usize)> = (0..st.len()).flat_map(|i| (0..N_ESC).map(move |e| (i, e))).collect();
    let res = par_map(jobs, threads, |&(i, e)| (i, e, fly(&world, &st[i], e)), |_, _| {});
    let mut o = String::new();
    let mut pass = [0usize; N_ESC];
    for (i, e, (hs, ts)) in res {
        write!(o, "L {} {e}", st[i].id).unwrap();
        hs.iter().for_each(|h| write!(o, " {h:016x}").unwrap());
        write!(o, "\nT {} {e}", st[i].id).unwrap();
        ts.iter().for_each(|(k, v)| write!(o, " {k}:{}", *v as u8).unwrap());
        o.push('\n');
        pass[e] += ts.iter().any(|t| t.1) as usize;
    }
    std::fs::write(out, o).unwrap();
    println!("{} starts x {N_ESC} escapes to {out}; starts whose end test passes somewhere, per escape: {pass:?}", st.len());
}

/// The reference-trajectory hashes of `docs/escape-law-terminal.md`.
fn reftraj(p: LawP, verbose: bool) {
    for (name, s, n) in [("A", [0.0, 0.0, 150.0, 30.0, -0.1, std::f64::consts::FRAC_PI_2, 0.4, 1.0, 1.0], 2048), ("B", [0.0, 0.0, 950.0, 40.0, 0.1, std::f64::consts::FRAC_PI_2, 0.0, 1.0, 1.0], 5120)] {
        let mut q = JsbPlant::new(&[s[0], s[1], s[2], s[3], s[4], s[5], s[6], 0.0, s[7], s[8]]);
        let mut law = Law::with(0, p);
        let mut h = FNV0;
        for k in 0..n {
            let u = law.controls(&q.obs);
            q.frame_raw(u[0], u[1], u[2], u[3]);
            law.t += DT_JSB;
            let x = q.state();
            u.iter().chain(&[x[X], x[Y], x[Z]]).for_each(|&v| fnv(&mut h, v));
            if verbose && (k + 1) % 256 == 0 {
                println!("{} {}", k + 1, u.iter().chain(&[x[X], x[Y], x[Z]]).map(|&v| hx(v)).collect::<Vec<_>>().join(" "));
            }
        }
        println!("start {name}, {n} frames: HASH {h:016x}");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    let threads = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(3);
    match args.first().map(|s| s.as_str()) {
        Some("starts") => starts(&args[1], args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40)),
        Some("laws") => laws(&args[1], &args[2], threads),
        Some("reftraj") => reftraj(if args.iter().any(|a| a == "--gate-law") { LawP { v_eas_t: [0.0; 4], h_level: f64::INFINITY, ..law_params() } } else { law_params() }, args.iter().any(|a| a == "-v")),
        _ => eprintln!("usage: gatefaith starts OUT [N] | laws STARTS OUT [--threads T] | reftraj [--gate-law]"),
    }
}
