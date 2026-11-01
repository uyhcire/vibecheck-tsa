//! Closed-loop check of the library with raw-surface pilots: `JsbExact` stands in for the host's JSBSim
//! (`cityjsb_step_dump`), every tick goes through the state-dump import, and the host flies the surfaces the
//! filter returns. `gatecheck [EPISODES] [--threads N] [--secs S] [--fbw] [--fuel-drain]` (default: infinite fuel, host and filter)
use cityflight::model::{State, GAM, PHI, PSI, V, X, Y, Z};
use cityflight::sim::{random_start, scenario_start, SCENARIOS};
use cityflight::world::Rng;
use cityflight::jsb::Pilot;
use gate::{Config, Filter, PilotKind};
use std::f64::consts::PI;

#[repr(C)]
struct Raw {
    _p: [u8; 0],
}
extern "C" {
    fn cityjsb_new(h: f64, v: f64, gam: f64, psi: f64, phi: f64, alpha: f64) -> *mut Raw;
    fn cityjsb_step_dump(p: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, dump: *mut f64);
    fn cityjsb_set_fuel_freeze(p: *mut Raw, on: i32);
    fn cityjsb_free(p: *mut Raw);
}

const A: f64 = 6378137.0;
const E2: f64 = 6.69437999014e-3;

/// A hostile pilot on raw surfaces: random holds of random sticks, dives, and hard banked pulls.
struct RawPilot {
    rng: Rng,
    hold: f64,
    u: [f64; 4],
}

impl RawPilot {
    fn update(&mut self, dt: f64) -> [f64; 4] {
        self.hold -= dt;
        if self.hold <= 0.0 {
            self.hold = 0.5 + 2.5 * self.rng.f();
            let r = |rng: &mut Rng, a: f64, b: f64| a + (b - a) * rng.f();
            self.u = match (self.rng.f() * 4.0) as u32 {
                0 => [r(&mut self.rng, 0.2, 0.6), r(&mut self.rng, -0.3, 0.3), 0.0, 1.0],
                1 => {
                    let side = if self.rng.f() < 0.5 { -1.0 } else { 1.0 };
                    [r(&mut self.rng, -0.8, -0.3), side * r(&mut self.rng, 0.5, 1.0), 0.0, r(&mut self.rng, 0.0, 1.0)]
                }
                2 => [r(&mut self.rng, -0.1, 0.1), r(&mut self.rng, -0.2, 0.2), 0.0, r(&mut self.rng, 0.4, 0.9)],
                _ => [r(&mut self.rng, -1.0, 1.0), r(&mut self.rng, -1.0, 1.0), r(&mut self.rng, -0.5, 0.5), r(&mut self.rng, 0.0, 1.0)],
            };
        }
        self.u
    }
}

struct Ep {
    verified_start: bool,
    crashed: bool,
    escape_ticks: u64,
    ticks: u64,
    replay_mismatch: u64,
    cpu_ms: Vec<f64>,
}

fn alpha_for(v: f64) -> f64 {
    let cl = 1043.0 * 9.80665 / (0.5 * 1.225 * v * v * 16.2);
    ((cl - 0.31) / 4.6).clamp(-0.05, 0.25)
}

fn run(filter: &mut Filter, s0: State, seed: u64, secs: f64, fbw: bool) -> Ep {
    // Origin placed so the aircraft, which starts at latitude and longitude 0, sits at s0's map position.
    let m = A * (1.0 - E2);
    filter.set_origin(-(s0[Y] / m).to_degrees(), -(s0[X] / A).to_degrees(), 0.0);
    let v = s0[V].max(20.0);
    let raw = unsafe { cityjsb_new(s0[Z], v, s0[GAM], PI / 2.0 - s0[PSI], -s0[PHI], alpha_for(v)) };
    // The host stands in for a JSBSim with propulsion/fuel_freeze set exactly when the filter assumes it is.
    unsafe { cityjsb_set_fuel_freeze(raw, !filter.cfg.fuel_drain as i32) };
    let mut dump = vec![0.0; filter.import_len()];
    unsafe { cityjsb_step_dump(raw, 0.0, 0.0, 0.0, 0.7, dump.as_mut_ptr()) };
    let mut pilot = RawPilot { rng: Rng::new(seed ^ 0x5eed), hold: 0.0, u: [0.0; 4] };
    let n = filter.cfg.tick_frames;
    let dt = n as f64 / 128.0;
    let mut ep = Ep { verified_start: false, crashed: false, escape_ticks: 0, ticks: 0, replay_mismatch: 0, cpu_ms: Vec::new() };
    let ticks = (secs / dt) as u64;
    for k in 0..ticks {
        let u = pilot.update(dt);
        let cmd = if fbw { Pilot::Fbw([1.0 - 2.5 * u[0], -1.5 * u[1], u[3]]) } else { Pilot::Surfaces(u) };
        let plant = filter.import(&dump).expect("dump imports");
        let t = filter.tick(plant, cmd);
        if k == 0 {
            ep.verified_start = t.accept;
        }
        ep.ticks += 1;
        ep.escape_ticks += (!t.accept) as u64;
        ep.replay_mismatch += (!t.replay_exact) as u64;
        ep.cpu_ms.push(t.cpu_ms);
        if t.clearance < 0.0 {
            ep.crashed = true;
            break;
        }
        for s in &t.surfaces {
            unsafe { cityjsb_step_dump(raw, s[0], s[1], s[2], s[3], dump.as_mut_ptr()) };
        }
    }
    unsafe { cityjsb_free(raw) };
    ep
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)?.parse::<f64>().ok());
    let episodes = args.first().and_then(|s| s.parse::<u64>().ok()).unwrap_or(20);
    let threads = arg("--threads").unwrap_or(4.0) as u64;
    let secs = arg("--secs").unwrap_or(60.0);
    let fbw = args.iter().any(|a| a == "--fbw");
    let fuel_drain = args.iter().any(|a| a == "--fuel-drain");
    let next = std::sync::atomic::AtomicU64::new(0);
    let total = episodes + SCENARIOS.len() as u64;
    let results = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|sc| {
        for _ in 0..threads {
            sc.spawn(|| {
                let mut filter = Filter::new(Config { pilot: if fbw { PilotKind::Fbw } else { PilotKind::Surfaces }, fuel_drain, ..Config::default() });
                loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= total {
                        break;
                    }
                    let s0 = if i < episodes {
                        random_start(&filter.world, &mut Rng::new(i.wrapping_mul(7919) ^ 0xE915))
                    } else {
                        scenario_start(&filter.world, (i - episodes) as usize)
                    };
                    let ep = run(&mut filter, s0, i, secs, fbw);
                    results.lock().unwrap().push((i, ep));
                }
            });
        }
    });
    let mut r = results.into_inner().unwrap();
    r.sort_by_key(|x| x.0);
    let (mut crashes, mut crashes_verified, mut verified, mut esc, mut ticks, mut mism) = (0, 0, 0, 0, 0, 0);
    let mut cpu: Vec<f64> = Vec::new();
    for (i, ep) in &r {
        let label = if *i < episodes { format!("episode {i}") } else { format!("scenario {}", SCENARIOS[(*i - episodes) as usize]) };
        if ep.crashed {
            println!("{label}: CRASH (verified start: {})", ep.verified_start);
        }
        crashes += ep.crashed as u64;
        crashes_verified += (ep.crashed && ep.verified_start) as u64;
        verified += ep.verified_start as u64;
        esc += ep.escape_ticks;
        ticks += ep.ticks;
        mism += ep.replay_mismatch;
        cpu.extend(&ep.cpu_ms[1..]);
    }
    cpu.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let q = |p: f64| cpu.get(((cpu.len() as f64 - 1.0) * p) as usize).copied().unwrap_or(0.0);
    println!("{} pilot, {} frames per tick: {crashes} crashes / {total} ({crashes_verified} from {verified} verified starts)", if fbw { "fly-by-wire" } else { "raw-surface" }, r.first().map_or(0, |_| gate::DEFAULT_TICK_FRAMES));
    println!("escape ticks {:.1}% of {ticks}; replay mismatches {mism}", 100.0 * esc as f64 / ticks.max(1) as f64);
    println!("check thread CPU ms: median {:.2}  p99 {:.2}  max {:.2}", q(0.5), q(0.99), q(1.0));
}
