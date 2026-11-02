//! The Lean city gate (`CityGate/Ffi.lean`, `c/citygate.h`) as the demo's plant and filter (`--safety-filter exact-rollout-lean`). Every
//! JSBSim frame goes through `citygate_frame`, which runs `cityGate.frame`, the frame `CityGate.city_safe` is
//! about (`frameOut_fst`); the gate's candidate checks run one after another on the calling thread, or with
//! `CITYGATE_PAR=N` up to N at once on Lean's task manager, in rounds of `CITYGATE_ROUND` frames (default 64). The pilot stays in
//! Rust: fly-by-wire demands become surfaces each frame from the gate's own observation (`jsb::fbw_law`), or
//! raw surfaces pass straight through.

use crate::jsb::{fbw_bumpless, fbw_law, Gains, Obs, Pilot, DT_JSB, GAINS, NOBS};
use crate::model::*;
use crate::world::{MapId, World};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

/// Set once at startup (`--safety-filter exact-rollout-lean`); every new `Sim` then flies the Lean gate.
pub static LEAN_GATE: AtomicBool = AtomicBool::new(false);

pub fn enabled() -> bool {
    LEAN_GATE.load(Ordering::Relaxed)
}

/// Maps the Lean gate checks against their own geometry: the default city built into it, and San Francisco passed
/// in from `World` (`map_handle`).
pub fn covers_map(map: MapId) -> bool {
    match map {
        MapId::Grid | MapId::SanFrancisco => true,
    }
}

#[repr(C)]
struct Raw {
    _p: [u8; 0],
}

/// `citygate_frame` output layout (`c/citygate.h`).
const NOUT: usize = 30;
const OUT_ACCEPTED: usize = 4;
const OUT_OBS: usize = 5;
const OUT_POS: usize = 27;

#[repr(C)]
struct RawMap {
    _p: [u8; 0],
}

extern "C" {
    #[allow(clippy::too_many_arguments)]
    fn citygate_map_new(
        x0: f64,
        y0: f64,
        x1: f64,
        y1: f64,
        tnx: usize,
        tny: usize,
        terr: *const f64,
        nboxes: usize,
        boxes: *const f64,
        rnx: usize,
        rny: usize,
        raster: *const f64,
        top: f64,
    ) -> *mut RawMap;
    #[allow(clippy::too_many_arguments)]
    fn citygate_new_on(m: *const RawMap, x: f64, y: f64, z: f64, v: f64, gam: f64, psi: f64, phi: f64, n: f64, thr: f64) -> *mut Raw;
    fn citygate_rollout(g: *const Raw, esc: u32, max_frames: u32, out: *mut f64, max: usize) -> usize;
    fn citygate_new(x: f64, y: f64, z: f64, v: f64, gam: f64, psi: f64, phi: f64, n: f64, thr: f64) -> *mut Raw;
    fn citygate_start_ok(g: *const Raw) -> i32;
    fn citygate_frame(g: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, out: *mut f64);
    fn citygate_bypass(g: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, out: *mut f64);
    fn citygate_restart(g: *mut Raw) -> i32;
    fn citygate_obs(g: *const Raw, out: *mut f64);
    fn citygate_path(g: *const Raw, xyz: *mut f64, max_points: usize) -> usize;
    fn citygate_frames(g: *const Raw, elev: f64, ail: f64, rud: f64, thr: f64) -> u64;
    fn citygate_probe(g: *const Raw, elev: f64, ail: f64, rud: f64, thr: f64, out: *mut f64, max: usize) -> usize;
    fn citygate_set_parallel(g: *mut Raw, par: u32, round: u32);
    fn citygate_trace(g: *const Raw, out: *mut f64, max: usize) -> usize;
    fn citygate_free(g: *mut Raw);
}

/// The Lean gate's map for San Francisco, built once: its terrain, the boxes covering its prisms
/// (`covering::cover`, checked to contain them) and its raster.
struct MapHandle(*mut RawMap);
// The map is persistent on the Lean side (never freed) and only read.
unsafe impl Send for MapHandle {}
unsafe impl Sync for MapHandle {}

static SF_MAP: OnceLock<MapHandle> = OnceLock::new();

fn map_handle(w: &World) -> *const RawMap {
    match w.map {
        MapId::Grid => std::ptr::null(),
        MapId::SanFrancisco => SF_MAP.get_or_init(|| MapHandle(new_map(w))).0,
    }
}

/// `w` as a Lean gate map.
fn new_map(w: &World) -> *mut RawMap {
    let t0 = std::time::Instant::now();
    let c = crate::covering::cover(w);
    let mut by: Vec<Vec<[f64; 6]>> = vec![Vec::new(); w.boxes.len()];
    for (b, &k) in c.boxes.iter().zip(&c.of) {
        by[k as usize].push(*b);
    }
    let ok = crate::covering::par_range(w.boxes.len(), |k| {
        let b = &w.boxes[k];
        crate::covering::covers(&w.outline(b), b.z0, b.z1, &by[k])
    });
    assert!(ok.iter().all(|&o| o), "covering boxes miss a building");
    let t1 = t0.elapsed().as_secs_f64();
    let terr: Vec<f64> = w.terr.iter().map(|&h| h as f64).collect();
    let boxes: Vec<f64> = c.boxes.iter().flatten().copied().collect();
    let raster: Vec<f64> = w.raw.v.iter().map(|&h| h as f64).collect();
    let m = unsafe {
        citygate_map_new(
            w.x0,
            w.y0,
            w.x1,
            w.y1,
            w.tnx,
            w.tny,
            terr.as_ptr(),
            c.boxes.len(),
            boxes.as_ptr(),
            w.raw.nx,
            w.raw.ny,
            raster.as_ptr(),
            w.raw_top,
        )
    };
    assert!(!m.is_null(), "libcityjsb: the Lean gate rejected the {} map", w.map.name());
    eprintln!("lean gate: {} map, {} boxes covering {} buildings, built in {:.1} s ({:.1} s covering)", w.map.name(), c.boxes.len(), w.boxes.len(), t0.elapsed().as_secs_f64(), t1);
    m
}

/// Trace values per frame (`CityGate.traceE`).
const NTRACE: usize = 26;

/// CPU time of the whole process (s): the calling thread plus Lean's task-manager threads.
pub fn proc_cpu() -> f64 {
    #[cfg(target_os = "macos")]
    const ID: i32 = 12;
    #[cfg(not(target_os = "macos"))]
    const ID: i32 = 2;
    #[repr(C)]
    struct Ts {
        sec: i64,
        nsec: i64,
    }
    extern "C" {
        fn clock_gettime(id: i32, ts: *mut Ts) -> i32;
    }
    let mut ts = Ts { sec: 0, nsec: 0 };
    unsafe { clock_gettime(ID, &mut ts) };
    ts.sec as f64 + ts.nsec as f64 * 1e-9
}

/// Pilot surfaces remembered for telling the pilot's (latched) input from an escape's.
const RECENT: usize = 16;

pub struct LeanGate {
    raw: *mut Raw,
    pub obs: Obs,
    /// Map position (east, north, altitude above sea level) from the gate, as its crash check sees it.
    pub pos: [f64; 3],
    /// JSBSim time minus simulation time (s); frames run while it is negative (as `JsbPlant::lag`).
    pub lag: f64,
    /// Surfaces applied on the last frame (elevator, aileron, rudder, throttle).
    pub surf: [f64; 4],
    /// Fly-by-wire integrators (load factor, roll rate) and gains.
    int: [f64; 2],
    pub gains: Gains,
    /// The start passed the gate's allowed-start check (`CityGate.Init`).
    pub start_ok: bool,
    /// The last frame applied something other than the pilot's recent input: an escape is flying.
    pub escaping: bool,
    recent: [[f64; 4]; RECENT],
    n_recent: usize,
    /// Frames on which the gate took a candidate, and frames in all.
    pub accepted_frames: u64,
    pub frames: u64,
    /// Smoothness metrics over the applied surfaces (as `JsbPlant::tv`, `jump`).
    pub tv: [f64; 4],
    pub jump: [f64; 4],
    /// Per-tick wall time of the gate's frames (ms).
    pub wall_ms: Vec<f32>,
    /// Per-tick CPU time of the calling thread, and of the whole process (ms).
    pub cpu_ms: Vec<f32>,
    pub proc_ms: Vec<f32>,
    /// With `CITYGATE_TRACE` set: per frame, the frame's output and `citygate_trace`, as little-endian f64 bits.
    pub trace: Option<Vec<u8>>,
    /// With `CITYGATE_COUNT` set: per tick, the plant frames a one-after-another check steps (computed separately).
    pub frames_tick: Option<Vec<u32>>,
    /// With `CITYGATE_COUNT`: per tick, the critical path in frames if every candidate ran at once.
    pub crit_tick: Vec<u32>,
    /// With `CITYGATE_PROBE` set: per checked frame, `tick frame` and `CityGate.probeE`'s output; and per tick the
    /// thread CPU (ms) of the gate's own frames, without the probe.
    pub probe: Option<Vec<String>>,
    pub gate_ms: Vec<f32>,
}

// The handle is only ever used by the thread that owns the `Sim`; the C ABI registers that thread with Lean.
unsafe impl Send for LeanGate {}

impl Drop for LeanGate {
    fn drop(&mut self) {
        unsafe { citygate_free(self.raw) };
    }
}

impl LeanGate {
    /// The gate on `w`'s map at point-mass state `s` (as `JsbPlant::new`).
    pub fn new(w: &World, s: &State) -> LeanGate {
        let m = map_handle(w);
        let raw = unsafe {
            if m.is_null() {
                citygate_new(s[X], s[Y], s[Z], s[V], s[GAM], s[PSI], s[PHI], s[N], s[THR])
            } else {
                citygate_new_on(m, s[X], s[Y], s[Z], s[V], s[GAM], s[PSI], s[PHI], s[N], s[THR])
            }
        };
        assert!(!raw.is_null(), "libcityjsb: Lean runtime failed to initialise");
        let env = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<u32>().ok());
        if env("CITYGATE_PAR").is_some() || env("CITYGATE_ROUND").is_some() {
            unsafe { citygate_set_parallel(raw, env("CITYGATE_PAR").unwrap_or(0), env("CITYGATE_ROUND").unwrap_or(0)) };
        }
        let start_ok = unsafe { citygate_start_ok(raw) } != 0;
        let mut g = LeanGate {
            raw,
            obs: Obs::default(),
            pos: [s[X], s[Y], s[Z]],
            lag: 0.0,
            surf: [0.0, 0.0, 0.0, s[THR]],
            int: [0.0; 2],
            gains: GAINS,
            start_ok,
            escaping: false,
            recent: [[f64::NAN; 4]; RECENT],
            n_recent: 0,
            accepted_frames: 0,
            frames: 0,
            tv: [0.0; 4],
            jump: [0.0; 4],
            wall_ms: Vec::new(),
            cpu_ms: Vec::new(),
            proc_ms: Vec::new(),
            trace: std::env::var_os("CITYGATE_TRACE").map(|_| Vec::new()),
            frames_tick: std::env::var_os("CITYGATE_COUNT").map(|_| Vec::new()),
            crit_tick: Vec::new(),
            probe: std::env::var_os("CITYGATE_PROBE").map(|_| Vec::new()),
            gate_ms: Vec::new(),
        };
        let mut o = [0.0; NOBS + 3];
        unsafe { citygate_obs(raw, o.as_mut_ptr()) };
        g.obs = Obs::from(o[..NOBS].try_into().unwrap());
        g.pos = [o[NOBS], o[NOBS + 1], o[NOBS + 2]];
        g
    }

    /// Advance `dt` seconds of simulation time with the pilot's command held, one gate frame per JSBSim frame;
    /// with `filter_on` false the frames bypass the gate.
    pub fn tick(&mut self, u: &Pilot, dt: f64, filter_on: bool) {
        let (w0, c0, p0) = (std::time::Instant::now(), crate::envfilter::thread_cpu(), proc_cpu());
        self.lag -= dt;
        self.gate_ms.push(0.0);
        if let Some(f) = self.frames_tick.as_mut() {
            f.push(0);
            self.crit_tick.push(0);
        }
        while self.lag < -1e-12 {
            // While an escape flies, keep the fly-by-wire bumpless to its surfaces, so a hand-back continues from them.
            if self.escaping {
                self.int = fbw_bumpless(&self.obs, &self.gains, &self.surf);
            }
            let s = match u {
                Pilot::Fbw(c) => fbw_law(&self.obs, &self.gains, &mut self.int, c),
                Pilot::Surfaces(s) => *s,
            };
            self.recent[self.n_recent % RECENT] = s;
            self.n_recent += 1;
            self.frame(s, filter_on);
            self.lag += DT_JSB;
        }
        self.wall_ms.push((w0.elapsed().as_secs_f64() * 1e3) as f32);
        self.cpu_ms.push(((crate::envfilter::thread_cpu() - c0) * 1e3) as f32);
        self.proc_ms.push(((proc_cpu() - p0) * 1e3) as f32);
        // `CITYGATE_STATS=1`: every 250 ticks, the wall time per tick (ms) over them, on stderr.
        if self.wall_ms.len() % 250 == 0 && std::env::var_os("CITYGATE_STATS").is_some() {
            let mut w = self.wall_ms[self.wall_ms.len() - 250..].to_vec();
            w.sort_by(|a, b| a.partial_cmp(b).unwrap());
            eprintln!("citygate ticks {}: wall ms median {:.2} p99 {:.2} max {:.2}", self.wall_ms.len(), w[125], w[247], w[249]);
        }
    }

    fn frame(&mut self, s: [f64; 4], filter_on: bool) {
        if let (Some(f), true) = (self.frames_tick.as_mut(), filter_on) {
            let n = unsafe { citygate_frames(self.raw, s[0], s[1], s[2], s[3]) };
            *f.last_mut().unwrap() += (n >> 32) as u32;
            *self.crit_tick.last_mut().unwrap() += (n & 0xffff_ffff) as u32;
        }
        if let (Some(log), true) = (self.probe.as_mut(), filter_on) {
            let mut buf = vec![0.0; 14 * 8];
            let n = unsafe { citygate_probe(self.raw, s[0], s[1], s[2], s[3], buf.as_mut_ptr(), buf.len()) };
            if n > 0 {
                let vals: Vec<String> = buf[..n].iter().map(|v| format!("{v}")).collect();
                log.push(format!("{} {} {}", self.wall_ms.len(), self.frames, vals.join(" ")));
            }
        }
        let mut out = [0.0; NOUT];
        let c0 = crate::envfilter::thread_cpu();
        unsafe {
            if filter_on {
                citygate_frame(self.raw, s[0], s[1], s[2], s[3], out.as_mut_ptr());
            } else {
                citygate_bypass(self.raw, s[0], s[1], s[2], s[3], out.as_mut_ptr());
            }
        }
        if let Some(t) = self.trace.as_mut() {
            let mut tr = [0.0; NTRACE];
            let n = unsafe { citygate_trace(self.raw, tr.as_mut_ptr(), NTRACE) };
            assert_eq!(n, NTRACE);
            for v in out.iter().chain(tr.iter()) {
                t.extend_from_slice(&v.to_bits().to_le_bytes());
            }
        }
        *self.gate_ms.last_mut().unwrap() += ((crate::envfilter::thread_cpu() - c0) * 1e3) as f32;
        let a = [out[0], out[1], out[2], out[3]];
        for i in 0..4 {
            let d = (a[i] - self.surf[i]).abs();
            self.tv[i] += d;
            self.jump[i] = self.jump[i].max(d);
        }
        self.surf = a;
        self.frames += 1;
        if out[OUT_ACCEPTED] != 0.0 {
            self.accepted_frames += 1;
        }
        let bits = |v: &[f64; 4]| v.map(f64::to_bits);
        self.escaping = !self.recent.iter().any(|r| bits(r) == bits(&a));
        self.obs = Obs::from(out[OUT_OBS..OUT_OBS + NOBS].try_into().unwrap());
        self.pos = [out[OUT_POS], out[OUT_POS + 1], out[OUT_POS + 2]];
    }

    /// Filter back on: the closed loop starts afresh from the current aircraft; whether that start is allowed.
    pub fn restart(&mut self) -> bool {
        self.start_ok = unsafe { citygate_restart(self.raw) } != 0;
        self.escaping = false;
        self.start_ok
    }

    /// The aircraft in the point-mass model's coordinates (as `JsbPlant::state`, with the gate's map position).
    pub fn state(&self) -> State {
        let o = &self.obs;
        let gh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
        [
            self.pos[0],
            self.pos[1],
            self.pos[2],
            o.vt,
            (-o.vned[2]).atan2(gh),
            o.vned[0].atan2(o.vned[1]),
            -o.phi,
            -o.pqr[0],
            o.nz,
            self.surf[3],
        ]
    }

    /// Tooling only: escape `esc` flown as a fresh candidate from the current aircraft (`citygate_rollout`): per
    /// frame the position after it and the surfaces applied, and how it ended (0 clearance failed, 1 cap or street
    /// test, 3 end test passed, 4 frames ran out).
    pub fn rollout(&self, esc: usize, max_frames: usize) -> (Vec<([f64; 3], [f64; 4])>, u32) {
        let mut buf = vec![0.0; 7 * max_frames + 2];
        let n = unsafe { citygate_rollout(self.raw, esc as u32, max_frames as u32, buf.as_mut_ptr(), buf.len()) };
        let frames = buf[n - 2] as usize;
        let path = buf[..7 * frames].chunks_exact(7).map(|c| ([c[0], c[1], c[2]], [c[3], c[4], c[5], c[6]])).collect();
        (path, buf[n - 1] as u32)
    }

    /// Display only: the held controller's predicted path (map metres).
    pub fn path(&self) -> Vec<[f64; 3]> {
        const MAX: usize = 4096;
        let mut xyz = vec![0.0; 3 * MAX];
        let n = unsafe { citygate_path(self.raw, xyz.as_mut_ptr(), MAX) }.min(MAX);
        xyz.chunks_exact(3).take(n).map(|c| [c[0], c[1], c[2]]).collect()
    }
}
