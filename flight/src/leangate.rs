//! The Lean city gate (`CityGate/Ffi.lean`, `c/citygate.h`) as the demo's plant and filter (`--safety-filter exact-rollout-lean`). Every
//! JSBSim frame goes through `citygate_frame`, which runs `cityGate.frame`, the frame `CityGate.city_safe` is
//! about (`frameOut_fst`); the gate's candidate checks run in parallel on Lean's task manager. The pilot stays in
//! Rust: fly-by-wire demands become surfaces each frame from the gate's own observation (`jsb::fbw_law`), or
//! raw surfaces pass straight through.

use crate::jsb::{fbw_bumpless, fbw_law, Gains, Obs, Pilot, DT_JSB, GAINS, NOBS};
use crate::model::*;
use std::sync::atomic::{AtomicBool, Ordering};

/// Set once at startup (`--safety-filter exact-rollout-lean`); every new `Sim` then flies the Lean gate.
pub static LEAN_GATE: AtomicBool = AtomicBool::new(false);

pub fn enabled() -> bool {
    LEAN_GATE.load(Ordering::Relaxed)
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

extern "C" {
    fn citygate_new(x: f64, y: f64, z: f64, v: f64, gam: f64, psi: f64, phi: f64, n: f64, thr: f64) -> *mut Raw;
    fn citygate_start_ok(g: *const Raw) -> i32;
    fn citygate_frame(g: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, out: *mut f64);
    fn citygate_bypass(g: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, out: *mut f64);
    fn citygate_restart(g: *mut Raw) -> i32;
    fn citygate_obs(g: *const Raw, out: *mut f64);
    fn citygate_path(g: *const Raw, xyz: *mut f64, max_points: usize) -> usize;
    fn citygate_trace(g: *const Raw, out: *mut f64, max: usize) -> usize;
    fn citygate_free(g: *mut Raw);
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
}

// The handle is only ever used by the thread that owns the `Sim`; the C ABI registers that thread with Lean.
unsafe impl Send for LeanGate {}

impl Drop for LeanGate {
    fn drop(&mut self) {
        unsafe { citygate_free(self.raw) };
    }
}

impl LeanGate {
    /// The gate at point-mass state `s` (as `JsbPlant::new`).
    pub fn new(s: &State) -> LeanGate {
        let raw = unsafe { citygate_new(s[X], s[Y], s[Z], s[V], s[GAM], s[PSI], s[PHI], s[N], s[THR]) };
        assert!(!raw.is_null(), "libcityjsb: Lean runtime failed to initialise");
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
    }

    fn frame(&mut self, s: [f64; 4], filter_on: bool) {
        let mut out = [0.0; NOUT];
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

    /// Display only: the held controller's predicted path (map metres).
    pub fn path(&self) -> Vec<[f64; 3]> {
        const MAX: usize = 4096;
        let mut xyz = vec![0.0; 3 * MAX];
        let n = unsafe { citygate_path(self.raw, xyz.as_mut_ptr(), MAX) }.min(MAX);
        xyz.chunks_exact(3).take(n).map(|c| [c[0], c[1], c[2]]).collect()
    }
}
