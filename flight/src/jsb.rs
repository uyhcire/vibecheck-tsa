//! JSBSim's c172p (through the bit-exact Lean port `JsbExact`, `libcityjsb`) as the simulated aircraft.
//!
//! The demo's pilot, filter and escapes command load factor, roll rate and throttle; a small fly-by-wire loop
//! turns those into elevator, aileron, rudder and throttle at JSBSim's 128 Hz frame rate. The aircraft's state
//! is reported back in the point-mass model's coordinates so the filter, world and renderer are unchanged.

use crate::model::*;
use std::f64::consts::PI;
use std::sync::atomic::{AtomicBool, Ordering};

/// Set once at startup (`--jsb`); every new `Sim` then flies JSBSim instead of the point-mass model.
pub static JSB_PLANT: AtomicBool = AtomicBool::new(false);

pub fn enabled() -> bool {
    JSB_PLANT.load(Ordering::Relaxed)
}

#[repr(C)]
struct Raw {
    _p: [u8; 0],
}

const NOBS: usize = 19;

extern "C" {
    fn cityjsb_new(h: f64, v: f64, gam: f64, psi: f64, phi: f64, alpha: f64) -> *mut Raw;
    fn cityjsb_step(p: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, obs: *mut f64);
    fn cityjsb_clone(p: *const Raw) -> *mut Raw;
    fn cityjsb_free(p: *mut Raw);
}

pub const DT_JSB: f64 = 1.0 / 128.0;
/// Dynamic pressure (Pa) the fly-by-wire gains are tuned at (about 50 m/s).
const QBAR_REF: f64 = 1500.0;

#[derive(Clone, Copy, Debug, Default)]
pub struct Obs {
    pub north: f64,
    pub east: f64,
    pub h: f64,
    pub vned: [f64; 3],
    pub vt: f64,
    pub phi: f64,
    pub theta: f64,
    pub psi: f64,
    pub pqr: [f64; 3],
    pub alpha: f64,
    pub beta: f64,
    pub nz: f64,
    pub agl: f64,
    pub qbar: f64,
    pub rpm: f64,
}

impl Obs {
    fn from(o: &[f64; NOBS]) -> Obs {
        Obs {
            north: o[0],
            east: o[1],
            h: o[2],
            vned: [o[3], o[4], o[5]],
            vt: o[6],
            phi: o[7],
            theta: o[8],
            psi: o[9],
            pqr: [o[10], o[11], o[12]],
            alpha: o[13],
            beta: o[14],
            nz: o[15],
            agl: o[16],
            qbar: o[17],
            rpm: o[18],
        }
    }
}

/// Fly-by-wire gains: load-factor PI with pitch damping, roll-rate PI, turn coordination.
#[derive(Clone, Copy, Debug)]
pub struct Gains {
    pub kn_p: f64,
    pub kn_i: f64,
    pub kq: f64,
    pub kp_p: f64,
    pub kp_i: f64,
    pub kb: f64,
    /// Angle-of-attack protection: limit (rad) and nose-down gain beyond it.
    pub a_max: f64,
    pub ka: f64,
}

pub const GAINS: Gains = Gains { kn_p: 0.21, kn_i: 0.84, kq: 0.21, kp_p: 4.0, kp_i: 4.0, kb: 1.4, a_max: 0.26, ka: 24.0 };

pub struct JsbPlant {
    raw: *mut Raw,
    pub obs: Obs,
    origin: [f64; 2],
    /// JSBSim time minus simulation time (s); JSBSim frames run while this is negative.
    pub lag: f64,
    int_n: f64,
    int_p: f64,
    pub thr: f64,
    pub surf: [f64; 4],
    pub gains: Gains,
}

// The handle is only ever used by the thread that owns the `Sim`.
unsafe impl Send for JsbPlant {}

/// Angle of attack for lift `n` g at airspeed `v` (rough c172p lift curve), for the initial state.
fn alpha_for(n: f64, v: f64) -> f64 {
    let qbar = 0.5 * 1.225 * v * v;
    let cl = n * 1043.0 * G / (qbar * 16.2);
    ((cl - 0.31) / 4.6).clamp(-0.05, 0.25)
}

impl JsbPlant {
    /// An aircraft matching the point-mass state `s` (position, speed, flight path, heading, bank, throttle).
    pub fn new(s: &State) -> JsbPlant {
        let v = s[V].max(20.0);
        let alpha = alpha_for(s[N].max(0.5), v);
        let psi_jsb = PI / 2.0 - s[PSI];
        let raw = unsafe { cityjsb_new(s[Z], v, s[GAM], psi_jsb, -s[PHI], alpha) };
        assert!(!raw.is_null(), "libcityjsb: Lean runtime failed to initialise");
        let mut p = JsbPlant {
            raw,
            obs: Obs::default(),
            origin: [s[X], s[Y]],
            lag: 0.0,
            int_n: 0.0,
            int_p: 0.0,
            thr: s[THR],
            surf: [0.0, 0.0, 0.0, s[THR]],
            gains: GAINS,
        };
        p.int_n = 0.0;
        p.frame(&[s[N], 0.0, s[THR]]);
        p
    }

    /// An independent copy for look-ahead rollouts.
    pub fn fork(&self) -> JsbPlant {
        let raw = unsafe { cityjsb_clone(self.raw) };
        assert!(!raw.is_null());
        JsbPlant { raw, ..*self }
    }

    /// One JSBSim frame with the surfaces set directly (JSBSim conventions: elevator positive nose down).
    pub fn frame_raw(&mut self, elev: f64, ail: f64, rud: f64, thr: f64) {
        self.thr = thr;
        self.surf = [elev, ail, rud, thr];
        let mut out = [0.0; NOBS];
        unsafe { cityjsb_step(self.raw, elev, ail, rud, thr, out.as_mut_ptr()) };
        self.obs = Obs::from(&out);
    }

    /// Forget the fly-by-wire integrators (after the escape has flown the surfaces directly).
    pub fn reset_fbw(&mut self) {
        self.int_n = 0.0;
        self.int_p = 0.0;
    }

    /// Set the fly-by-wire integrators so its output on a zero tracking error equals the surfaces now set.
    pub fn bumpless_fbw(&mut self) {
        let (o, g) = (self.obs, self.gains);
        let sched = if o.qbar > 100.0 { (QBAR_REF / o.qbar).min(4.0) } else { 1.0 };
        self.int_n = ((-self.surf[0] / sched + g.kq * o.pqr[1]) / g.kn_i).clamp(-3.0, 3.0);
        self.int_p = (self.surf[1] / (sched * g.kp_i)).clamp(-1.0, 1.0);
    }

    /// One JSBSim frame under the fly-by-wire loop.
    pub fn frame(&mut self, u: &Cmd) {
        let o = self.obs;
        let g = self.gains;
        let sched = if o.qbar > 100.0 { (QBAR_REF / o.qbar).min(4.0) } else { 1.0 };
        let en = u[0] - o.nz;
        let over = (o.alpha - g.a_max).max(0.0);
        let raw = sched * (g.kn_p * en + g.kn_i * self.int_n - g.kq * o.pqr[1]) - g.ka * over;
        let pull = raw.clamp(-1.0, 1.0);
        // Anti-windup: integrate only while the elevator is free and alpha is inside its limit.
        if raw == pull && over == 0.0 || en * self.int_n < 0.0 {
            self.int_n = (self.int_n + en * DT_JSB).clamp(-3.0, 3.0);
        }
        let elev = -pull;
        let ep = -u[1] - o.pqr[0];
        let ail_raw = sched * (g.kp_p * ep + g.kp_i * self.int_p);
        let ail = ail_raw.clamp(-1.0, 1.0);
        if ail_raw == ail || ep * self.int_p < 0.0 {
            self.int_p = (self.int_p + ep * DT_JSB).clamp(-1.0, 1.0);
        }
        let rud = (g.kb * o.beta).clamp(-1.0, 1.0);
        self.thr = u[2].clamp(0.0, 1.0);
        self.surf = [elev, ail, rud, self.thr];
        let mut out = [0.0; NOBS];
        unsafe { cityjsb_step(self.raw, elev, ail, rud, self.thr, out.as_mut_ptr()) };
        self.obs = Obs::from(&out);
    }

    /// Advance by `dt` seconds of simulation time with command `u` held.
    pub fn advance(&mut self, u: &Cmd, dt: f64) {
        self.lag -= dt;
        while self.lag < -1e-12 {
            self.frame(u);
            self.lag += DT_JSB;
        }
    }

    /// The aircraft in the point-mass model's coordinates (x east, y north, heading counter-clockwise from +x,
    /// bank positive left wing down).
    pub fn state(&self) -> State {
        let o = &self.obs;
        let gh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
        [
            self.origin[0] + o.east,
            self.origin[1] + o.north,
            o.h,
            o.vt,
            (-o.vned[2]).atan2(gh),
            o.vned[0].atan2(o.vned[1]),
            -o.phi,
            -o.pqr[0],
            o.nz,
            self.thr,
        ]
    }
}

impl Drop for JsbPlant {
    fn drop(&mut self) {
        unsafe { cityjsb_free(self.raw) }
    }
}
