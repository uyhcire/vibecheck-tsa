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

const NOBS: usize = 22;

extern "C" {
    fn cityjsb_new(h: f64, v: f64, gam: f64, psi: f64, phi: f64, alpha: f64) -> *mut Raw;
    fn cityjsb_step(p: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, obs: *mut f64);
    fn cityjsb_step_dump(p: *mut Raw, elev: f64, ail: f64, rud: f64, thr: f64, dump: *mut f64);
    fn cityjsb_clone(p: *const Raw) -> *mut Raw;
    fn cityjsb_free(p: *mut Raw);
    fn cityjsb_from_dump(dump: *const f64, n: usize) -> *mut Raw;
    fn cityjsb_obs_from_dump(dump: *const f64, n: usize, obs: *mut f64) -> i32;
    fn cityjsb_dump_len() -> usize;
}

/// Number of doubles in a JSBSim state dump (`jsbx/export_state.hpp`).
pub fn dump_len() -> usize {
    unsafe { cityjsb_dump_len() }
}

/// Map axes for an aircraft anywhere on Earth: east and north on the tangent plane at a WGS84 origin, and
/// height above `alt0` (m above sea level). At latitude and longitude 0 the axes are exactly the ECEF y and z
/// that `JsbPlant::new` starts use.
#[derive(Clone, Copy, Debug)]
pub struct MapFrame {
    ecef0: [f64; 3],
    east: [f64; 3],
    north: [f64; 3],
    pub alt0: f64,
}

const WGS84_A: f64 = 6378137.0;
const WGS84_E2: f64 = 6.69437999014e-3;

fn geodetic_to_ecef(lat: f64, lon: f64, h: f64) -> [f64; 3] {
    let (sp, cp) = lat.sin_cos();
    let (sl, cl) = lon.sin_cos();
    let n = WGS84_A / (1.0 - WGS84_E2 * sp * sp).sqrt();
    [(n + h) * cp * cl, (n + h) * cp * sl, (n * (1.0 - WGS84_E2) + h) * sp]
}

/// Latitude and longitude (rad) of an ECEF position (m).
fn ecef_to_latlon(p: &[f64; 3]) -> (f64, f64) {
    let r = p[0].hypot(p[1]);
    let mut lat = p[2].atan2(r * (1.0 - WGS84_E2));
    for _ in 0..6 {
        let n = WGS84_A / (1.0 - WGS84_E2 * lat.sin().powi(2)).sqrt();
        let h = r / lat.cos() - n;
        lat = p[2].atan2(r * (1.0 - WGS84_E2 * n / (n + h)));
    }
    (lat, p[1].atan2(p[0]))
}

impl MapFrame {
    pub fn new(lat_deg: f64, lon_deg: f64, alt0: f64) -> MapFrame {
        let (sp, cp) = lat_deg.to_radians().sin_cos();
        let (sl, cl) = lon_deg.to_radians().sin_cos();
        MapFrame {
            ecef0: geodetic_to_ecef(lat_deg.to_radians(), lon_deg.to_radians(), 0.0),
            east: [-sl, cl, 0.0],
            north: [-sp * cl, -sp * sl, cp],
            alt0,
        }
    }

    /// East and north (m) of an ECEF position (m).
    pub fn local(&self, ecef: &[f64; 3]) -> [f64; 2] {
        let d: [f64; 3] = std::array::from_fn(|i| ecef[i] - self.ecef0[i]);
        let dot = |u: &[f64; 3]| u[0] * d[0] + u[1] * d[1] + u[2] * d[2];
        [dot(&self.east), dot(&self.north)]
    }

    /// Latitude and longitude (degrees) and altitude above the ellipsoid (m) of map point `(x, y, z)`: the
    /// inverse of `local` horizontally, and `z + alt0` vertically.
    pub fn geodetic(&self, x: f64, y: f64, z: f64) -> [f64; 3] {
        let h = z + self.alt0;
        let mut p: [f64; 3] = std::array::from_fn(|i| self.ecef0[i] + x * self.east[i] + y * self.north[i]);
        let (mut lat, mut lon) = ecef_to_latlon(&p);
        for _ in 0..4 {
            let q = geodetic_to_ecef(lat, lon, h);
            let [qx, qy] = self.local(&q);
            p = std::array::from_fn(|i| q[i] + (x - qx) * self.east[i] + (y - qy) * self.north[i]);
            (lat, lon) = ecef_to_latlon(&p);
        }
        [lat.to_degrees(), lon.to_degrees(), h]
    }
}

/// A pilot command for one tick: the demo's fly-by-wire demands (load factor, roll rate, throttle), or raw
/// surfaces (JSBSim `fcs/*-cmd-norm`: elevator positive nose down, aileron, rudder, throttle).
#[derive(Clone, Copy, Debug)]
pub enum Pilot {
    Fbw(Cmd),
    Surfaces([f64; 4]),
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
    /// ECEF position (m).
    pub ecef: [f64; 3],
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
            ecef: [o[19], o[20], o[21]],
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
    /// Map axes for an imported aircraft (`from_dump`); `None` for `new`, which offsets from `origin`.
    pub frame: Option<MapFrame>,
    /// Smoothness metrics over the frames flown: total variation of each surface command (`surf` order), and
    /// the largest single-frame change since the caller last cleared `jump`.
    pub tv: [f64; 4],
    pub jump: [f64; 4],
}

// The handle is only ever used by the thread that owns the `Sim`.
unsafe impl Send for JsbPlant {}

/// A plant without its Lean state: a state dump (plain doubles) and the Rust-side fields. Another thread
/// rebuilds an independent, bit-identical plant from it (`JsbPlant::from_seed`). Lean reference counts are
/// not atomic, so forks that share Lean objects (`fork`) must stay on one thread; a seed holds none.
#[derive(Clone, Debug)]
pub struct Seed {
    dump: Vec<f64>,
    obs: Obs,
    origin: [f64; 2],
    lag: f64,
    int_n: f64,
    int_p: f64,
    thr: f64,
    surf: [f64; 4],
    gains: Gains,
    frame: Option<MapFrame>,
}

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
            frame: None,
            tv: [0.0; 4],
            jump: [0.0; 4],
        };
        p.int_n = 0.0;
        p.frame(&[s[N], 0.0, s[THR]]);
        (p.tv, p.jump) = ([0.0; 4], [0.0; 4]);
        p
    }

    /// The exact aircraft a JSBSim state dump describes, placed on the map by `frame`; `None` if the dump does
    /// not have `dump_len()` fields. Fly-by-wire state starts at rest (`carry_fbw` keeps it across imports).
    pub fn from_dump(dump: &[f64], frame: MapFrame) -> Option<JsbPlant> {
        let mut out = [0.0; NOBS];
        if unsafe { cityjsb_obs_from_dump(dump.as_ptr(), dump.len(), out.as_mut_ptr()) } != 0 {
            return None;
        }
        let raw = unsafe { cityjsb_from_dump(dump.as_ptr(), dump.len()) };
        if raw.is_null() {
            return None;
        }
        Some(JsbPlant {
            raw,
            obs: Obs::from(&out),
            origin: [0.0, 0.0],
            lag: 0.0,
            int_n: 0.0,
            int_p: 0.0,
            thr: 0.0,
            surf: [0.0; 4],
            gains: GAINS,
            frame: Some(frame),
            tv: [0.0; 4],
            jump: [0.0; 4],
        })
    }

    /// Take over another plant's fly-by-wire integrators and last surfaces.
    pub fn carry_fbw(&mut self, prev: &JsbPlant) {
        self.int_n = prev.int_n;
        self.int_p = prev.int_p;
        self.thr = prev.thr;
        self.surf = prev.surf;
    }

    /// Advance by `dt` seconds with the pilot's command held.
    pub fn advance_pilot(&mut self, u: &Pilot, dt: f64) {
        match u {
            Pilot::Fbw(c) => self.advance(c, dt),
            Pilot::Surfaces(s) => {
                self.lag -= dt;
                while self.lag < -1e-12 {
                    self.frame_raw(s[0], s[1], s[2], s[3]);
                    self.lag += DT_JSB;
                }
            }
        }
    }

    /// An independent copy for look-ahead rollouts.
    pub fn fork(&self) -> JsbPlant {
        let raw = unsafe { cityjsb_clone(self.raw) };
        assert!(!raw.is_null());
        JsbPlant { raw, ..*self }
    }

    /// `advance_pilot`, also returning the surfaces flown on each frame and, if `want_dump`, the state dump after
    /// the last frame (`None` if no frame ran), for `seed`.
    pub fn advance_pilot_dump(&mut self, u: &Pilot, dt: f64, want_dump: bool) -> (Vec<[f64; 4]>, Option<Vec<f64>>) {
        let mut surfs = Vec::with_capacity(4);
        let mut dump = None;
        self.lag -= dt;
        while self.lag < -1e-12 {
            // The same test the loop makes after this frame: is this the tick's last frame?
            let last = !(self.lag + DT_JSB < -1e-12);
            let surf = match u {
                Pilot::Fbw(c) => self.fbw_surf(c),
                Pilot::Surfaces(s) => {
                    self.thr = s[3];
                    self.set_surf(*s);
                    *s
                }
            };
            if want_dump && last {
                dump = Some(self.dump_after(surf));
            }
            self.step_surf(surf);
            self.lag += DT_JSB;
            surfs.push(surf);
        }
        (surfs, dump)
    }

    /// The state dump after one frame with surfaces `s`, leaving this plant unchanged: a clone steps instead
    /// (`JsbExact.step` is a function, so the clone's state is the one this plant reaches with `s`).
    fn dump_after(&self, s: [f64; 4]) -> Vec<f64> {
        let mut d = vec![0.0; dump_len()];
        unsafe {
            let c = cityjsb_clone(self.raw);
            assert!(!c.is_null());
            cityjsb_step_dump(c, s[0], s[1], s[2], s[3], d.as_mut_ptr());
            cityjsb_free(c);
        }
        d
    }

    /// What another thread needs to rebuild this plant, given the dump of its current state.
    pub fn seed(&self, dump: Vec<f64>) -> Seed {
        Seed {
            dump,
            obs: self.obs,
            origin: self.origin,
            lag: self.lag,
            int_n: self.int_n,
            int_p: self.int_p,
            thr: self.thr,
            surf: self.surf,
            gains: self.gains,
            frame: self.frame,
        }
    }

    /// An independent plant equal to the one `s` was taken from. Its Lean objects belong to the calling thread.
    pub fn from_seed(s: &Seed) -> JsbPlant {
        let raw = unsafe { cityjsb_from_dump(s.dump.as_ptr(), s.dump.len()) };
        assert!(!raw.is_null(), "libcityjsb: bad state dump");
        JsbPlant {
            raw,
            obs: s.obs,
            origin: s.origin,
            lag: s.lag,
            int_n: s.int_n,
            int_p: s.int_p,
            thr: s.thr,
            surf: s.surf,
            gains: s.gains,
            frame: s.frame,
            tv: [0.0; 4],
            jump: [0.0; 4],
        }
    }

    /// One JSBSim frame with the surfaces set directly (JSBSim conventions: elevator positive nose down).
    pub fn frame_raw(&mut self, elev: f64, ail: f64, rud: f64, thr: f64) {
        self.thr = thr;
        self.set_surf([elev, ail, rud, thr]);
        self.step_surf(self.surf);
    }

    /// Step JSBSim one frame with surfaces `s` and read the observation.
    fn step_surf(&mut self, s: [f64; 4]) {
        let mut out = [0.0; NOBS];
        unsafe { cityjsb_step(self.raw, s[0], s[1], s[2], s[3], out.as_mut_ptr()) };
        self.obs = Obs::from(&out);
    }

    /// Set the surfaces for the next frame, accumulating the smoothness metrics.
    fn set_surf(&mut self, s: [f64; 4]) {
        for i in 0..4 {
            let d = (s[i] - self.surf[i]).abs();
            self.tv[i] += d;
            self.jump[i] = self.jump[i].max(d);
        }
        self.surf = s;
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
        let s = self.fbw_surf(u);
        self.step_surf(s);
    }

    /// The fly-by-wire loop's surfaces for this frame (updating its integrators, `thr` and `surf`).
    fn fbw_surf(&mut self, u: &Cmd) -> [f64; 4] {
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
        self.set_surf([elev, ail, rud, self.thr]);
        self.surf
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
        let (x, y, z) = match &self.frame {
            Some(f) => {
                let [e, n] = f.local(&o.ecef);
                (e, n, o.h - f.alt0)
            }
            None => (self.origin[0] + o.east, self.origin[1] + o.north, o.h),
        };
        [
            x,
            y,
            z,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_frame_round_trip() {
        for (lat0, lon0, alt0) in [(0.0, 0.0, 0.0), (37.79, -122.40, 15.0), (-33.9, 151.2, 40.0)] {
            let f = MapFrame::new(lat0, lon0, alt0);
            for (x, y, z) in [(0.0, 0.0, 0.0), (2999.0, -2999.0, 450.0), (-1234.5, 2100.25, 3.0)] {
                let [lat, lon, h] = f.geodetic(x, y, z);
                let [e, n] = f.local(&geodetic_to_ecef(lat.to_radians(), lon.to_radians(), h));
                assert!((e - x).abs() < 1e-6 && (n - y).abs() < 1e-6, "{lat0} {lon0}: ({x}, {y}) -> ({e}, {n})");
                assert_eq!(h, z + alt0);
            }
        }
        let f = MapFrame::new(0.0, 0.0, 0.0);
        assert_eq!(f.local(&[WGS84_A + 100.0, 12.5, -40.25]), [12.5, -40.25]);
    }
}

