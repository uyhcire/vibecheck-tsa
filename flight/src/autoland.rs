//! Autoland escapes for funnel mode (`--funnel`), the landing funnel test, and the landing contact rule.
//!
//! An autoland escape flies from anywhere onto final for the runway (`runway.rs`), then down the glideslope,
//! flares (John's sink-rate barrier, `sidecar/approach_cbf.py`), touches down and brakes to a stop. The gate's
//! check of an escape ends when it enters the landing funnel (`in_funnel`): from there on the landing is the
//! funnel assumption. Once in the funnel (or on final) every variant flies the same final approach, and its
//! integrators are reset on entry, so what happens after the funnel depends only on the aircraft.
//!
//! Variants (escape index in funnel mode): 0 direct to the downwind point `W` the short way; 1 and 2 the same
//! turning left or right first; 3 a straight full-power climb for `CLIMB_T` first. Inside the city they hold
//! at least their starting altitude; outside it they descend to the pattern altitude, orbiting near `W` (left for
//! 0, 1, 3; right for 2) when too high, and intercept the extended centreline toward the east.

use crate::jsb::{JsbPlant, DT_JSB};
use crate::model::{X, Y, Z};
use crate::runway::*;
use crate::world::World;
use std::f64::consts::{FRAC_PI_2, PI};
use std::sync::atomic::{AtomicBool, Ordering};

/// Funnel mode: the gate's escapes are the autoland variants and its end-of-escape test is `in_funnel`.
pub static FUNNEL: AtomicBool = AtomicBool::new(false);

pub fn funnel() -> bool {
    FUNNEL.load(Ordering::Relaxed)
}

/// Autoland variants (escape indices `0..N_AUTO` in funnel mode).
pub const N_AUTO: usize = 4;
/// Longest escape check in funnel mode (s): from anywhere on the map to the funnel.
pub const HORIZON_FUNNEL: f64 = 300.0;
/// Ticks between checks in funnel mode: a candidate is the pilot's command held this many ticks, then an escape.
pub const FUNNEL_CHECK_TICKS: u32 = 10;

const G0: f64 = 9.80665;
/// Downwind point north of final, pattern altitude (map m), and the city's extent (m).
const WX: f64 = RWY_X0 - 1700.0;
const WY: f64 = RWY_YC + 600.0;
const ZP: f64 = 150.0;
const CITY: f64 = 1300.0;
/// Intercept region (west of the runway, near the extended centreline) and lookaheads (m).
const INT_X0: f64 = RWY_X0 - 2600.0;
const INT_X1: f64 = RWY_X0 - 1000.0;
const INT_Y: f64 = 1100.0;
const L_INT: f64 = 350.0;
const L_LOC: f64 = 250.0;
const L_GND: f64 = 60.0;
/// Speeds (m/s), glideslope (rad), climb-first time (s).
const V_NAV: f64 = 40.0;
const V_FINAL: f64 = 38.0;
const V_SHORT: f64 = 34.0;
const GS: f64 = 3.0 * PI / 180.0;
const CLIMB_T: f64 = 12.0;
/// CG height above the wheels (m), flare start (wheel height, m), John's flare barrier (m/s, 1/s).
pub const GEAR_H: f64 = 1.3;
const FLARE_H: f64 = 12.0;
const SINK_MIN: f64 = 0.9;
const SINK_K: f64 = 0.12;
/// Bank limits (rad): navigating, on final, in the flare.
const BANK_NAV: f64 = 25.0 * PI / 180.0;
const BANK_FINAL: f64 = 15.0 * PI / 180.0;
const BANK_FLARE: f64 = 5.0 * PI / 180.0;

fn wrap(a: f64) -> f64 {
    (a + PI).rem_euclid(2.0 * PI) - PI
}

/// `d` m before the threshold (negative past it): the glideslope's map altitude, which meets the runway
/// `TCH / tan(GS)` (286 m) past the threshold.
fn z_gs(d: f64) -> f64 {
    RWY_Z + TCH + GS.tan() * d
}

/// The aircraft is in the landing funnel (`runway.rs`).
pub fn in_funnel(q: &JsbPlant) -> bool {
    let s = q.state();
    let o = &q.obs;
    let d = RWY_X0 - s[X];
    if !(FUN_D0..=FUN_D1).contains(&d) {
        return false;
    }
    if (s[Y] - RWY_YC).abs() > FUN_LAT_FLOOR.max(FUN_LAT_DEG.to_radians().tan() * d) {
        return false;
    }
    let h = s[Z] - RWY_Z - TCH;
    if h < FUN_GS_LO_DEG.to_radians().tan() * d || h > FUN_GS_HI_DEG.to_radians().tan() * d {
        return false;
    }
    if o.vt < FUN_V_LO || o.vt > FUN_V_HI {
        return false;
    }
    let chi = o.vned[1].atan2(o.vned[0]);
    if wrap(chi - FRAC_PI_2).abs() > FUN_TRACK_DEG.to_radians() || o.phi.abs() > FUN_BANK_DEG.to_radians() {
        return false;
    }
    let vz = -o.vned[2];
    if vz < FUN_VZ_LO || vz > FUN_VZ_HI {
        return false;
    }
    q.fuel() >= FUN_FUEL_LB
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Phase {
    Climb,
    Nav,
    Orbit,
    Final,
    Flare,
    Rollout,
}

/// An autoland escape's state: variant, phase, time, integrators (elevator α, roll, sideslip, throttle), the
/// heading held in the climb, the altitude held inside the city, and whether a forced first turn is done.
#[derive(Clone, Copy, Debug)]
pub struct Auto {
    pub variant: usize,
    pub phase: Phase,
    pub t: f64,
    pub ia: f64,
    pub iphi: f64,
    pub ib: f64,
    pub iv: f64,
    pub chi0: f64,
    pub z_hold: f64,
    pub turned: bool,
}

impl Auto {
    pub fn new(variant: usize) -> Auto {
        Auto {
            variant,
            phase: if variant == 3 { Phase::Climb } else { Phase::Nav },
            t: 0.0,
            ia: 0.0,
            iphi: 0.0,
            ib: 0.0,
            iv: 0.0,
            chi0: f64::NAN,
            z_hold: f64::NAN,
            turned: variant == 0 || variant == 3,
        }
    }

    fn reset(&mut self) {
        (self.ia, self.iphi, self.ib, self.iv) = (0.0, 0.0, 0.0, 0.0);
    }

    /// One frame: phase changes, then elevator, aileron, rudder, throttle, brake (JSBSim conventions).
    pub fn controls(&mut self, q: &JsbPlant) -> [f64; 5] {
        let s = q.state();
        let o = &q.obs;
        let (x, y, z) = (s[X], s[Y], s[Z]);
        let v = o.vt.max(10.0);
        let gh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
        let gam = (-o.vned[2]).atan2(gh);
        let chi = o.vned[1].atan2(o.vned[0]);
        let hw = o.agl - GEAR_H;
        let d = RWY_X0 - x;
        if self.chi0.is_nan() {
            self.chi0 = chi;
            self.z_hold = z;
        }
        // Phase changes.
        if matches!(self.phase, Phase::Climb | Phase::Nav | Phase::Orbit) && in_funnel(q) {
            self.phase = Phase::Final;
            self.reset();
        }
        if self.phase == Phase::Climb && self.t >= CLIMB_T {
            self.phase = Phase::Nav;
            self.z_hold = self.z_hold.max(z);
        }
        let in_city = x.abs() < CITY && y.abs() < CITY;
        let near_w = ((x - WX).powi(2) + (y - WY).powi(2)).sqrt() < 1500.0;
        if self.phase == Phase::Nav && !in_city && near_w && z > ZP + 80.0 {
            self.phase = Phase::Orbit;
        }
        if self.phase == Phase::Orbit && z <= ZP + 30.0 {
            self.phase = Phase::Nav;
        }
        if self.phase == Phase::Final && hw < FLARE_H {
            self.phase = Phase::Flare;
        }
        if matches!(self.phase, Phase::Final | Phase::Flare) && hw < 0.25 {
            self.phase = Phase::Rollout;
        } else if self.phase == Phase::Rollout && hw > 0.6 {
            // Bounced: flare again.
            self.phase = Phase::Flare;
        }
        // Guidance: track command (JSBSim track, clockwise from north), bank limit, flight path, speed, throttle.
        let mut thr_fixed: Option<f64> = None;
        let (e_chi, bank_max, gam_c, v_c) = match self.phase {
            Phase::Climb => {
                thr_fixed = Some(1.0);
                (wrap(self.chi0 - chi), BANK_NAV, 0.15, V_NAV)
            }
            Phase::Nav => {
                let intercept = (INT_X0..=INT_X1).contains(&x) && (y - RWY_YC).abs() < INT_Y;
                let (chi_c, z_t) = if intercept {
                    (FRAC_PI_2 + ((y - RWY_YC) / L_INT).atan(), z_gs(d).min(ZP).max(RWY_Z + 40.0))
                } else {
                    let zt = if in_city { ZP.max(self.z_hold) } else { ZP };
                    ((WX - x).atan2(WY - y), zt)
                };
                let mut e = wrap(chi_c - chi);
                if intercept && e.abs() > 2.0 {
                    // Turn toward the centreline: left when north of it.
                    e = -(y - RWY_YC).signum() * e.abs();
                }
                if !self.turned {
                    if e.abs() < 0.5 {
                        self.turned = true;
                    } else if self.variant == 1 && e > 0.0 {
                        e -= 2.0 * PI;
                    } else if self.variant == 2 && e < 0.0 {
                        e += 2.0 * PI;
                    }
                }
                (e, BANK_NAV, (0.012 * (z_t - z)).clamp(-0.08, 0.12), V_NAV)
            }
            Phase::Orbit => {
                thr_fixed = Some(0.0);
                let dir = if self.variant == 2 { 1.0 } else { -1.0 };
                (dir * 10.0, BANK_NAV, (-0.08 + 0.02 * (v - V_NAV)).clamp(-0.2, 0.0), V_NAV)
            }
            Phase::Final | Phase::Flare => {
                let chi_c = FRAC_PI_2 + ((y - RWY_YC) / L_LOC).atan();
                let g_final = -GS + (0.02 * (z_gs(d) - z)).clamp(-0.05, 0.05);
                let vc = if hw < 30.0 { V_SHORT } else { V_FINAL };
                if self.phase == Phase::Flare {
                    let vz_lim = -(SINK_MIN + SINK_K * hw.max(0.0));
                    if hw < 4.0 {
                        thr_fixed = Some(0.0);
                    }
                    (wrap(chi_c - chi), BANK_FLARE, g_final.max((vz_lim / v).clamp(-1.0, 1.0).asin()), vc)
                } else {
                    (wrap(chi_c - chi), BANK_FINAL, g_final, vc)
                }
            }
            Phase::Rollout => {
                let chi_c = FRAC_PI_2 + ((y - RWY_YC) / L_GND).atan();
                let e = wrap(chi_c - chi);
                let ail = self.roll(o, 0.0);
                let rud = (-2.0 * e + 0.5 * o.pqr[2]).clamp(-1.0, 1.0);
                let brk = if gh < 25.0 { 1.0 } else { 0.5 };
                // Neutral elevator while fast (so it stays on the ground), then the nose held up.
                let elev = if gh > 20.0 { 0.0 } else { -0.2 };
                self.t += DT_JSB;
                return [elev, ail, rud, 0.0, brk];
            }
        };
        // Lateral: bank toward the track command, roll PI-D, sideslip and coordinated-yaw rudder.
        let phi_c = (1.5 * e_chi).clamp(-bank_max, bank_max);
        let ail = self.roll(o, phi_c);
        let r_turn = G0 / v * o.phi.sin();
        let rud_raw = -2.0 * o.beta + 0.5 * (o.pqr[2] - r_turn) + self.ib;
        let rud = rud_raw.clamp(-1.0, 1.0);
        if rud == rud_raw || o.beta * self.ib > 0.0 {
            self.ib = (self.ib - 2.0 * o.beta * DT_JSB).clamp(-0.5, 0.5);
        }
        // Longitudinal: load factor for the flight-path command, then an angle-of-attack loop (the escape law's
        // inner loop with its gains).
        let (sphi, cphi) = o.phi.sin_cos();
        let _ = sphi;
        let n_long = gam.cos() + v * 1.0 * (gam_c - gam) / G0;
        let ncmd = if cphi < 0.35 { 0.3 } else { (n_long / cphi).clamp(0.3, 2.5) };
        let rho = 1.225 * (1.0 - 2.2558e-5 * o.h).max(0.5).powf(4.256);
        let rv2 = rho * v * v;
        let acmd = (-0.058 + 205.0 * ncmd / rv2).min(0.2);
        let n_ach = (acmd + 0.058) * rv2 / 205.0;
        let qcmd = G0 * (n_ach - gam.cos() * cphi) / v;
        let sc = (50.0 / v).powi(2).min(1.0);
        let ea = acmd - o.alpha;
        let e_raw = -0.21 + 2.49 * acmd + 0.6 * qcmd * 40.0 / v + sc * (3.0 * ea - 1.2 * (o.pqr[1] - qcmd)) + self.ia;
        let e = e_raw.clamp(-1.0, 1.0);
        if e == e_raw || ea * self.ia < 0.0 {
            self.ia = (self.ia + 2.0 * ea * DT_JSB).clamp(-0.4, 0.4);
        }
        // Throttle: speed PI (or fixed).
        let thr = match thr_fixed {
            Some(t) => t,
            None => {
                let ev = v_c - v;
                let raw = 0.45 + 0.08 * ev + self.iv;
                if (0.0..=1.0).contains(&raw) || ev * self.iv < 0.0 {
                    self.iv = (self.iv + 0.04 * ev * DT_JSB).clamp(-0.6, 0.6);
                }
                raw.clamp(0.0, 1.0)
            }
        };
        self.t += DT_JSB;
        [-e, ail, rud, thr, 0.0]
    }

    /// Aileron for bank `phi_c` (rad, positive right): roll PI-D.
    fn roll(&mut self, o: &crate::jsb::Obs, phi_c: f64) -> f64 {
        let ephi = phi_c - o.phi;
        let raw = 2.5 * ephi - 0.8 * o.pqr[0] + self.iphi;
        let ail = raw.clamp(-1.0, 1.0);
        if ail == raw || ephi * self.iphi < 0.0 {
            self.iphi = (self.iphi + 1.0 * ephi * DT_JSB).clamp(-0.3, 0.3);
        }
        ail
    }

    /// One frame of the autoland on the aircraft.
    pub fn frame(&mut self, q: &mut JsbPlant) {
        let u = self.controls(q);
        q.frame_brake(u[0], u[1], u[2], u[3], u[4]);
    }
}

/// Airframe points (m from the CG: forward, right, down), from the stock and FlightGear c172p contact points of
/// a level aircraft (`level` in `Spec/CitySafetyChecks.lean`). The wheels come first.
const WHEELS: [[f64; 3]; 6] = [
    [1.24, 0.0, 1.46], [-0.41, -1.09, 1.36], [-0.41, 1.09, 1.36],
    [1.23, 0.0, 1.48], [-0.41, -1.09, 1.35], [-0.41, 1.09, 1.35],
];
const STRUCTURE: [[f64; 3]; 14] = [
    [2.02, 0.0, 0.29], [-3.71, 0.0, 0.76], [-0.03, -5.46, -0.54], [-0.03, 5.46, -0.54],
    [-4.71, 0.0, 0.53], [0.54, -5.89, -0.31], [0.54, 5.89, -0.31],
    [1.22, 0.0, 0.96], [-0.43, -1.22, 0.96], [-0.43, 1.22, 0.96],
    [4.07, 0.0, 0.07], [4.07, 0.0, 0.76], [1.17, 0.0, -0.56], [-5.39, 0.0, -1.32],
];

/// Map position (x east, y north, z up) of body point `b` (forward, right, down) of the aircraft.
fn point(q: &JsbPlant, b: [f64; 3]) -> [f64; 3] {
    let s = q.state();
    let o = &q.obs;
    let (sf, cf) = o.phi.sin_cos();
    let (st, ct) = o.theta.sin_cos();
    let (sp, cp) = o.psi.sin_cos();
    // Body to NED: Rz(psi) Ry(theta) Rx(phi).
    let n = cp * ct * b[0] + (cp * st * sf - sp * cf) * b[1] + (cp * st * cf + sp * sf) * b[2];
    let e = sp * ct * b[0] + (sp * st * sf + cp * cf) * b[1] + (sp * st * cf - cp * sf) * b[2];
    let dn = -st * b[0] + ct * sf * b[1] + ct * cf * b[2];
    [s[X] + e, s[Y] + n, s[Z] - dn]
}

fn on_runway(p: [f64; 3]) -> bool {
    (RWY_X0..=RWY_X1).contains(&p[0]) && (RWY_Y0..=RWY_Y1).contains(&p[1])
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Contact {
    /// Nothing touches (or the aircraft is not near the runway: the usual clearance check applies).
    Clear,
    /// Wheels touch the runway within the rule.
    Rolling,
    /// Stopped on the runway: the flight ends.
    Landed,
    Crash,
}

/// The landing contact rule near the runway (funnel mode); `None` away from it.
pub fn landing_contact(world: &World, q: &JsbPlant) -> Option<Contact> {
    let s = q.state();
    let near = (RWY_X0 - 300.0..=RWY_X1 + 300.0).contains(&s[X]) && (RWY_Y0 - 150.0..=RWY_Y1 + 150.0).contains(&s[Y]);
    if !near || s[Z] > RWY_Z + 20.0 {
        return None;
    }
    for b in STRUCTURE {
        let p = point(q, b);
        if p[2] <= world.terrain(p[0], p[1]) {
            return Some(Contact::Crash);
        }
    }
    let mut touching = 0;
    for b in WHEELS {
        let p = point(q, b);
        if p[2] <= world.terrain(p[0], p[1]) + 0.02 {
            if !on_runway(p) || p[2] < RWY_Z - GEAR_PEN_MAX {
                return Some(Contact::Crash);
            }
            touching += 1;
        }
    }
    if touching == 0 {
        return Some(Contact::Clear);
    }
    let o = &q.obs;
    if -o.vned[2] < -TD_SINK_MAX {
        return Some(Contact::Crash);
    }
    let gs = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
    Some(if gs < LANDED_V { Contact::Landed } else { Contact::Rolling })
}
