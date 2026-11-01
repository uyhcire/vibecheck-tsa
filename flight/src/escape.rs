//! Backup (escape) maneuvers and the forward predictor that turns them into
//! the implicit backup CBF
//!
//!   h_i(x) = min_{tau in [0,T]} c(Phi_i(tau, x))  if escape i reaches its
//!            terminal set, else -inf;      h(x) = max_i h_i(x).
//!
//! Escapes are Auto-GCAS-style: full power, climb angle scheduled on airspeed
//! (a speed-hold through pitch, so a slow aircraft trades less energy), bank
//! limited so the load factor stays below the stall limit. Each escape fixes
//! a path over the ground when it begins (`EscRef`): a straight climb line
//! for 0, 3, 6, 10 or 15 s along the nearest street direction (if within
//! 25 deg of the current track), then an orbit left or right around a fixed
//! ground point. It follows that path with a crab angle into the measured
//! wind, so a gust causes a small, bounded wobble instead of a drift that
//! grows with time.
//! The terminal set is that orbit, once the predicted flight has stayed
//! settled on it for `T_SETTLE` (radius, course, bank, roll rate, speed and
//! climb all steady) while climbing faster than the worst downdraft: from
//! then on it stays within a small band around the same ground circle at
//! ever greater height, so if the whole circle is clear at the current
//! height it stays clear forever. (No full 360 deg needs to be flown: the
//! circle is fixed and is checked in full.)

use crate::model::*;
use crate::world::{hc_at, swept_clear, World, CELL, LAT_CELLS, R_BODY, ROBUST_CELLS};
use std::f64::consts::PI;

/// Wings-level pull-up durations; each escape is (pull-up, turn direction).
pub const PULLUPS: [f64; 5] = [0.0, 3.0, 6.0, 10.0, 15.0];
pub const N_ESC: usize = 2 * PULLUPS.len();
pub const ESC_NAMES: [&str; N_ESC] = [
    "turn L",
    "turn R",
    "climb 3s, L",
    "climb 3s, R",
    "climb 6s, L",
    "climb 6s, R",
    "climb 10s, L",
    "climb 10s, R",
    "climb 15s, L",
    "climb 15s, R",
];
/// Default evaluation order (the filter promotes whichever escape won last).
pub const ESC_ORDER: [usize; N_ESC] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

pub const PHI_ESC: f64 = 45.0 * PI / 180.0;
pub const V_T: f64 = 35.0;
pub const K_V: f64 = 0.15;
pub const K_G: f64 = 1.2;
pub const K_PHI: f64 = 2.5;
pub const G_LO: f64 = -10.0 * PI / 180.0;
pub const G_HI: f64 = 25.0 * PI / 180.0;
pub const N_ESC_MAX: f64 = 3.5;
/// Climb line: snap window to a street axis, bank cap while on the line.
pub const SNAP_WINDOW: f64 = 25.0 * PI / 180.0;
pub const PHI_PU_MAX: f64 = 25.0 * PI / 180.0;
/// Path following: bank per heading error, and the cross-track distance
/// over which the course correction reaches 45 deg.
pub const K_HDG: f64 = 4.0;
pub const L1: f64 = 100.0;
/// Orbit radius is sized so the fastest ground-speed leg needs this bank,
/// leaving headroom up to `PHI_ESC` for corrections.
pub const PHI_ORB: f64 = 40.0 * PI / 180.0;
/// Time for path following to cancel a gust: lateral error <= gust * T_TRACK.
pub const T_TRACK: f64 = 1.5;
/// Settled on the orbit: radial, course and bank error, and roll rate,
/// below these, continuously for `T_SETTLE` seconds of predicted flight.
pub const ORBIT_TOL: f64 = 2.0;
pub const ORBIT_CHI_TOL: f64 = 0.05;
pub const ORBIT_PHI_TOL: f64 = 0.08;
pub const ORBIT_P_TOL: f64 = 0.15;
pub const T_SETTLE: f64 = 3.0;
/// Lateral band around the orbit circle covered by the terminal check.
pub const ORBIT_BAND: f64 = 2.0;
/// Time allowed to reach the terminal helix, counted after the pull-up.
pub const HORIZON: f64 = 40.0;
pub const DTP: f64 = 0.1;

/// Phase 3 (model error): growth of the required clearance along the
/// prediction.
pub const ROBUST_W_GUST: f64 = 1.0; // m/s lateral
pub const ROBUST_VZ: f64 = 0.25; // m/s vertical

#[inline]
pub fn esc_pullup(i: usize) -> f64 {
    PULLUPS[i / 2]
}

fn wrap_pi(a: f64) -> f64 {
    (a + PI).rem_euclid(2.0 * PI) - PI
}

/// Climb-line course for an escape that began on ground track `chi0`: the
/// nearest street direction if within `SNAP_WINDOW`, else `chi0` itself.
/// `axis` is the local street-grid orientation (`None`: no streets here).
#[inline]
pub fn line_course(chi0: f64, axis: Option<f64>) -> f64 {
    let Some(a) = axis else { return chi0 };
    let snap = a + ((chi0 - a) / (PI / 2.0)).round() * (PI / 2.0);
    if wrap_pi(chi0 - snap).abs() <= SNAP_WINDOW {
        snap
    } else {
        chi0
    }
}

#[inline]
fn ground_vel(s: &State, w: &[f64; 3]) -> (f64, f64) {
    let vh = s[V].max(5.0) * s[GAM].cos();
    (vh * s[PSI].cos() + w[0], vh * s[PSI].sin() + w[1])
}

/// Orbit radius for a known mean wind and gust envelope.
#[inline]
pub fn orbit_radius(w: &[f64; 3], gust: f64) -> f64 {
    let vg = V_T + (w[0] * w[0] + w[1] * w[1]).sqrt() + gust;
    vg * vg / (G * PHI_ORB.tan())
}

/// An escape's ground path, fixed when it begins. The filter stores the
/// path it verified in the plan, and the aircraft flies exactly that one.
#[derive(Clone, Copy, Debug)]
pub struct EscRef {
    /// Climb line: origin and course.
    pub x0: f64,
    pub y0: f64,
    pub chi: f64,
    /// Orbit centre and radius.
    pub cx: f64,
    pub cy: f64,
    pub r: f64,
}

impl EscRef {
    /// `w` is the filter's mean-wind estimate, `gust` its gust envelope,
    /// `axis` the local street-grid orientation.
    pub fn new(s: &State, i: usize, w: &[f64; 3], gust: f64, axis: Option<f64>) -> EscRef {
        let (gx, gy) = ground_vel(s, w);
        let chi0 = gy.atan2(gx);
        let t_pu = esc_pullup(i);
        let chi = if t_pu > 0.0 { line_course(chi0, axis) } else { chi0 };
        let r = orbit_radius(w, gust);
        // Expected end of the climb line, then the orbit to the turn side.
        let (sc, cc) = chi.sin_cos();
        let along = 0.5 * (s[V] + V_T) + w[0] * cc + w[1] * sc;
        let d = along.max(10.0) * t_pu;
        let (ex, ey) = (s[X] + d * cc, s[Y] + d * sc);
        let dir = esc_dir(i);
        EscRef { x0: s[X], y0: s[Y], chi, cx: ex - dir * r * sc, cy: ey + dir * r * cc, r }
    }
}

#[inline]
pub fn esc_dir(i: usize) -> f64 {
    if i % 2 == 0 {
        1.0
    } else {
        -1.0
    }
}

pub struct LawOut {
    pub cmd: Cmd,
    pub phi_t: f64,
    pub gam_c: f64,
    /// Ground-track error (desired minus actual course).
    pub chi_err: f64,
}

/// Escape `i` evaluated at state `s`, `t_esc` seconds after it started on
/// path `e`. `w` is the wind used to measure the ground track: the measured
/// wind on the aircraft, the mean-wind estimate inside the predictor.
#[inline]
pub fn esc_law(p: &Params, s: &State, i: usize, t_esc: f64, e: &EscRef, w: &[f64; 3]) -> LawOut {
    let v = s[V].max(5.0);
    let nl = n_lift(p, v);
    let n_safe = N_ESC_MAX.min(0.85 * nl);
    let cg = s[GAM].cos();
    let phi_lim = if n_safe <= cg { 0.0 } else { (cg / n_safe).acos() };
    let (gx, gy) = ground_vel(s, w);
    let vg = (gx * gx + gy * gy).sqrt().max(1.0);
    let (chi_d, phi_ff, cap) = if t_esc < esc_pullup(i) {
        // Follow the climb line.
        let ct = -(s[X] - e.x0) * e.chi.sin() + (s[Y] - e.y0) * e.chi.cos();
        (e.chi - (ct / L1).atan(), 0.0, PHI_PU_MAX.min(phi_lim))
    } else {
        // Follow the orbit.
        let (dx, dy) = (s[X] - e.cx, s[Y] - e.cy);
        let rr = (dx * dx + dy * dy).sqrt();
        let dir = esc_dir(i);
        let chi_d = dy.atan2(dx) + dir * (0.5 * PI + ((rr - e.r) / L1).atan());
        (chi_d, dir * (vg * vg / (G * e.r)).atan(), PHI_ESC.min(phi_lim))
    };
    // Crab: the air heading whose ground track is chi_d.
    let vh = v * cg;
    let wperp = -w[0] * chi_d.sin() + w[1] * chi_d.cos();
    let psi_d = chi_d - (wperp / vh).clamp(-0.6, 0.6).asin();
    let phi_t = (phi_ff + K_HDG * wrap_pi(psi_d - s[PSI])).clamp(-cap, cap);
    let chi_err = wrap_pi(chi_d - gy.atan2(gx));
    let (t, d) = thrust_drag(p, v, n_act(p, s), s[THR]);
    let sin_gc = ((t - d) / p.m + K_V * (v - V_T)) / G;
    let gam_c = sin_gc.clamp(-1.0, 1.0).asin().clamp(G_LO, G_HI);
    let nc = (cg + v / G * K_G * (gam_c - s[GAM])) / s[PHI].cos().max(0.3);
    let nc = nc.clamp(0.0, N_ESC_MAX.min(0.92 * nl));
    let pc = (K_PHI * (phi_t - s[PHI])).clamp(-p.p_max, p.p_max);
    LawOut { cmd: [nc, pc, 1.0], phi_t, gam_c, chi_err }
}

#[derive(Clone, Copy, Debug)]
pub struct Roll {
    pub valid: bool,
    pub pruned: bool,
    pub h: f64,
    pub t_end: f64,
    /// The escape's ground path, if the rollout got that far.
    pub eref: Option<EscRef>,
}

/// The filter's internal model of the world and aircraft.
pub struct Pred<'a> {
    pub world: &'a World,
    pub prm: Params,
    pub wind: [f64; 3],
    pub robust: bool,
    /// true: swept cell check over the whole path (safety decisions).
    /// false: bilinear point samples (smooth, for Phase 2 derivatives).
    pub swept: bool,
    /// true: the wider acceptance map (new plans); false: re-check map.
    pub accept: bool,
    /// Gust envelope: max horizontal / vertical deviation of the wind from
    /// `wind` (m/s). Zero in calm air.
    pub gust: f64,
    pub gust_z: f64,
}

/// Margin a new plan needs on top of the acceptance checks; slack against
/// re-checks from shifted starting points.
pub const EPS_ACC: f64 = 0.5;
/// Buildings: required gap between the aircraft sphere and any box, for
/// re-checks, plus extra for accepting new plans.
pub const M_BLD: f64 = 1.0;
pub const ACC_BLD: f64 = 0.5;
/// Boxes farther than this beyond the required distance are ignored.
const BLD_QUERY_EXTRA: f64 = 10.0;

impl<'a> Pred<'a> {
    /// Street-grid orientation at (x, y): the procedural city's streets run
    /// along x and y everywhere.
    #[inline]
    pub fn street_axis(&self, _x: f64, _y: f64) -> Option<f64> {
        Some(0.0)
    }

    /// A new escape's ground path from state `s`.
    #[inline]
    pub fn esc_ref(&self, s: &State, i: usize) -> EscRef {
        EscRef::new(s, i, &self.wind, self.gust, self.street_axis(s[X], s[Y]))
    }

    #[inline]
    fn map_for(&self, tau: f64) -> (&[f32], f64) {
        let base = if self.accept { &self.world.hc_acc } else { &self.world.hc };
        if !self.robust {
            return (base, 0.0);
        }
        let need = LAT_CELLS as f64 * CELL + ROBUST_W_GUST * tau;
        let maps = self.world.robust_maps(self.accept);
        let mut idx = None;
        if need > LAT_CELLS as f64 * CELL {
            for (k, &r) in ROBUST_CELLS.iter().enumerate() {
                idx = Some(k);
                if r as f64 * CELL >= need {
                    break;
                }
            }
        }
        let vz = ROBUST_VZ * tau;
        match idx {
            None => (base, vz),
            Some(k) => (&maps[k], vz),
        }
    }

    /// Clearance `c = z - Hc(x,y)` of a predicted point `tau` s ahead.
    #[inline]
    pub fn clear(&self, x: f64, y: f64, z: f64, tau: f64) -> f64 {
        self.seg(x, y, z, x, y, z, tau, 0.0, 0.0)
    }

    /// Clearance of the straight 3D segment: terrain via the map, buildings
    /// via exact distance to their boxes. Gusts: the path is checked lowered
    /// by the worst downdraft so far, with a lateral margin for the tracking
    /// error plus the drift while the pilot's (uncorrected) command was held
    /// (`drift` seconds). `band`: extra lateral margin.
    #[inline]
    #[allow(clippy::too_many_arguments)]
    fn seg(&self, x0: f64, y0: f64, z0: f64, x1: f64, y1: f64, z1: f64, tau: f64, drift: f64, band: f64) -> f64 {
        let (m, mut extra) = self.map_for(tau);
        let low = self.gust_z * tau;
        let (z0, z1) = (z0 - low, z1 - low);
        // New plans pay the tracking error twice: once for themselves and once
        // for what a gust can already have done by the time they're re-checked.
        let track = if self.accept { 2.0 * T_TRACK } else { T_TRACK };
        let mw = self.gust * (track + drift) + band;
        extra += mw;
        let ct = if self.swept {
            swept_clear(m, x0, y0, z0, x1, y1, z1) - extra
        } else {
            z0.min(z1) - hc_at(m, x1, y1).max(hc_at(m, 0.5 * (x0 + x1), 0.5 * (y0 + y1))) - extra
        };
        let mut mb = M_BLD + mw;
        if self.accept {
            mb += ACC_BLD;
        }
        if self.robust {
            mb += ROBUST_W_GUST * tau;
        }
        let need = R_BODY + mb;
        let db = self.world.seg_building_dist([x0, y0, z0], [x1, y1, z1], need + BLD_QUERY_EXTRA);
        ct.min(db - need)
    }

    #[inline]
    fn seg_clear(&self, a: &State, b: &State, tau: f64, drift: f64) -> f64 {
        self.seg(a[X], a[Y], a[Z], b[X], b[Y], b[Z], tau, drift, 0.0)
    }

    /// Is the aircraft settled on the orbit right now?
    fn settled(&self, s: &State, i: usize, e: &EscRef) -> bool {
        let (dx, dy) = (s[X] - e.cx, s[Y] - e.cy);
        let rr = (dx * dx + dy * dy).sqrt();
        if (rr - e.r).abs() > ORBIT_TOL || (s[V] - V_T).abs() > 1.5 || s[P].abs() > ORBIT_P_TOL {
            return false;
        }
        let law = esc_law(&self.prm, s, i, 1e9, e, &self.wind);
        let climb = s[V] * s[GAM].sin();
        law.chi_err.abs() <= ORBIT_CHI_TOL
            && (s[PHI] - law.phi_t).abs() <= ORBIT_PHI_TOL
            && climb >= self.gust_z + 0.5
            && (s[GAM] - law.gam_c).abs() <= 0.02
    }

    /// Clearance of the fixed ground circle (plus a band) at the current
    /// height, which only grows; `None` if any part of it is blocked.
    fn circle_clear(&self, s: &State, e: &EscRef, tau: f64, drift: f64) -> Option<f64> {
        let (dx, dy) = (s[X] - e.cx, s[Y] - e.cy);
        let mut minc = f64::INFINITY;
        let n = 60;
        let th0 = dy.atan2(dx);
        let (mut qx, mut qy) = (e.cx + e.r * th0.cos(), e.cy + e.r * th0.sin());
        for k in 1..=n {
            let th = th0 + 2.0 * PI * k as f64 / n as f64;
            let (px, py) = (e.cx + e.r * th.cos(), e.cy + e.r * th.sin());
            let c = self.seg(qx, qy, s[Z], px, py, s[Z], tau, drift, ORBIT_BAND);
            if c < 0.0 {
                return None;
            }
            minc = minc.min(c);
            (qx, qy) = (px, py);
        }
        Some(minc)
    }

    /// Simulate: hold `hold.0` for `hold.1` s, then escape `i` (already
    /// `t_esc0` s in on path `eref`, or starting now if `None`). Stops on a
    /// hit, when the running minimum drops below `cutoff`, at the terminal
    /// set, or at the horizon.
    pub fn rollout(
        &self,
        s0: &State,
        hold: Option<(Cmd, f64)>,
        i: usize,
        t_esc0: f64,
        eref: Option<EscRef>,
        cutoff: f64,
        mut path: Option<&mut Vec<[f32; 3]>>,
    ) -> Roll {
        let mut s = *s0;
        let mut tau = 0.0;
        let mut minc = self.clear(s[X], s[Y], s[Z], 0.0);
        let push = |p: &mut Option<&mut Vec<[f32; 3]>>, s: &State| {
            if let Some(v) = p.as_deref_mut() {
                v.push([s[X] as f32, s[Y] as f32, s[Z] as f32]);
            }
        };
        push(&mut path, &s);
        let fail = |minc: f64, tau: f64, pruned: bool| Roll { valid: false, pruned, h: minc, t_end: tau, eref: None };
        if minc < 0.0 {
            return fail(minc, 0.0, false);
        }
        let hold_dur = hold.map_or(0.0, |h| h.1);
        if let Some((u, dur)) = hold {
            let mut t = 0.0;
            while t < dur - 1e-9 {
                let dt = DTP.min(dur - t);
                let prev = s;
                rk4(&self.prm, &mut s, dt, &self.wind, |_, _| u);
                t += dt;
                tau += dt;
                minc = minc.min(self.seg_clear(&prev, &s, tau, tau.min(hold_dur)));
                push(&mut path, &s);
                if minc < 0.0 {
                    return fail(minc, tau, false);
                }
                if minc < cutoff {
                    return fail(minc, tau, true);
                }
            }
        }
        let mut te = t_esc0;
        let e = eref.unwrap_or_else(|| self.esc_ref(&s, i));
        let t_pu = esc_pullup(i);
        let mut settled_at: Option<f64> = None;
        loop {
            if te >= t_pu && self.settled(&s, i, &e) {
                let t0 = *settled_at.get_or_insert(te);
                if te - t0 >= T_SETTLE - 1e-9 {
                    if let Some(cc) = self.circle_clear(&s, &e, tau, hold_dur) {
                        return Roll { valid: true, pruned: false, h: minc.min(cc), t_end: tau, eref: Some(e) };
                    }
                }
            } else {
                settled_at = None;
            }
            if te >= t_pu + HORIZON - 1e-9 {
                return fail(minc, tau, false);
            }
            let mut dt = DTP;
            if te < t_pu && te + dt > t_pu - 1e-9 {
                dt = t_pu - te;
            }
            let prev = s;
            let prm = &self.prm;
            let w = self.wind;
            rk4(prm, &mut s, dt, &w, |st, off| esc_law(prm, st, i, te + off, &e, &w).cmd);
            te += dt;
            tau += dt;
            minc = minc.min(self.seg_clear(&prev, &s, tau, hold_dur));
            push(&mut path, &s);
            if minc < 0.0 {
                return fail(minc, tau, false);
            }
            if minc < cutoff {
                return fail(minc, tau, true);
            }
        }
    }

    /// Best escape after holding `hold` (branch and bound over the four
    /// escapes, in `order`). Stops early once a value >= `enough` is found.
    /// Returns (h, index); h = -inf if no escape is valid.
    pub fn best(&self, s: &State, hold: Option<(Cmd, f64)>, order: &[usize; N_ESC], enough: f64) -> (f64, usize) {
        let (h, i, _) = self.best_ref(s, hold, order, enough);
        (h, i)
    }

    /// As `best`, also returning the verified ground path of the winner.
    pub fn best_ref(&self, s: &State, hold: Option<(Cmd, f64)>, order: &[usize; N_ESC], enough: f64) -> (f64, usize, Option<EscRef>) {
        let mut bh = f64::NEG_INFINITY;
        let mut bi = order[0];
        let mut be = None;
        for &i in order {
            let r = self.rollout(s, hold, i, 0.0, None, bh, None);
            if r.valid && r.h > bh {
                bh = r.h;
                bi = i;
                be = r.eref;
                if bh >= enough {
                    break;
                }
            }
        }
        (bh, bi, be)
    }
}
