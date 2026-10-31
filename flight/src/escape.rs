//! Backup (escape) maneuvers and the forward predictor that turns them into
//! the implicit backup CBF
//!
//!   h_i(x) = min_{tau in [0,T]} c(Phi_i(tau, x))  if escape i reaches its
//!            terminal set, else -inf;      h(x) = max_i h_i(x).
//!
//! Escapes are Auto-GCAS-style: full power, climb angle scheduled on airspeed
//! (a speed-hold through pitch, so a slow aircraft trades less energy), bank
//! up to 45 deg but limited so the load factor stays below the stall limit.
//! The terminal set is a steady climbing helix: after 360 deg of turn with
//! speed, bank and climb settled, the aircraft repeats the same ground circle
//! at ever greater height, so if that circle is clear at the current height
//! it stays clear forever.

use crate::model::*;
use crate::world::{hc_at, swept_clear, World, CELL, LAT_CELLS, ROBUST_CELLS};
use std::f64::consts::PI;

pub const N_ESC: usize = 4;
pub const ESC_NAMES: [&str; N_ESC] = ["climb-turn L", "climb-turn R", "pull-up, turn L", "pull-up, turn R"];

pub const PHI_ESC: f64 = 45.0 * PI / 180.0;
pub const V_T: f64 = 35.0;
pub const K_V: f64 = 0.15;
pub const K_G: f64 = 1.2;
pub const K_PHI: f64 = 2.5;
pub const G_LO: f64 = -10.0 * PI / 180.0;
pub const G_HI: f64 = 25.0 * PI / 180.0;
pub const T_PU: f64 = 6.0;
pub const N_ESC_MAX: f64 = 3.5;
pub const HORIZON: f64 = 40.0;
pub const DTP: f64 = 0.1;

/// Phase 3: growth of the required clearance along the prediction.
pub const ROBUST_W_GUST: f64 = 1.0; // m/s lateral
pub const ROBUST_VZ: f64 = 0.25; // m/s vertical

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
}

/// Escape `i` evaluated at state `s`, `t_esc` seconds after it started.
#[inline]
pub fn esc_law(p: &Params, s: &State, i: usize, t_esc: f64) -> LawOut {
    let v = s[V].max(5.0);
    let nl = n_lift(p, v);
    let pullup = i >= 2 && t_esc < T_PU;
    let n_safe = N_ESC_MAX.min(0.85 * nl);
    let cg = s[GAM].cos();
    let phi_lim = if n_safe <= cg { 0.0 } else { (cg / n_safe).acos() };
    let phi_t = if pullup { 0.0 } else { esc_dir(i) * PHI_ESC.min(phi_lim) };
    let (t, d) = thrust_drag(p, v, n_act(p, s), s[THR]);
    let sin_gc = ((t - d) / p.m + K_V * (v - V_T)) / G;
    let gam_c = sin_gc.clamp(-1.0, 1.0).asin().clamp(G_LO, G_HI);
    let nc = (cg + v / G * K_G * (gam_c - s[GAM])) / s[PHI].cos().max(0.3);
    let nc = nc.clamp(0.0, N_ESC_MAX.min(0.92 * nl));
    let pc = (K_PHI * (phi_t - s[PHI])).clamp(-p.p_max, p.p_max);
    LawOut { cmd: [nc, pc, 1.0], phi_t, gam_c }
}

#[derive(Clone, Copy, Debug)]
pub struct Roll {
    pub valid: bool,
    pub pruned: bool,
    pub h: f64,
    pub t_end: f64,
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
}

/// Margin a new plan needs on top of the acceptance map; slack against
/// re-checks from shifted starting points.
pub const EPS_ACC: f64 = 1.0;

impl<'a> Pred<'a> {
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
        self.seg(x, y, z, x, y, z, tau)
    }

    /// Clearance of the straight 3D segment.
    #[inline]
    fn seg(&self, x0: f64, y0: f64, z0: f64, x1: f64, y1: f64, z1: f64, tau: f64) -> f64 {
        let (m, extra) = self.map_for(tau);
        if self.swept {
            swept_clear(m, x0, y0, z0, x1, y1, z1) - extra
        } else {
            z0.min(z1) - hc_at(m, x1, y1).max(hc_at(m, 0.5 * (x0 + x1), 0.5 * (y0 + y1))) - extra
        }
    }

    #[inline]
    fn seg_clear(&self, a: &State, b: &State, tau: f64) -> f64 {
        self.seg(a[X], a[Y], a[Z], b[X], b[Y], b[Z], tau)
    }

    /// Steady-helix terminal condition, and the clearance of the circle the
    /// helix will repeat (at the current height, which only grows).
    fn terminal(&self, s: &State, i: usize, tau: f64) -> Option<f64> {
        let law = esc_law(&self.prm, s, i, 1e9);
        if (s[V] - V_T).abs() > 1.5
            || (s[PHI] - law.phi_t).abs() > 0.05
            || law.phi_t.abs() < 0.3
            || s[GAM] < 0.017
            || (s[GAM] - law.gam_c).abs() > 0.02
        {
            return None;
        }
        let v = s[V];
        let cg = s[GAM].cos();
        let w = G * n_act(&self.prm, s) * s[PHI].sin() / (v * cg);
        if w.abs() < 0.02 {
            return None;
        }
        let r = v * cg / w.abs();
        let dir = w.signum();
        let (sps, cps) = s[PSI].sin_cos();
        let cx = s[X] - dir * r * sps;
        let cy = s[Y] + dir * r * cps;
        let th0 = (s[Y] - cy).atan2(s[X] - cx);
        let period = 2.0 * PI / w.abs();
        let mut minc = f64::INFINITY;
        let (mut qx, mut qy) = (s[X], s[Y]);
        for k in 1..=36 {
            let t = period * k as f64 / 36.0;
            let th = th0 + dir * w.abs() * t;
            let px = cx + r * th.cos() + self.wind[0] * t;
            let py = cy + r * th.sin() + self.wind[1] * t;
            let c = self.seg(qx, qy, s[Z], px, py, s[Z], tau + t);
            if c < 0.0 {
                return None;
            }
            minc = minc.min(c);
            (qx, qy) = (px, py);
        }
        Some(minc)
    }

    /// Simulate: hold `hold.0` for `hold.1` s, then escape `i` (already
    /// `t_esc0` s in, heading reference `psi0`). Stops on a hit, when the
    /// running minimum drops below `cutoff`, at the terminal set, or at the
    /// horizon.
    pub fn rollout(
        &self,
        s0: &State,
        hold: Option<(Cmd, f64)>,
        i: usize,
        t_esc0: f64,
        psi0: Option<f64>,
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
        let fail = |minc: f64, tau: f64, pruned: bool| Roll { valid: false, pruned, h: minc, t_end: tau };
        if minc < 0.0 {
            return fail(minc, 0.0, false);
        }
        if let Some((u, dur)) = hold {
            let mut t = 0.0;
            while t < dur - 1e-9 {
                let dt = DTP.min(dur - t);
                let prev = s;
                rk4(&self.prm, &mut s, dt, &self.wind, |_, _| u);
                t += dt;
                tau += dt;
                minc = minc.min(self.seg_clear(&prev, &s, tau));
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
        let psi_start = psi0.unwrap_or(s[PSI]);
        let dir = esc_dir(i);
        loop {
            if dir * (s[PSI] - psi_start) >= 2.0 * PI {
                if let Some(cc) = self.terminal(&s, i, tau) {
                    return Roll { valid: true, pruned: false, h: minc.min(cc), t_end: tau };
                }
            }
            if te >= HORIZON - 1e-9 {
                return fail(minc, tau, false);
            }
            let mut dt = DTP;
            if i >= 2 && te < T_PU && te + dt > T_PU - 1e-9 {
                dt = T_PU - te;
            }
            let prev = s;
            let prm = &self.prm;
            rk4(prm, &mut s, dt, &self.wind, |st, off| esc_law(prm, st, i, te + off).cmd);
            te += dt;
            tau += dt;
            minc = minc.min(self.seg_clear(&prev, &s, tau));
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
        let mut bh = f64::NEG_INFINITY;
        let mut bi = order[0];
        for &i in order {
            let r = self.rollout(s, hold, i, 0.0, None, bh, None);
            if r.valid && r.h > bh {
                bh = r.h;
                bi = i;
                if bh >= enough {
                    break;
                }
            }
        }
        (bh, bi)
    }
}
