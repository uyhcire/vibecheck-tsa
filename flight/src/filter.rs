//! Safety filters. Both only ever change the command sent to the aircraft.
//!
//! Phase 1 (blend and commit, after Singletary / Gurriet, with the gatekeeper
//! committed-trajectory fallback): each tick, predict the pilot's command held
//! for a while followed by each escape. The margin is a time margin: if the
//! pilot could keep the command for 1 s and still escape, leave them alone;
//! the shorter that time, the harder it blends toward the best escape. (A
//! distance margin blends all the time in a street canyon, where walls are
//! always close even when escape is easy.) The blended command, held for
//! `T_LOOK`, must itself verify; if it does it becomes the new committed plan,
//! otherwise keep flying the plan committed at the last tick that passed.
//!
//! Phase 2 (closed-form bCBF, after van Wijk et al.): interpolate
//! u = (1-b) u_pilot + b u_backup with the smallest b that satisfies
//! dh/dt >= -alpha h, which is a scalar inequality in b. The same discrete-time
//! verification and committed fallback run underneath as a safety net.
//!
//! Permissive (pure gatekeeper): pass the pilot's command whenever "pilot for
//! one tick, then the best escape" verifies; otherwise fly the committed
//! escape. Maximally permissive, but it intervenes abruptly.

use crate::escape::*;
use crate::model::*;
use std::time::Instant;

pub const T_LOOK: f64 = 0.25;
pub const T_LOOK_STEPS: u64 = 25;
/// Time-margin blending: (pilot hold time, blend amount if that hold still
/// verifies), tried in order. If none verifies, blend fully.
pub const T_MARGIN: [(f64, f64); 3] = [(1.0, 0.0), (0.4, 0.35), (0.1, 0.7)];
pub const T_FREE_STEPS: u64 = 100;
/// Permissive mode stops searching once an escape keeps this much clearance.
pub const PERM_ENOUGH: f64 = 20.0;
pub const LAM_DECAY: f64 = 1.0;
pub const ALPHA: f64 = 1.0;
pub const P2_DELTA: f64 = 0.1;
/// Phase 2 keeps h above this floor, so the discrete check rarely has to step in.
pub const P2_HMIN: f64 = 12.0;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    P1,
    P2,
    Permissive,
}

impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Phase::P1 => "P1 blend + commit",
            Phase::P2 => "P2 closed-form",
            Phase::Permissive => "permissive",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FilterCfg {
    pub phase: Phase,
    pub robust: bool,
}

/// Committed plan: hold `hold` until physics step `hold_end`, then fly
/// escape `esc`; `psi0` is the heading when the escape began.
#[derive(Clone, Copy, Debug)]
pub struct Plan {
    pub hold: Cmd,
    pub hold_end: u64,
    pub esc: usize,
    pub psi0: Option<f64>,
}

impl Plan {
    /// Command this plan applies at step `k` (and records `psi0`).
    pub fn begin_step(&mut self, k: u64, s: &State) {
        if k >= self.hold_end && self.psi0.is_none() {
            self.psi0 = Some(s[PSI]);
        }
    }
    pub fn tail(&self, k: u64) -> (Option<(Cmd, f64)>, f64) {
        if k < self.hold_end {
            (Some((self.hold, (self.hold_end - k) as f64 * DT)), 0.0)
        } else {
            (None, (k - self.hold_end) as f64 * DT)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Off,
    Free,
    Blend,
    Commit,
}

#[derive(Clone, Copy, Debug)]
pub enum CmdSrc {
    Const(Cmd),
    FollowPlan,
}

pub struct FilterState {
    pub cfg: FilterCfg,
    pub plan: Option<Plan>,
    pub lam: f64,
    pub mode: Mode,
    /// Barrier value shown on the HUD (best escape clearance, m).
    pub h: f64,
    pub act_esc: Option<usize>,
    pub ms: f64,
    pub inv_ok: bool,
    pub tail_ok: bool,
    /// A fresh escape from the current state verified this tick.
    fresh_ok: bool,
    /// Diagnostics: last re-check of the committed plan's tail.
    pub last_tail: Option<Roll>,
    order: [usize; N_ESC],
}

impl FilterState {
    pub fn new(cfg: FilterCfg) -> Self {
        FilterState {
            cfg,
            plan: None,
            lam: 0.0,
            mode: Mode::Free,
            h: 0.0,
            act_esc: None,
            ms: 0.0,
            inv_ok: true,
            tail_ok: true,
            fresh_ok: false,
            last_tail: None,
            order: ESC_ORDER,
        }
    }

    fn promote(&mut self, i: usize) {
        if let Some(pos) = self.order.iter().position(|&x| x == i) {
            self.order[..=pos].rotate_right(1);
        }
    }

    /// Initialise the committed plan from a state inside the safe set.
    pub fn init(&mut self, pred: &Pred, s: &State, k: u64) -> bool {
        let (h, i) = pred.best(s, None, &self.order, f64::INFINITY);
        self.h = h;
        if h >= 0.0 {
            self.plan = Some(Plan { hold: [1.0, 0.0, 1.0], hold_end: k, esc: i, psi0: None });
            true
        } else {
            false
        }
    }

    pub fn tick(&mut self, pred: &Pred, s: &State, k: u64, u_p: Cmd) -> CmdSrc {
        let t0 = Instant::now();
        // Re-check the committed plan against the (narrower) check map.
        let chk = Pred { accept: false, ..*pred };
        self.last_tail = self.plan.map(|pl| {
            let (hold, te) = pl.tail(k);
            chk.rollout(s, hold, pl.esc, te, pl.psi0, f64::NEG_INFINITY, None)
        });
        self.tail_ok = self.last_tail.map_or(false, |r| r.valid);
        self.fresh_ok = false;
        let (src, verified) = match self.cfg.phase {
            Phase::P1 => self.tick_p1(pred, s, k, u_p),
            Phase::P2 => self.tick_p2(pred, s, k, u_p),
            Phase::Permissive => self.tick_perm(pred, s, k, u_p),
        };
        // Invariant: some verified escape exists from the current state.
        self.inv_ok = verified || self.tail_ok || self.fresh_ok;
        if let CmdSrc::FollowPlan = src {
            self.mode = Mode::Commit;
            self.lam = 1.0;
            self.act_esc = self.plan.map(|p| p.esc);
        }
        self.ms = t0.elapsed().as_secs_f64() * 1e3;
        src
    }

    fn commit(&mut self) -> (CmdSrc, bool) {
        (CmdSrc::FollowPlan, false)
    }

    fn tick_p1(&mut self, pred: &Pred, s: &State, k: u64, u_p: Cmd) -> (CmdSrc, bool) {
        // How long could the pilot keep this command and still escape?
        let mut lam_t = 1.0;
        let (mut h_a, mut i_a) = (f64::NEG_INFINITY, self.order[0]);
        for (n, &(hold, lam_v)) in T_MARGIN.iter().enumerate() {
            let (h, i) = pred.best(s, Some((u_p, hold)), &self.order, PERM_ENOUGH);
            if h >= EPS_ACC {
                lam_t = lam_v;
                if n == 0 {
                    (h_a, i_a) = (h, i);
                }
                break;
            }
            if n == 0 {
                i_a = i;
            }
        }
        let lam = lam_t.max(self.lam - LAM_DECAY * DT_F).clamp(0.0, 1.0);
        if lam <= 1e-3 && h_a >= EPS_ACC {
            self.plan = Some(Plan { hold: u_p, hold_end: k + T_FREE_STEPS, esc: i_a, psi0: None });
            self.promote(i_a);
            self.lam = 0.0;
            self.mode = Mode::Free;
            self.h = h_a;
            self.act_esc = None;
            return (CmdSrc::Const(u_p), true);
        }
        let (h_n, i_n) = pred.best(s, None, &self.order, f64::INFINITY);
        let i_b = if h_n > f64::NEG_INFINITY { i_n } else { i_a };
        let u_b = esc_law(&pred.prm, s, i_b, 0.0, s[PSI]).cmd;
        let u_l = lerp_cmd(&u_p, &u_b, lam);
        let (h_l, i_l) = pred.best(s, Some((u_l, T_LOOK)), &self.order, f64::INFINITY);
        self.h = h_n;
        self.fresh_ok = h_n >= 0.0;
        if h_l >= EPS_ACC {
            self.plan = Some(Plan { hold: u_l, hold_end: k + T_LOOK_STEPS, esc: i_l, psi0: None });
            self.promote(i_l);
            self.lam = lam;
            self.mode = Mode::Blend;
            self.act_esc = Some(i_b);
            (CmdSrc::Const(u_l), true)
        } else {
            self.commit()
        }
    }

    fn tick_perm(&mut self, pred: &Pred, s: &State, k: u64, u_p: Cmd) -> (CmdSrc, bool) {
        let (h, i) = pred.best(s, Some((u_p, DT_F)), &self.order, PERM_ENOUGH);
        self.h = h;
        if h >= EPS_ACC {
            self.plan = Some(Plan { hold: u_p, hold_end: k + STEPS_PER_TICK, esc: i, psi0: None });
            self.promote(i);
            self.lam = 0.0;
            self.mode = Mode::Free;
            self.act_esc = None;
            (CmdSrc::Const(u_p), true)
        } else {
            self.commit()
        }
    }

    fn tick_p2(&mut self, pred: &Pred, s: &State, k: u64, u_p: Cmd) -> (CmdSrc, bool) {
        let (h0, i0) = pred.best(s, None, &self.order, f64::INFINITY);
        self.h = h0;
        self.fresh_ok = h0 >= 0.0;
        if h0 == f64::NEG_INFINITY {
            return self.commit();
        }
        let u_b = esc_law(&pred.prm, s, i0, 0.0, s[PSI]).cmd;
        // The closed form works on a smooth (bilinear) version of h_i0.
        let sm = Pred { swept: false, accept: false, ..*pred };
        let hs = sm.rollout(s, None, i0, 0.0, None, f64::NEG_INFINITY, None);
        let hdot = |u: &Cmd| -> f64 {
            let mut s1 = *s;
            rk4(&sm.prm, &mut s1, P2_DELTA, &sm.wind, |_, _| *u);
            let r = sm.rollout(&s1, None, i0, 0.0, None, f64::NEG_INFINITY, None);
            if r.valid {
                (r.h - hs.h) / P2_DELTA
            } else {
                -1e6
            }
        };
        let hd_p = if hs.valid { hdot(&u_p) } else { -1e6 };
        let a = hd_p + ALPHA * (h0 - P2_HMIN);
        let beta = if a >= 0.0 {
            0.0
        } else {
            let b = hdot(&u_b) - hd_p;
            if b > 1e-9 {
                (-a / b).min(1.0)
            } else {
                1.0
            }
        };
        let u = lerp_cmd(&u_p, &u_b, beta);
        let (h_v, i_v) = pred.best(s, Some((u, DT_F)), &self.order, f64::INFINITY);
        if h_v >= EPS_ACC {
            self.plan = Some(Plan { hold: u, hold_end: k + STEPS_PER_TICK, esc: i_v, psi0: None });
            self.promote(i_v);
            self.lam = beta;
            self.mode = if beta > 1e-3 { Mode::Blend } else { Mode::Free };
            self.act_esc = if beta > 1e-3 { Some(i0) } else { None };
            (CmdSrc::Const(u), true)
        } else {
            self.commit()
        }
    }
}
