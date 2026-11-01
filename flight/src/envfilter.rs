//! Exact-rollout safety filters on the JSBSim plant.
//!
//! Every check forks the JSBSim aircraft and flies an escape law on the copy, frame by frame, so the
//! prediction is the plant itself (bit-exact: the committed aircraft flies the same frames). Escapes: a
//! straight climb-out, climbing turns left and right at 30° and 40° bank, and a street-following climb that
//! captures the nearest street axis, then turns into a 40° helix once one fits. A rollout verifies when the
//! airframe (body sphere and wing, `World::airframe_clearance`) keeps `MARGIN` of true clearance at every
//! path sample until it reaches a terminal set, checked numerically on the settled rollout:
//! - straight: a climbing ray (with a widening corridor) above everything on the map, or off the map;
//! - turns: a steady climbing helix whose ground circle (with margin for radius and centre drift) is clear
//!   at the current height, so climbing around it from here on never meets anything.
//!
//! `--env gate` schedules the checks gatekeeper-style (see `Gate`): either sequentially under a per-tick
//! frame budget, or (`CHECK_THREADS` ≥ 1) every escape to its full horizon, in parallel (`verify_first`).

use crate::jsb::*;
use crate::model::*;
use crate::world::{World, CELL, R_BODY};
use std::f64::consts::{FRAC_PI_2, PI};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};

pub static ENV_FILTER: AtomicU8 = AtomicU8::new(0);

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind {
    Exact,
    Fitted { margin: f64 },
    Gate,
}

pub fn kind() -> Option<Kind> {
    match ENV_FILTER.load(Ordering::Relaxed) {
        1 => Some(Kind::Exact),
        2 => Some(Kind::Fitted { margin: 0.0 }),
        3 => Some(Kind::Fitted { margin: 0.25 }),
        4 => Some(Kind::Gate),
        _ => None,
    }
}

pub fn parse(name: &str) -> u8 {
    match name {
        "exact" => 1,
        "fitted" => 2,
        "fitted25" => 3,
        "gate" => 4,
        _ => 0,
    }
}


/// An escape: turn direction in JSBSim's convention (+1 = bank right) and bank (rad).
#[derive(Clone, Copy, Debug)]
pub struct Esc {
    pub name: &'static str,
    pub dir: f64,
    pub bank: f64,
}

pub const N_ESC: usize = 6;
pub const ESCAPES: [Esc; N_ESC] = [
    Esc { name: "straight", dir: 0.0, bank: 0.0 },
    Esc { name: "left", dir: -1.0, bank: 0.52 },
    Esc { name: "right", dir: 1.0, bank: 0.52 },
    Esc { name: "left40", dir: -1.0, bank: 0.7 },
    Esc { name: "right40", dir: 1.0, bank: 0.7 },
    Esc { name: "street", dir: 0.0, bank: 0.7 },
];
pub const STREET: usize = 5;
/// The street escape applies when the track is within this of a street axis (rad).
pub const STREET_CAPTURE: f64 = 25.0 * PI / 180.0;
/// Street escape heading capture: bank per radian of heading error, and its bank limit (rad).
const K_STREET: f64 = 2.0;
const BANK_STREET: f64 = 0.35;
/// Margin (m) the street escape's predicted helix annulus must clear before it rolls in.
const M_TRIGGER: f64 = 10.0;
/// Street escape roll loop (bank, rate, integral gains): settles its helix bank within 2° about 3 s after
/// roll-in, where the shared gains overshoot by 6-13°.
const ROLL_STREET: [f64; 3] = [4.0, 2.5, 3.0];
/// How many of `ESCAPES` the filters use: all 6 by default; `--escapes 5` drops the street escape, `3` also
/// the 40° turns.
pub static N_USED: AtomicU8 = AtomicU8::new(N_ESC as u8);

pub fn n_esc() -> usize {
    N_USED.load(Ordering::Relaxed) as usize
}

/// Escape-law gains: a referee-verified longitudinal law plus an angle-of-attack integral and lateral terms.
#[derive(Clone, Copy, Debug)]
pub struct LawP {
    pub kind: LawKind,
    /// Airspeed reference per escape (m/s): the climb settles near it.
    pub v_ref: [f64; N_ESC],
    pub nmax: f64,
    pub amax: f64,
    pub kv: f64,
    pub gc_lo: f64,
    pub gc_hi: f64,
    pub gc_ref: f64,
    pub kg: f64,
    pub nmin: f64,
    pub a0: f64,
    pub ka0: f64,
    pub ka: f64,
    pub kq: f64,
    pub e0: f64,
    pub e1: f64,
    pub ki_a: f64,
    /// Gains scale by `min(1, (vs/V)²)`; pitch-rate feedforward (elevator per rad/s at 40 m/s).
    pub vs: f64,
    pub kqf: f64,
    /// Lateral: roll PI-D, heading hold (straight), turn coordination.
    pub kphi: f64,
    pub ki_phi: f64,
    pub kp: f64,
    pub kpsi: f64,
    pub kb: f64,
    pub ki_b: f64,
    pub kr: f64,
    /// The turn starts once the climb is established (γ ≥ `gam_turn`) after `t_pull_min` (per escape), or at
    /// `t_pull_max`. With `keep_bank`, a bank already toward the turn (up to its bank) is held through the pull-up.
    pub t_pull_min: [f64; N_ESC],
    pub keep_bank: bool,
    pub t_pull_max: f64,
    pub gam_turn: f64,
}

/// Which longitudinal law: `Ci/cegis/Law.lean` (flight-path loop over n and α caps) at `0093c1a` or `3e7fd42`,
/// or `Ci/lawfirst/Law.lean` with `Sub.lean`'s `p1` (α command with an n cap, PI inner loop).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LawKind {
    Cegis,
    Lawfirst,
}

pub const LAW: LawP = LawP {
    kind: LawKind::Cegis,
    v_ref: [41.0, 37.0, 37.0, 37.0, 37.0, 41.0],
    nmax: 3.3,
    amax: 0.22,
    kv: 0.03,
    gc_lo: 0.0,
    gc_hi: 0.35,
    gc_ref: 0.15,
    kg: 2.5,
    nmin: 0.3,
    a0: -0.058,
    ka0: 205.0,
    ka: 3.0,
    kq: 1.5,
    e0: -0.21,
    e1: 2.49,
    ki_a: 2.0,
    vs: 0.0,
    kqf: 0.0,
    kphi: 2.5,
    ki_phi: 1.0,
    kp: 0.8,
    kpsi: 1.0,
    kb: 2.0,
    ki_b: 2.0,
    kr: 0.5,
    t_pull_min: [1.5; N_ESC],
    keep_bank: false,
    t_pull_max: 6.0,
    gam_turn: 0.03,
};

pub const LAW_CEGIS2: LawP = LawP {
    v_ref: [35.0, 35.0, 35.0, 36.0, 36.0, 35.0],
    keep_bank: true,
    t_pull_min: [1.5, 1.5, 1.5, 0.0, 0.0, 1.5],
    nmax: 3.5, amax: 0.24, kv: 0.02, gc_lo: 0.05, kq: 1.2, vs: 50.0, kqf: 0.6, ..LAW };
pub const LAW_LAWFIRST: LawP = LawP { kind: LawKind::Lawfirst, ..LAW };

/// `lawfirst` `p1`, converted from raw ×2^16 units (`kI` is per 1/16 s tick there, per second here).
mod lf {
    pub const A_REF: f64 = 6500.0 / 65536.0;
    pub const KV: f64 = 1311.0 / 65536.0;
    pub const KG: f64 = 25600.0 / 65536.0;
    pub const GC: f64 = 9830.0 / 65536.0;
    pub const A_MAX: f64 = 15000.0 / 65536.0;
    pub const A_MIN: f64 = -6000.0 / 65536.0;
    pub const N_LIM: f64 = 235929.0 / 65536.0;
    pub const N_LIM_UP: f64 = 183500.0 / 65536.0;
    pub const A0: f64 = -4000.0 / 65536.0;
    pub const KA: f64 = 2.0;
    pub const KQ: f64 = 19661.0 / 65536.0;
    pub const KI: f64 = 16.0 * 6554.0 / 65536.0;
    pub const KF: f64 = 111411.0 / 65536.0;
    pub const E_I0: f64 = -5243.0 / 65536.0;
    pub const G_MAX: f64 = 29491.0 / 65536.0;
    pub const KGL: f64 = 1.0;
}

/// The law the filters fly: `--law cegis1|cegis2|lawfirst`.
pub static LAW_SEL: AtomicU8 = AtomicU8::new(1);

pub fn parse_law(name: &str) -> u8 {
    match name {
        "cegis1" => 0,
        "lawfirst" => 2,
        _ => 1,
    }
}

pub fn law_params() -> LawP {
    match LAW_SEL.load(Ordering::Relaxed) {
        0 => LAW,
        2 => LAW_LAWFIRST,
        _ => LAW_CEGIS2,
    }
}

const G0: f64 = 9.80665;

fn rho_of(h: f64) -> f64 {
    1.225 * (1.0 - 2.2558e-5 * h).max(0.5).powf(4.256)
}

fn wrap(a: f64) -> f64 {
    (a + PI).rem_euclid(2.0 * PI) - PI
}

/// The escape law's state: which escape, time since it began, integrators, and the turn/heading reference
/// captured when the pull-up ends. A fresh law depends only on the escape index, so a check and the commit
/// that follows it fly the same frames.
#[derive(Clone, Copy, Debug)]
pub struct Law {
    pub esc: usize,
    pub t: f64,
    pub ia: f64,
    pub ib: f64,
    pub iphi: f64,
    /// Track (rad, JSBSim convention) held by the straight escape once the pull-up ends; `NAN` before.
    pub psi_ref: f64,
    /// Street escape: the captured street axis (JSBSim track; `NAN` if none within `STREET_CAPTURE`), its
    /// helix direction once one fits (0 while following the street), and the next time it looks for one.
    pub axis: f64,
    pub side: f64,
    next_try: f64,
    captured: bool,
    pub p: LawP,
}

impl Law {
    pub fn new(esc: usize) -> Law {
        Law::with(esc, law_params())
    }

    pub fn with(esc: usize, p: LawP) -> Law {
        let ia = if p.kind == LawKind::Lawfirst { lf::E_I0 } else { 0.0 };
        Law { esc, t: 0.0, ia, ib: 0.0, iphi: 0.0, psi_ref: f64::NAN, axis: f64::NAN, side: 0.0, next_try: 0.0, captured: false, p }
    }

    /// Turn direction of the terminal set this escape is heading for (JSBSim sign; 0 = a straight climb).
    pub fn dir(&self) -> f64 {
        if self.esc == STREET { self.side } else { ESCAPES[self.esc].dir }
    }

    /// Street escape: capture the nearest street axis from the starting track (once, so a check and the
    /// commit that follows it capture the same axis).
    pub fn capture(&mut self, o: &Obs) {
        if self.captured || self.esc != STREET {
            return;
        }
        self.captured = true;
        let track = o.vned[1].atan2(o.vned[0]);
        let a = (track / FRAC_PI_2).round() * FRAC_PI_2;
        if wrap(a - track).abs() <= STREET_CAPTURE {
            self.axis = a;
        }
    }

    /// Street escape, every 0.25 s once the climb is established on the axis: start the helix toward the
    /// first side (left, then right) whose predicted annulus is clear at the current height.
    fn street_turn(&mut self, world: &World, q: &JsbPlant) {
        if self.esc != STREET || self.axis.is_nan() || self.side != 0.0 || !self.turning() || self.t < self.next_try {
            return;
        }
        self.next_try = self.t + 0.25;
        let o = &q.obs;
        if wrap(self.axis - o.vned[1].atan2(o.vned[0])).abs() > 0.05 {
            return;
        }
        let s = q.state();
        let vh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
        let r = vh * vh / (G0 * ESCAPES[STREET].bank.tan());
        let (c, sn) = (s[PSI].cos(), s[PSI].sin());
        for side in [-1.0, 1.0] {
            // Point-mass frame: a left turn (JSBSim -1) circles a centre to the left, (-sin, cos).
            let ctr = [s[X] + vh * c + side * r * sn, s[Y] + vh * sn - side * r * c];
            if helix_clear(world, ctr, r, M_TRIGGER, s[Z], top(world)) {
                self.side = side;
                return;
            }
        }
    }

    /// One frame of the escape. The street escape reads the map to choose where its helix starts.
    pub fn step(&mut self, world: &World, q: &mut JsbPlant) {
        self.capture(&q.obs);
        self.street_turn(world, q);
        self.frame(q);
    }

    pub fn turning(&self) -> bool {
        !self.psi_ref.is_nan()
    }

    /// Surfaces for one frame (JSBSim conventions: elevator positive nose down; aileron positive rolls right;
    /// rudder positive yaws left) and throttle.
    pub fn controls(&mut self, o: &Obs) -> [f64; 4] {
        let gh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
        let v = o.vt.max(10.0);
        let g = (-o.vned[2]).atan2(gh);
        let (sphi, cphi) = o.phi.sin_cos();
        let esc = ESCAPES[self.esc];
        let e = if self.p.kind == LawKind::Lawfirst { self.elev_lawfirst(o, v, g, cphi, self.p.v_ref[self.esc]) } else { self.elev_cegis(o, v, g, cphi, self.p.v_ref[self.esc]) };
        let p = &self.p;
        // Lateral: wings level through the pull-up, then a coordinated climbing turn (or a heading hold).
        let track = o.vned[1].atan2(o.vned[0]);
        if !self.turning() && self.t >= p.t_pull_min[self.esc] && (g >= p.gam_turn || self.t >= p.t_pull_max) {
            self.psi_ref = track;
        }
        let phi_t = if self.esc == STREET {
            if self.side != 0.0 {
                self.side * esc.bank
            } else if self.axis.is_nan() {
                0.0
            } else {
                (K_STREET * wrap(self.axis - track)).clamp(-BANK_STREET, BANK_STREET)
            }
        } else if !self.turning() {
            if p.keep_bank && esc.dir * o.phi > 0.0 { esc.dir * (o.phi.abs().min(esc.bank)) } else { 0.0 }
        } else if esc.dir == 0.0 {
            (p.kpsi * wrap(self.psi_ref - track)).clamp(-0.15, 0.15)
        } else {
            esc.dir * esc.bank
        };
        let ephi = phi_t - o.phi;
        let (kphi, kp) = if self.esc == STREET { (ROLL_STREET[0], ROLL_STREET[1]) } else { (p.kphi, p.kp) };
        let ail_raw = kphi * ephi - kp * o.pqr[0] + self.iphi;
        let ail = ail_raw.clamp(-1.0, 1.0);
        if self.esc == STREET {
            // Integrate near the target only, so a roll-in does not wind it up against the bank it needs.
            if ail == ail_raw && ephi.abs() < 0.1 {
                self.iphi = (self.iphi + ROLL_STREET[2] * ephi * DT_JSB).clamp(-0.45, 0.45);
            }
        } else if ail == ail_raw || ephi * self.iphi < 0.0 {
            self.iphi = (self.iphi + p.ki_phi * ephi * DT_JSB).clamp(-0.3, 0.3);
        }
        // Yaw rate of a coordinated turn at this bank, so the damper only opposes the excess.
        let r_turn = G0 / v * sphi;
        let rud_raw = -p.kb * o.beta + p.kr * (o.pqr[2] - r_turn) + self.ib;
        let rud = rud_raw.clamp(-1.0, 1.0);
        if rud == rud_raw || o.beta * self.ib > 0.0 {
            self.ib = (self.ib - p.ki_b * o.beta * DT_JSB).clamp(-0.5, 0.5);
        }
        [-e, ail, rud, 1.0]
    }

    /// Elevator (+1 nose up) from the cegis law; in a bank the load factor is divided by cos φ.
    fn elev_cegis(&mut self, o: &Obs, v: f64, g: f64, cphi: f64, v_ref: f64) -> f64 {
        let p = &self.p;
        let gc = (p.gc_ref + p.kv * (v - v_ref)).clamp(p.gc_lo, p.gc_hi);
        let n_long = g.cos() + v * p.kg * (gc - g) / G0;
        // Unload while steeply banked or inverted; otherwise pull for the vertical component.
        let ncmd = if cphi < 0.35 { p.nmin } else { (n_long / cphi).clamp(p.nmin, p.nmax) };
        let rv2 = rho_of(o.h) * v * v;
        let acmd = (p.a0 + p.ka0 * ncmd / rv2).min(p.amax);
        let n_ach = (acmd - p.a0) * rv2 / p.ka0;
        let qcmd = G0 * (n_ach - g.cos() * cphi) / v;
        let sc = if p.vs > 0.0 { (p.vs / v).powi(2).min(1.0) } else { 1.0 };
        let ea = acmd - o.alpha;
        let e_raw = p.e0 + p.e1 * acmd + p.kqf * qcmd * 40.0 / v + sc * (p.ka * ea - p.kq * (o.pqr[1] - qcmd)) + self.ia;
        let e = e_raw.clamp(-1.0, 1.0);
        if e == e_raw || ea * self.ia < 0.0 {
            self.ia = (self.ia + p.ki_a * ea * DT_JSB).clamp(-0.4, 0.4);
        }
        e
    }

    /// Elevator (+1 nose up) from the lawfirst law (in tan α); in a bank the α command above zero lift is
    /// divided by cos φ, and the pitch-rate reference uses the banked kinematics.
    fn elev_lawfirst(&mut self, o: &Obs, v: f64, g: f64, cphi: f64, v_c: f64) -> f64 {
        let ta = o.alpha.tan();
        let tg = g.tan();
        let kv = if v < v_c { 0.0 } else { lf::KV };
        let mut raw = lf::A_REF + kv * (v - v_c) + lf::KG * (lf::GC - tg) - lf::KGL * (tg - lf::G_MAX).max(0.0);
        raw = if cphi < 0.35 { 0.0 } else { lf::A0 + (raw - lf::A0) / cphi };
        let n = o.nz;
        let n_lim = if o.vned[2] < 0.0 { lf::N_LIM_UP } else { lf::N_LIM };
        let a_n = if n > 0.3 && ta > lf::A0 { lf::A0 + (ta - lf::A0) * n_lim / n } else { lf::A_MAX };
        let ac = raw.clamp(lf::A_MIN, lf::A_MAX.min(a_n).max(lf::A_MIN));
        let err = ac - ta;
        let q_ref = G0 * (n - g.cos() * cphi) / v;
        let e = self.ia + lf::KF * ac + lf::KA * err - lf::KQ * (o.pqr[1] - q_ref);
        self.ia = (self.ia + lf::KI * err * DT_JSB).clamp(-1.0, 1.0);
        e.clamp(-1.0, 1.0)
    }

    /// One frame without the map: for escapes other than `STREET` (which never turns here).
    pub fn frame(&mut self, q: &mut JsbPlant) {
        let u = self.controls(&q.obs);
        q.frame_raw(u[0], u[1], u[2], u[3]);
        self.t += DT_JSB;
    }
}


/// Longest rollout (s) and the earliest terminal test (s); terminal tests run every `TERM_EVERY` frames.
pub const HORIZON: f64 = 16.0;
pub const T_TERM: f64 = 6.0;
const TERM_EVERY: usize = 64;
/// Path sample spacing (frames) and the clearance required at every sample (m).
pub const SAMPLE: usize = 8;
pub const MARGIN: f64 = 4.0;
/// Climb rate the terminal sets require throughout their settling window (m/s).
pub const VZ_MIN: f64 = 1.0;
/// Settling window for terminal tests (samples): two halves of 2 s each.
const HALF: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Outcome {
    /// Reached a terminal set (or left the map).
    Ok,
    /// Clearance below `MARGIN` at a path sample.
    Hit,
    /// No terminal set by `HORIZON`.
    Horizon,
    /// Out of frame budget before a verdict.
    Budget,
}

#[derive(Clone, Debug)]
pub struct Roll {
    pub esc: usize,
    pub outcome: Outcome,
    pub frames: usize,
    /// Path samples (every `SAMPLE` frames) and the terminal set's continuation, for display.
    pub path: Vec<[f64; 3]>,
    pub tail: Vec<[f64; 3]>,
    pub min_clear: f64,
    /// Time at which the verdict was reached (s).
    pub t: f64,
}

impl Roll {
    pub fn ok(&self) -> bool {
        self.outcome == Outcome::Ok
    }
}

#[derive(Clone, Copy, Debug)]
struct Hist {
    t: f64,
    x: f64,
    y: f64,
    z: f64,
    /// Unwrapped track, counter-clockwise from +x (the point-mass convention).
    psi: f64,
    vh: f64,
    vz: f64,
}

/// Highest raw cell (terrain or roof) on the map (m).
pub fn top(world: &World) -> f64 {
    world.raw_top
}

fn on_map(world: &World, x: f64, y: f64) -> bool {
    x > world.x0 && x < world.x1 && y > world.y0 && y < world.y1
}

/// Fly escape `esc` from `p` for at most `max_frames` frames and check it.
pub fn rollout(world: &World, p: &JsbPlant, esc: usize, max_frames: usize) -> Roll {
    rollout_law(world, p, Law::new(esc), max_frames, None)
}

/// `rollout` with an explicit law, stopping with `Outcome::Budget` at the wall-clock `deadline` if given.
pub fn rollout_law(world: &World, p: &JsbPlant, law: Law, max_frames: usize, deadline: Option<std::time::Instant>) -> Roll {
    rollout_ctl(world, p, law, max_frames, deadline, None)
}

/// `rollout_law` that also stops with `Outcome::Budget` once `cancel = (best, i)` has `best < i`: a candidate
/// earlier in the priority order verified, so this one's verdict no longer matters.
fn rollout_ctl(world: &World, p: &JsbPlant, mut law: Law, max_frames: usize, deadline: Option<std::time::Instant>, cancel: Option<(&AtomicUsize, usize)>) -> Roll {
    let esc = law.esc;
    let mut q = p.fork();
    law.capture(&q.obs);
    let n_max = ((HORIZON / DT_JSB).round() as usize).min(max_frames);
    let mut hist: Vec<Hist> = Vec::with_capacity(n_max / SAMPLE + 2);
    let mut r = Roll { esc, outcome: Outcome::Horizon, frames: 0, path: Vec::with_capacity(n_max / SAMPLE + 2), tail: Vec::new(), min_clear: f64::INFINITY, t: 0.0 };
    if esc == STREET && law.axis.is_nan() {
        return r;
    }
    let mut psi_prev = f64::NAN;
    let mut push = |q: &JsbPlant, t: f64, hist: &mut Vec<Hist>, r: &mut Roll| -> Option<Outcome> {
        let s = q.state();
        r.path.push([s[X], s[Y], s[Z]]);
        if !on_map(world, s[X], s[Y]) {
            return Some(Outcome::Ok);
        }
        let c = world.airframe_clearance(&s, 50.0);
        r.min_clear = r.min_clear.min(c);
        if c <= MARGIN {
            return Some(Outcome::Hit);
        }
        let o = &q.obs;
        let mut psi = o.vned[0].atan2(o.vned[1]);
        if !psi_prev.is_nan() {
            psi = psi_prev + wrap(psi - psi_prev);
        }
        psi_prev = psi;
        hist.push(Hist { t, x: s[X], y: s[Y], z: s[Z], psi, vh: (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt(), vz: -o.vned[2] });
        None
    };
    if let Some(out) = push(&q, 0.0, &mut hist, &mut r) {
        r.outcome = out;
        return r;
    }
    let k_term = (T_TERM / DT_JSB).round() as usize;
    for k in 1..=n_max {
        law.step(world, &mut q);
        r.frames = k;
        let t = k as f64 * DT_JSB;
        r.t = t;
        if k % SAMPLE == 0 {
            if deadline.is_some_and(|d| std::time::Instant::now() >= d) || cancel.is_some_and(|(b, i)| b.load(Ordering::Relaxed) < i) {
                r.outcome = Outcome::Budget;
                return r;
            }
            if let Some(out) = push(&q, t, &mut hist, &mut r) {
                r.outcome = out;
                return r;
            }
            if k >= k_term && k % TERM_EVERY == 0 && law.turning() {
                if let Some(tail) = terminal(world, law.dir(), &hist) {
                    r.tail = tail;
                    r.outcome = Outcome::Ok;
                    return r;
                }
            }
        }
    }
    r.outcome = if n_max < (HORIZON / DT_JSB).round() as usize { Outcome::Budget } else { Outcome::Horizon };
    r
}

struct Seg {
    omega: f64,
    vh: f64,
    vz_min: f64,
    vz_mean: f64,
    end: Hist,
}

fn seg(h: &[Hist]) -> Seg {
    let (a, b) = (h[0], h[h.len() - 1]);
    let n = h.len() as f64;
    Seg {
        omega: (b.psi - a.psi) / (b.t - a.t),
        vh: h.iter().map(|x| x.vh).sum::<f64>() / n,
        vz_min: h.iter().map(|x| x.vz).fold(f64::INFINITY, f64::min),
        vz_mean: h.iter().map(|x| x.vz).sum::<f64>() / n,
        end: b,
    }
}

/// Terminal test on the rollout so far: `Some(continuation points)` if the escape has settled into its
/// terminal set and that set is clear.
fn terminal(world: &World, dir: f64, hist: &[Hist]) -> Option<Vec<[f64; 3]>> {
    if hist.len() < 2 * HALF + 1 {
        return None;
    }
    let n = hist.len();
    let a = seg(&hist[n - 2 * HALF - 1..n - HALF]);
    let b = seg(&hist[n - HALF - 1..]);
    if a.vz_min.min(b.vz_min) < VZ_MIN {
        return None;
    }
    let e = b.end;
    let top = top(world);
    if dir == 0.0 {
        // Straight: settled heading, then a climbing ray at 80% of the slower half's gradient.
        if a.omega.abs().max(b.omega.abs()) > 0.01 {
            return None;
        }
        let grad = 0.8 * (a.vz_mean / a.vh.max(1.0)).min(b.vz_mean / b.vh.max(1.0));
        ray_clear(world, [e.x, e.y, e.z], e.psi, grad, top)
    } else {
        // Turn: radius and centre from each half; both must agree closely.
        let want = -dir; // a right turn (JSBSim +) turns clockwise, i.e. negative omega here
        if a.omega * want <= 0.02 || b.omega * want <= 0.02 {
            return None;
        }
        let circ = |s: &Seg| {
            let rr = s.vh / s.omega;
            (rr.abs(), [s.end.x - rr * s.end.psi.sin(), s.end.y + rr * s.end.psi.cos()])
        };
        let (ra, ca) = circ(&a);
        let (rb, cb) = circ(&b);
        let d_r = (ra - rb).abs();
        let d_c = ((ca[0] - cb[0]).powi(2) + (ca[1] - cb[1]).powi(2)).sqrt();
        if d_r > 0.1 * rb || d_c > 0.1 * rb {
            return None;
        }
        let m = 5.0 + 3.0 * (d_r + d_c);
        if !helix_clear(world, cb, rb, m, e.z, top) {
            return None;
        }
        Some((0..=72).map(|i| {
            let th = i as f64 * PI / 36.0;
            [cb[0] + rb * th.cos(), cb[1] + rb * th.sin(), e.z + b.vz_mean * (i as f64 / 72.0) * 2.0 * PI * rb / b.vh.max(1.0)]
        }).collect())
    }
}

/// Every raw cell within the annulus `r ± (m + R_BODY)` around `c` is at least `R_BODY + MARGIN` below `z`
/// (or `z` is that far above everything on the map).
pub fn helix_clear(world: &World, c: [f64; 2], r: f64, m: f64, z: f64, top: f64) -> bool {
    let floor = z - R_BODY - MARGIN;
    if floor > top {
        return true;
    }
    let (r0, r1) = ((r - m - R_BODY).max(0.0), r + m + R_BODY);
    if !on_map(world, c[0] - r1, c[1] - r1) || !on_map(world, c[0] + r1, c[1] + r1) {
        return false;
    }
    // Cell centres within half a cell diagonal of the annulus.
    let pad = CELL * std::f64::consts::FRAC_1_SQRT_2;
    let (lo2, hi2) = ((r0 - pad).max(0.0).powi(2), (r1 + pad).powi(2));
    let raw = &world.raw;
    let (i0, j0) = raw.cell(c[0] - r1 - pad, c[1] - r1 - pad);
    let (i1, j1) = raw.cell(c[0] + r1 + pad, c[1] + r1 + pad);
    let floor = floor as f32;
    for j in j0..=j1 {
        let dy = raw.y0 + (j as f64 + 0.5) * CELL - c[1];
        let row = &raw.v[j * raw.nx..(j + 1) * raw.nx];
        for i in i0..=i1 {
            if row[i] <= floor {
                continue;
            }
            let dx = raw.x0 + (i as f64 + 0.5) * CELL - c[0];
            let d2 = dx * dx + dy * dy;
            if d2 >= lo2 && d2 <= hi2 {
                return false;
            }
        }
    }
    true
}

/// A climbing ray from `p` along track `psi` (point-mass convention) at gradient `grad`, inside a corridor
/// of half-width `R_BODY + 5 m + 2% of the distance`: every raw cell under the corridor stays `R_BODY +
/// MARGIN` below the ray until the ray is that far above the map's top or leaves the map.
pub fn ray_clear(world: &World, p: [f64; 3], psi: f64, grad: f64, top: f64) -> Option<Vec<[f64; 3]>> {
    if grad < 0.02 {
        return None;
    }
    let (c, s) = (psi.cos(), psi.sin());
    let mut d = 0.0;
    loop {
        let (x, y, z) = (p[0] + d * c, p[1] + d * s, p[2] + d * grad);
        let floor = z - R_BODY - MARGIN;
        if floor > top || !on_map(world, x, y) {
            return Some(vec![p, [x, y, z]]);
        }
        let w = R_BODY + 5.0 + 0.02 * d;
        let mut l = -w;
        while l <= w {
            if world.surface(x - l * s, y + l * c) > floor {
                return None;
            }
            l += 0.5 * CELL;
        }
        d += 0.5 * CELL;
    }
}

/// Fly escape `esc` from `p` for `secs` with no checks: the path (every `SAMPLE` frames) and the end state.
pub fn fly_escape(p: &JsbPlant, esc: usize, secs: f64) -> (Vec<[f64; 3]>, JsbPlant) {
    let mut q = p.fork();
    let mut law = Law::new(esc);
    let n = (secs / DT_JSB).round() as usize;
    let mut path = Vec::with_capacity(n / SAMPLE + 1);
    let s = q.state();
    path.push([s[X], s[Y], s[Z]]);
    for k in 1..=n {
        law.frame(&mut q);
        if k % SAMPLE == 0 {
            let s = q.state();
            path.push([s[X], s[Y], s[Z]]);
        }
    }
    (path, q)
}


/// Escapes flown from typical commit states (settled alpha, no pitch rate, cruise power): the straight
/// escape's profile in the start's track frame, by airspeed and flight-path angle.
pub struct Table {
    v0: f64,
    dv: f64,
    nv: usize,
    g0: f64,
    dg: f64,
    ng: usize,
    prof: Vec<Vec<[f64; 3]>>,
    fin: Vec<[f64; 3]>,
}

impl Table {
    fn build() -> Table {
        let (v0, dv, nv, g0, dg, ng) = (24.0, 2.0, 24, -0.7, 0.05, 21);
        let cells: Vec<(f64, f64)> =
            (0..nv).flat_map(|i| (0..ng).map(move |j| (v0 + i as f64 * dv, g0 + j as f64 * dg))).collect();
        let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
        let out = crate::harness::par_map(
            cells,
            threads,
            |&(v, g)| {
                let s0 = trimmed(0.0, 0.0, 1500.0, v, g, 0.0, 0.6);
                let p = JsbPlant::new(&s0);
                let st = p.state();
                let (path, q) = fly_escape(&p, 0, HORIZON);
                let (c, sn) = (st[PSI].cos(), st[PSI].sin());
                let prof: Vec<[f64; 3]> = path
                    .iter()
                    .map(|q| {
                        let (dx, dy) = (q[0] - st[X], q[1] - st[Y]);
                        [dx * c + dy * sn, dx * sn - dy * c, q[2] - st[Z]]
                    })
                    .collect();
                let e = q.state();
                (prof, [e[V], e[PSI] - st[PSI], -q.obs.vned[2]])
            },
            |_, _| {},
        );
        let (prof, fin) = out.into_iter().unzip();
        Table { v0, dv, nv, g0, dg, ng, prof, fin }
    }

    fn blend<const K: usize>(&self, v: f64, g: f64, f: impl Fn(usize) -> Vec<[f64; K]>) -> Vec<[f64; K]> {
        let fi = ((v - self.v0) / self.dv).clamp(0.0, (self.nv - 1) as f64 - 1e-9);
        let fj = ((g - self.g0) / self.dg).clamp(0.0, (self.ng - 1) as f64 - 1e-9);
        let (i, j) = (fi as usize, fj as usize);
        let (u, w) = (fi - i as f64, fj - j as f64);
        let ix = |a: usize, b: usize| f(a * self.ng + b);
        let (a, b, c, d) = (ix(i, j), ix(i + 1, j), ix(i, j + 1), ix(i + 1, j + 1));
        (0..a.len())
            .map(|k| std::array::from_fn(|m| (1.0 - u) * (1.0 - w) * a[k][m] + u * (1.0 - w) * b[k][m] + (1.0 - u) * w * c[k][m] + u * w * d[k][m]))
            .collect()
    }
}

pub fn table() -> &'static Table {
    static T: OnceLock<Table> = OnceLock::new();
    T.get_or_init(Table::build)
}

/// The fitted straight escape from `s`: its path and the terminal ray check.
pub fn predict_fitted(world: &World, s: &State, margin: f64) -> (Vec<[f64; 3]>, bool) {
    let t = table();
    let prof = t.blend(s[V], s[GAM], |c| t.prof[c].clone());
    let fin = t.blend(s[V], s[GAM], |c| vec![t.fin[c]])[0];
    let (c, sn) = (s[PSI].cos(), s[PSI].sin());
    let path: Vec<[f64; 3]> = prof
        .iter()
        .map(|&[a, r, dz]| [s[X] + a * c + r * sn, s[Y] + a * sn - r * c, s[Z] + if dz < 0.0 { dz * (1.0 + margin) } else { dz }])
        .collect();
    let last = *path.last().unwrap();
    let ok = path.iter().all(|q| !on_map(world, q[0], q[1]) || world.true_clearance(*q) > MARGIN)
        && ray_clear(world, last, s[PSI] + fin[1], 0.8 * fin[2] / fin[0].max(1.0), top(world)).is_some();
    (path, ok)
}

/// One full check (every escape, no budget): the first escape that verifies, and the path to display.
pub fn check(world: &World, kind: Kind, p: &JsbPlant) -> (Option<usize>, Vec<[f64; 3]>) {
    if let Kind::Fitted { margin } = kind {
        let (path, ok) = predict_fitted(world, &p.state(), margin);
        return (if ok { Some(0) } else { None }, path);
    }
    let mut first = Vec::new();
    for esc in 0..n_esc() {
        let r = rollout(world, p, esc, usize::MAX);
        if r.ok() {
            return (Some(esc), r.path);
        }
        if first.is_empty() {
            first = r.path;
        }
    }
    (None, first)
}

/// How `Gate` checks its candidate escapes. 0: one after another under the per-tick frame budget `BUDGET`.
/// N ≥ 1: every candidate gets its full horizon and the first in priority order that verifies wins
/// (`verify_first`), on N threads (this one and N - 1 pool workers). The verdict does not depend on N: it is the
/// one the sequential check reaches with an unlimited budget.
pub static CHECK_THREADS: AtomicUsize = AtomicUsize::new(0);
/// Debug: re-run every rollout a pool worker flew on the calling thread's plant and panic unless the two agree
/// bit for bit (checks that a `Seed` rebuilds the plant exactly).
pub static VERIFY_SEEDS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

type Job = Box<dyn FnOnce() + Send + 'static>;

/// Worker threads for `verify_first`, started on first use with `CHECK_THREADS - 1` of them (at least 1). They
/// live as long as the process, so each sets up Lean's per-thread state once.
fn pool() -> &'static Mutex<std::sync::mpsc::Sender<Job>> {
    static POOL: OnceLock<Mutex<std::sync::mpsc::Sender<Job>>> = OnceLock::new();
    POOL.get_or_init(|| {
        let (tx, rx) = std::sync::mpsc::channel::<Job>();
        let rx = Arc::new(Mutex::new(rx));
        for i in 0..CHECK_THREADS.load(Ordering::Relaxed).saturating_sub(1).max(1) {
            let rx = rx.clone();
            std::thread::Builder::new()
                .name(format!("gate-check-{i}"))
                .spawn(move || loop {
                    let job = rx.lock().unwrap().recv();
                    match job {
                        Ok(job) => job(),
                        Err(_) => return,
                    }
                })
                .expect("spawn a gate check worker");
        }
        Mutex::new(tx)
    })
}

/// Jobs on the pool that may borrow from the caller's stack: dropping the scope waits until every job it
/// spawned has finished (also when the caller unwinds), so the borrows outlive the jobs.
struct Scope<'s> {
    left: Arc<(Mutex<usize>, Condvar)>,
    panicked: Arc<std::sync::atomic::AtomicBool>,
    _borrows: std::marker::PhantomData<&'s ()>,
}

impl<'s> Scope<'s> {
    fn new() -> Scope<'s> {
        Scope { left: Arc::new((Mutex::new(0), Condvar::new())), panicked: Arc::default(), _borrows: std::marker::PhantomData }
    }

    fn spawn(&self, f: impl FnOnce() + Send + 's) {
        *self.left.0.lock().unwrap() += 1;
        let (left, panicked) = (self.left.clone(), self.panicked.clone());
        let job: Box<dyn FnOnce() + Send + 's> = Box::new(move || {
            if std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).is_err() {
                panicked.store(true, Ordering::Relaxed);
            }
            let mut n = left.0.lock().unwrap();
            *n -= 1;
            if *n == 0 {
                left.1.notify_all();
            }
        });
        // SAFETY: `Scope::drop` blocks until this job has run, and `Scope` (which has a `Drop` impl) cannot
        // outlive `'s`, so everything the job borrows is alive while it runs.
        let job: Job = unsafe { std::mem::transmute::<Box<dyn FnOnce() + Send + 's>, Job>(job) };
        pool().lock().unwrap().send(job).expect("gate check pool is gone");
    }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        let mut n = self.left.0.lock().unwrap();
        while *n > 0 {
            n = self.left.1.wait(n).unwrap();
        }
        drop(n);
        if self.panicked.load(Ordering::Relaxed) && !std::thread::panicking() {
            panic!("a gate check worker panicked");
        }
    }
}

/// One candidate for `verify_first`: the escape `law` flown from `plant`. Candidates after the first are flown
/// on other threads from `seed` (a `Seed` of `plant`); without one, everything runs on the calling thread.
pub struct Cand<'a> {
    pub plant: &'a JsbPlant,
    pub seed: Option<&'a Seed>,
    pub law: Law,
}

/// Result of `verify_first`: the first candidate that verified (its index and rollout), the outcome of every
/// rollout that decided it (escape, outcome), the JSBSim frames those rollouts spent (from `frames0`), and the
/// last rollout that failed (for display). Also all frames flown, including rollouts cut short or discarded
/// because an earlier candidate verified, and the pool workers' thread CPU (s).
pub struct Verdict {
    pub found: Option<(usize, Roll)>,
    pub tried: Vec<(usize, Outcome)>,
    pub frames: usize,
    pub last: Option<Roll>,
    pub frames_all: usize,
    pub cpu_workers: f64,
}

impl Verdict {
    pub fn empty(frames0: usize) -> Verdict {
        Verdict { found: None, tried: Vec::new(), frames: frames0, last: None, frames_all: frames0, cpu_workers: 0.0 }
    }

    /// Record a rollout that decides the verdict (candidate `i`); whether it verified.
    fn decide(&mut self, i: usize, r: Roll) -> bool {
        self.frames += r.frames;
        self.tried.push((r.esc, r.outcome));
        if r.ok() {
            self.found = Some((i, r));
            true
        } else {
            self.last = Some(r);
            false
        }
    }
}

/// Frames a candidate's rollout may use (besides the budget): a resumed law (`t > 0`) at most `RESUME_CAP`.
fn law_cap(law: &Law) -> usize {
    if law.t > 0.0 { RESUME_CAP } else { usize::MAX }
}

/// Check candidates in order and return the first whose escape verifies. A candidate is the aircraft after a
/// candidate tick and the escape law state to fly from there.
/// - `CHECK_THREADS` = 0: one after another under the per-tick budget. The first rollout runs to its verdict;
///   later ones run only while at least `MIN_ATTEMPT` frames of `BUDGET` are left (`frames0` are spent).
/// - `CHECK_THREADS` ≥ 1: every candidate gets its full horizon (a resumed law `RESUME_CAP`) and the first in
///   priority order that verifies wins. With more than one thread and seeds, the candidates run concurrently:
///   the first on this thread, the rest on the pool, each from its own copy of the plant rebuilt from the seed
///   on the worker (Lean objects are never shared between threads). A candidate stops as soon as an earlier one
///   has verified, since it can no longer win; no other cut-off depends on timing, so the verdict is the
///   sequential full-horizon one (the wall-clock `deadline`, if given, is the exception).
pub fn verify_first(world: &World, cands: &[Cand], frames0: usize, deadline: Option<std::time::Instant>) -> Verdict {
    let mut v = Verdict::empty(frames0);
    let threads = CHECK_THREADS.load(Ordering::Relaxed);
    let n = cands.len();
    if threads == 0 {
        for (i, c) in cands.iter().enumerate() {
            let left = BUDGET.load(Ordering::Relaxed).saturating_sub(v.frames);
            if i > 0 && left < MIN_ATTEMPT {
                break;
            }
            let max = if i == 0 { usize::MAX } else { left };
            let r = rollout_ctl(world, c.plant, c.law, max.min(law_cap(&c.law)), deadline, None);
            v.frames_all += r.frames;
            if v.decide(i, r) {
                break;
            }
        }
        return v;
    }
    if threads == 1 || n < 2 || !cands[1..].iter().all(|c| c.seed.is_some()) {
        for (i, c) in cands.iter().enumerate() {
            let r = rollout_ctl(world, c.plant, c.law, law_cap(&c.law), deadline, None);
            v.frames_all += r.frames;
            if v.decide(i, r) {
                break;
            }
        }
        return v;
    }
    let best = AtomicUsize::new(usize::MAX);
    let slots: Vec<Mutex<Option<(Roll, f64)>>> = (0..n).map(|_| Mutex::new(None)).collect();
    {
        let scope = Scope::new();
        for i in 1..n {
            let (seed, law, best, slot) = (cands[i].seed.unwrap(), cands[i].law, &best, &slots[i]);
            scope.spawn(move || {
                if best.load(Ordering::Relaxed) < i {
                    return;
                }
                let c0 = thread_cpu();
                let p = JsbPlant::from_seed(seed);
                let r = rollout_ctl(world, &p, law, law_cap(&law), deadline, Some((best, i)));
                drop(p);
                if r.ok() {
                    best.fetch_min(i, Ordering::Relaxed);
                }
                *slot.lock().unwrap() = Some((r, thread_cpu() - c0));
            });
        }
        let r = rollout_ctl(world, cands[0].plant, cands[0].law, law_cap(&cands[0].law), deadline, None);
        if r.ok() {
            best.fetch_min(0, Ordering::Relaxed);
        }
        *slots[0].lock().unwrap() = Some((r, 0.0));
    }
    let verify = VERIFY_SEEDS.load(Ordering::Relaxed);
    for (i, slot) in slots.into_iter().enumerate() {
        let Some((r, cpu)) = slot.into_inner().unwrap() else { continue };
        v.frames_all += r.frames;
        v.cpu_workers += cpu;
        if v.found.is_some() {
            continue;
        }
        if verify && i > 0 {
            let c = &cands[i];
            let q = rollout_ctl(world, c.plant, c.law, law_cap(&c.law), deadline, None);
            let bits = |r: &Roll| r.path.iter().chain(&r.tail).flat_map(|p| p.map(f64::to_bits)).collect::<Vec<u64>>();
            assert!(
                q.outcome == r.outcome && q.frames == r.frames && q.min_clear.to_bits() == r.min_clear.to_bits() && bits(&q) == bits(&r),
                "seeded rollout {i} (escape {}) differs from the fork's: {:?}/{} vs {:?}/{}",
                r.esc,
                r.outcome,
                r.frames,
                q.outcome,
                q.frames
            );
        }
        v.decide(i, r);
    }
    v
}

/// Per-tick budget in JSBSim frames: 15 ms at the 6.7 µs per checked frame measured on an M4 Max. In frames,
/// not wall time, so runs are reproducible.
pub const BUDGET_FRAMES: usize = 2200;
/// The budget in force (`--budget FRAMES` overrides it for experiments).
pub static BUDGET: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(BUDGET_FRAMES);
/// Wall-clock cap per tick (ms; 0 = off). A check cut short fails, so the filter falls back to its witness:
/// safety is unchanged, only which command flies. The GUI sets 15 ms; headless runs stay deterministic.
pub static TIME_CAP_MS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
/// Commit runs this short (ticks) are counted separately: interventions a larger budget might have avoided.
pub const SHORT_RUN: u64 = 5;
/// Don't start another rollout in a tick with fewer frames than this left.
const MIN_ATTEMPT: usize = 640;

/// Pilot ticks after a hand-back during which the escape that was flying is tried first (resumed with its
/// clock and integrators), so a re-commit continues it instead of restarting or reversing it.
pub const RESUME_TICKS: u64 = 100;
/// Frames a resumed escape (one already flying, `Law::t > 0`) may use in a check: past the first terminal
/// tests (6 s, then every 0.5 s), so a resumed escape that does not settle again leaves budget for fresh ones.
pub const RESUME_CAP: usize = 1100;
/// Hysteresis: a commit holds at least this many ticks (0.3 s) before a hand-back is checked, and hands back
/// only to a candidate whose escape keeps `MARGIN + HANDBACK_EXTRA` (m) at every sample.
pub const HOLD_TICKS: u64 = 15;
pub const HANDBACK_EXTRA: f64 = 3.0;

/// Turn direction of a law's terminal set, or of its escape before the street escape picks a side.
fn law_dir(l: &Law) -> f64 {
    if l.dir() != 0.0 { l.dir() } else { ESCAPES[l.esc].dir }
}

/// Gatekeeper state.
///
/// Safety invariant (the statement the gate's proof is about): every tick applied to the aircraft is either
/// - (a) a candidate tick whose frames were checked clear and after which an escape law state verified from
///   the resulting aircraft state; that law state becomes `witness`; or
/// - (b) frames of `law`, the committed escape law state, which verified from the state where it was
///   committed, so flying on from here follows the rest of a verified rollout.
///
/// So while the pilot flies, `witness` is a law state (escape, clock, integrators, captured references) that
/// verified from the current aircraft state, and a commit flies exactly that law state. Which candidates are
/// tried, in which order, and when (resumption, direction preference) is proposal logic: it changes which
/// verified command flies, never whether one does. (Clearance of a candidate tick: `rollout_law` checks the
/// state the tick ends in and every `SAMPLE` frames of the escape, not the tick's intermediate frames.)
#[derive(Clone, Debug)]
pub struct Gate {
    /// Escape tried first each tick: the last one that verified.
    pub last: usize,
    /// First escape to try on the next committed tick (round robin across ticks).
    pub rr: usize,
    /// Escape law state verified from the current aircraft state, when flying the pilot: a fresh law, or the
    /// escape that was flying, resumed, after a hand-back.
    pub witness: Option<Law>,
    /// The committed escape law in flight.
    pub law: Option<Law>,
    /// Surfaces (elevator, aileron, rudder, throttle) applied on each frame of the latest tick.
    pub tick_surfaces: Vec<[f64; 4]>,
    /// Pilot ticks since the last hand-back.
    pub since_handback: u64,
    /// Displays: the latest rollout (and whether it verified), and the committed escape's verified path.
    pub shown: Vec<[f64; 3]>,
    pub shown_ok: bool,
    pub committed_path: Vec<[f64; 3]>,
    pub witness_path: Vec<[f64; 3]>,
    /// The first tick accepted the pilot's command.
    pub first_accept: Option<bool>,
    /// Ticks committed although no escape had ever verified (no witness).
    pub blind_ticks: u64,
    /// Rollout outcomes by `Outcome` (Ok, Hit, Horizon, Budget) and escape.
    pub outcomes: [[u64; 4]; N_ESC],
    /// Commit runs, those released within `SHORT_RUN` ticks, and the current run's length.
    pub runs: u64,
    pub short_runs: u64,
    pub run_len: u64,
    /// Smoothness: commits whose turn direction is opposite to the previous commit's, the turn direction of
    /// the latest committed law, and ticks flown with a blended command.
    pub reversals: u64,
    pub prev_dir: f64,
    pub blend_ticks: u64,
    /// Per-tick filter cost: thread CPU (ms), wall (ms), JSBSim frames.
    /// Per-tick filter cost: thread CPU (ms), wall (ms), JSBSim frames of the rollouts that decided the tick.
    pub cpu_ms: Vec<f32>,
    pub wall_ms: Vec<f32>,
    pub frames: Vec<u32>,
    /// With parallel checks (`CHECK_THREADS` > 1): all JSBSim frames flown, including discarded rollouts, and
    /// the pool workers' CPU (ms).
    pub frames_all: Vec<u32>,
    pub cpu_workers_ms: Vec<f32>,
}

impl Gate {
    /// Initialise from the starting aircraft: search every escape (not real-time; before the pilot flies).
    pub fn new(world: &World, p: &JsbPlant) -> Gate {
        let mut g = Gate {
            last: 0,
            rr: 0,
            witness: None,
            law: None,
            tick_surfaces: Vec::new(),
            since_handback: u64::MAX / 2,
            shown: Vec::new(),
            shown_ok: false,
            committed_path: Vec::new(),
            witness_path: Vec::new(),
            first_accept: None,
            blind_ticks: 0,
            outcomes: [[0; 4]; N_ESC],
            runs: 0,
            short_runs: 0,
            run_len: 0,
            reversals: 0,
            prev_dir: 0.0,
            blend_ticks: 0,
            cpu_ms: Vec::new(),
            wall_ms: Vec::new(),
            frames: Vec::new(),
            frames_all: Vec::new(),
            cpu_workers_ms: Vec::new(),
        };
        let mut best: Option<Roll> = None;
        for esc in 0..n_esc() {
            let r = rollout(world, p, esc, usize::MAX);
            if r.ok() {
                g.witness = Some(Law::new(esc));
                g.last = esc;
                g.witness_path = r.path.iter().chain(&r.tail).copied().collect();
                best = Some(r);
                break;
            }
            if best.as_ref().map_or(true, |b| r.t > b.t) {
                g.last = esc;
                best = Some(r);
            }
        }
        if let Some(b) = best {
            g.shown_ok = b.ok();
            g.shown = b.path;
        }
        g
    }

    /// One 20 ms tick: verify the pilot's next tick followed by an escape; fly the pilot's command if it
    /// verifies, otherwise the committed (witness) escape. Returns whether the pilot was accepted.
    pub fn tick(&mut self, world: &World, plant: &mut JsbPlant, u_p: &Cmd, dt: f64, filter_on: bool) -> bool {
        self.tick_pilot(world, plant, &Pilot::Fbw(*u_p), dt, filter_on)
    }

    /// Turn direction to keep when ordering escapes: the committed or witness law's, else the bank's, else
    /// the latest commit's.
    fn pref_dir(&self, o: &Obs) -> f64 {
        let d = self.law.or(self.witness).map_or(0.0, |l| law_dir(&l));
        if d != 0.0 {
            d
        } else if o.phi.abs() > 0.1 {
            o.phi.signum()
        } else {
            self.prev_dir
        }
    }

    /// Escape laws to try after the pilot's tick, in order: the committed escape continued (or, shortly after
    /// a hand-back, the resumed witness), then fresh escapes from `start` round the list, those turning the
    /// preferred way (or straight) before those turning against it.
    fn candidate_laws(&self, o: &Obs) -> Vec<Law> {
        let n = n_esc();
        let mut laws = Vec::with_capacity(n + 1);
        match (self.law, self.witness) {
            (Some(l), _) => laws.push(l),
            (None, Some(w)) if w.t == 0.0 || self.since_handback < RESUME_TICKS => laws.push(w),
            _ => {}
        }
        let pref = self.pref_dir(o);
        let start = if self.law.is_none() { self.last } else { self.rr };
        let order = (0..n).map(|i| (start + i) % n);
        let (with, against): (Vec<usize>, Vec<usize>) = order.partition(|&e| ESCAPES[e].dir * pref >= 0.0);
        for e in with.into_iter().chain(against) {
            if !laws.iter().any(|l| l.t == 0.0 && l.esc == e) {
                laws.push(Law::new(e));
            }
        }
        laws
    }

    /// `tick` for either kind of pilot command: fly-by-wire demands or raw surfaces.
    pub fn tick_pilot(&mut self, world: &World, plant: &mut JsbPlant, u_p: &Pilot, dt: f64, filter_on: bool) -> bool {
        let (c0, w0) = (thread_cpu(), std::time::Instant::now());
        let mut cand = plant.fork();
        if self.law.is_some() && matches!(u_p, Pilot::Fbw(_)) {
            cand.bumpless_fbw();
        }
        let f0 = (-cand.lag / DT_JSB).ceil().max(0.0) as usize;
        // Hysteresis (proposal logic: staying committed is always safe): no hand-back check during the hold.
        let holding = self.law.is_some() && self.run_len < HOLD_TICKS;
        let full = CHECK_THREADS.load(Ordering::Relaxed) > 0;
        let (cand_surf, dump) = cand.advance_pilot_dump(u_p, dt, full && filter_on && !holding);
        if !filter_on {
            *plant = cand;
            self.tick_surfaces = cand_surf;
            self.law = None;
            self.witness = None;
            return true;
        }
        let cap = TIME_CAP_MS.load(Ordering::Relaxed);
        let deadline = (cap > 0).then(|| w0 + std::time::Duration::from_millis(cap as u64));
        let laws = self.candidate_laws(&plant.obs);
        let seed = dump.map(|d| cand.seed(d));
        let cands: Vec<Cand> = laws.iter().map(|&law| Cand { plant: &cand, seed: seed.as_ref(), law }).collect();
        // After the hold, hand back only with `HANDBACK_EXTRA` of spare clearance.
        let committed = self.law.is_some();
        let mut v = if holding { Verdict::empty(f0) } else { verify_first(world, &cands, f0, deadline) };
        if committed && v.found.as_ref().is_some_and(|(_, r)| r.min_clear < MARGIN + HANDBACK_EXTRA) {
            v.last = v.found.take().map(|(_, r)| r);
        }
        let n = n_esc();
        for &(esc, out) in &v.tried {
            self.outcomes[esc][out as usize] += 1;
        }
        if self.law.is_some() {
            // Fresh escapes tried this tick (the first candidate is the committed escape continued).
            self.rr = (self.rr + v.tried.len().saturating_sub(1).max(1)) % n;
        }
        let shown = v.found.as_ref().map(|(_, r)| r).or(v.last.as_ref());
        if let Some(r) = shown {
            self.shown_ok = r.ok();
            self.shown = r.path.iter().chain(&r.tail).copied().collect();
        }
        let accept = if let Some((i, _)) = v.found {
            if self.law.is_some() {
                if self.run_len <= SHORT_RUN {
                    self.short_runs += 1;
                }
                self.since_handback = 0;
            } else {
                self.since_handback += 1;
            }
            *plant = cand;
            self.tick_surfaces = cand_surf;
            self.last = laws[i].esc;
            self.witness = Some(laws[i]);
            self.witness_path = self.shown.clone();
            self.law = None;
            self.committed_path.clear();
            true
        } else {
            if self.law.is_none() {
                let law = match self.witness {
                    Some(w) => w,
                    None => {
                        self.blind_ticks += 1;
                        Law::new(self.last)
                    }
                };
                if law_dir(&law) * self.prev_dir < 0.0 {
                    self.reversals += 1;
                }
                self.law = Some(law);
                self.committed_path = std::mem::take(&mut self.witness_path);
                self.runs += 1;
                self.run_len = 0;
            } else if self.witness.is_none() {
                self.blind_ticks += 1;
            }
            self.run_len += 1;
            let law = self.law.as_mut().unwrap();
            self.tick_surfaces.clear();
            plant.lag -= dt;
            while plant.lag < -1e-12 {
                law.step(world, plant);
                plant.lag += DT_JSB;
                self.tick_surfaces.push(plant.surf);
            }
            if law_dir(law) != 0.0 {
                self.prev_dir = law_dir(law);
            }
            false
        };
        self.first_accept.get_or_insert(accept);
        self.cpu_ms.push(((thread_cpu() - c0) * 1e3) as f32);
        self.wall_ms.push((w0.elapsed().as_secs_f64() * 1e3) as f32);
        self.frames.push(v.frames as u32);
        self.frames_all.push(v.frames_all as u32);
        self.cpu_workers_ms.push((v.cpu_workers * 1e3) as f32);
        accept
    }
}

#[repr(C)]
struct Timespec {
    sec: i64,
    nsec: i64,
}
extern "C" {
    fn clock_gettime(id: i32, ts: *mut Timespec) -> i32;
}
/// CPU time of the calling thread (s): check-time measurements that other processes' load does not inflate.
pub fn thread_cpu() -> f64 {
    #[cfg(target_os = "macos")]
    const ID: i32 = 16;
    #[cfg(not(target_os = "macos"))]
    const ID: i32 = 3;
    let mut ts = Timespec { sec: 0, nsec: 0 };
    unsafe { clock_gettime(ID, &mut ts) };
    ts.sec as f64 + ts.nsec as f64 * 1e-9
}
