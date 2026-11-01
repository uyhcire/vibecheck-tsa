//! P1-exact (`--env p1x`): Phase 1 blend-and-commit (`filter.rs`) predicting with exact JSBSim rollouts; see README.

use crate::envfilter::{law_params, rollout_law, thread_cpu, Law, Outcome, Roll, BUDGET, ESCAPES, MARGIN, N_ESC, SAMPLE, TIME_CAP_MS, n_esc};
use crate::filter::{LAM_DECAY, T_LOOK, T_MARGIN};
use crate::jsb::{JsbPlant, DT_JSB};
use crate::model::*;
use crate::world::World;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Instant;

/// Don't start another rollout in a tick with fewer budget frames than this left (as the gate).
const MIN_ATTEMPT: usize = 640;
/// Frames the free test leaves for the blend check (a typical verified escape needs about 900).
const RESERVE: usize = 1000;
/// Roll-rate gain of the escape's wings-level command (rad/s per rad of bank).
const K_ROLL: f64 = 2.5;

/// `--p1x-order margin`: P1's order (margin search, then the blend check) instead of the blend check first.
pub static MARGIN_FIRST: AtomicBool = AtomicBool::new(false);
/// `--p1x-scale S` multiplies P1's 1 s / 0.4 s / 0.1 s hold times (f64 bits).
pub static HOLD_SCALE: AtomicU64 = AtomicU64::new(0x3FF0_0000_0000_0000);

pub fn hold_scale() -> f64 {
    f64::from_bits(HOLD_SCALE.load(Ordering::Relaxed))
}

/// Read `--p1x-order margin` and `--p1x-scale S` from the command line.
pub fn parse_args(args: &[String]) {
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1));
    MARGIN_FIRST.store(arg("--p1x-order").is_some_and(|o| o == "margin"), Ordering::Relaxed);
    if let Some(s) = arg("--p1x-scale").and_then(|s| s.parse::<f64>().ok()) {
        HOLD_SCALE.store(s.to_bits(), Ordering::Relaxed);
    }
}

fn frames(t: f64) -> usize {
    (t / DT_JSB).round() as usize
}

/// Hold `hold` through the fly-by-wire for `hold_frames` frames from where it verified, then escape `esc`.
#[derive(Clone, Debug)]
pub struct XPlan {
    pub hold: Cmd,
    pub hold_frames: usize,
    pub esc: usize,
    pub flown: usize,
    pub law: Option<Law>,
    pub path: Vec<[f64; 3]>,
}

impl XPlan {
    /// Fly `dt` seconds of the plan on `plant` (frames run while the plant's lag is negative).
    fn fly(&mut self, world: &World, plant: &mut JsbPlant, dt: f64) {
        plant.lag -= dt;
        while plant.lag < -1e-12 {
            if self.flown < self.hold_frames {
                plant.frame(&self.hold);
            } else {
                let esc = self.esc;
                self.law.get_or_insert_with(|| Law::new(esc)).step(world, plant);
            }
            self.flown += 1;
            plant.lag += DT_JSB;
        }
    }
}

struct Margin {
    pass: Option<usize>,
    roll: Option<Roll>,
    failed: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum XMode {
    Free,
    Blend,
    Commit,
}

/// The escape's pull-up as a pilot command (point-mass signs): its load-factor command, wings level, full throttle.
pub fn esc_cmd(p: &JsbPlant, esc: usize) -> Cmd {
    let o = &p.obs;
    let lp = law_params();
    let gh = (o.vned[0] * o.vned[0] + o.vned[1] * o.vned[1]).sqrt();
    let v = o.vt.max(10.0);
    let g = (-o.vned[2]).atan2(gh);
    let cphi = o.phi.cos();
    let gc = (lp.gc_ref + lp.kv * (v - lp.v_ref[esc])).clamp(lp.gc_lo, lp.gc_hi);
    let n_long = g.cos() + v * lp.kg * (gc - g) / 9.80665;
    let n = if cphi < 0.35 { lp.nmin } else { (n_long / cphi).clamp(lp.nmin, lp.nmax) };
    let e = ESCAPES[esc];
    let phi_t = if lp.keep_bank && e.dir * o.phi > 0.0 { e.dir * o.phi.abs().min(e.bank) } else { 0.0 };
    let pm = Params::nominal();
    [n, (K_ROLL * (o.phi - phi_t)).clamp(-pm.p_max, pm.p_max), 1.0]
}

/// Forks after each mark's frames of `u`; `None` once a path sample came within `MARGIN`.
struct Hold {
    forks: Vec<Option<JsbPlant>>,
    path: Vec<[f64; 3]>,
    frames: usize,
}

fn hold(world: &World, base: &JsbPlant, u: &Cmd, marks: &[usize]) -> Hold {
    let n = *marks.iter().max().unwrap_or(&0);
    let mut q = base.fork();
    let mut out = Hold { forks: marks.iter().map(|_| None).collect(), path: Vec::with_capacity(n / SAMPLE + 2), frames: 0 };
    let ok = |q: &JsbPlant| {
        world.airframe_clearance(&q.state(), 50.0) > MARGIN
    };
    let s = q.state();
    out.path.push([s[X], s[Y], s[Z]]);
    if !ok(&q) {
        return out;
    }
    for (m, &k) in marks.iter().enumerate() {
        if k == 0 {
            out.forks[m] = Some(q.fork());
        }
    }
    for k in 1..=n {
        q.frame(u);
        out.frames = k;
        let mark = marks.iter().any(|&m| m == k);
        if k % SAMPLE == 0 || mark {
            let s = q.state();
            out.path.push([s[X], s[Y], s[Z]]);
            if !ok(&q) {
                return out;
            }
        }
        if mark {
            for (m, &mk) in marks.iter().enumerate() {
                if mk == k {
                    out.forks[m] = Some(q.fork());
                }
            }
        }
    }
    out
}

/// Per-tick frame budget; `limit` caps the current phase below it.
struct Search {
    budget: usize,
    limit: usize,
    frames: usize,
    deadline: Option<Instant>,
}

impl Search {
    fn cap(&self) -> Option<usize> {
        let left = self.budget.min(self.limit).saturating_sub(self.frames);
        if left < MIN_ATTEMPT || self.deadline.is_some_and(|d| Instant::now() >= d) {
            None
        } else {
            Some(left)
        }
    }
}

/// Invariant: `plan` verified on a fork of the plant, which has flown exactly `plan.flown` of its frames since.
#[derive(Clone, Debug)]
pub struct P1x {
    pub order: [usize; N_ESC],
    pub plan: Option<XPlan>,
    pub lam: f64,
    pub mode: XMode,
    pub applied: Cmd,
    pub level: usize,
    pub lam_t: f64,
    /// Commits by cause: blend check cut by the budget, failed outright, its hold came within `MARGIN`.
    pub why: [u64; 3],
    pub shown: Vec<[f64; 3]>,
    pub shown_ok: bool,
    pub first_accept: Option<bool>,
    pub blind_ticks: u64,
    pub outcomes: [[u64; 4]; N_ESC],
    pub runs: u64,
    pub short_runs: u64,
    pub run_len: u64,
    pub cpu_ms: Vec<f32>,
    pub wall_ms: Vec<f32>,
    pub frames: Vec<u32>,
}

impl P1x {
    pub fn new(world: &World, p: &JsbPlant) -> P1x {
        let mut x = P1x {
            order: std::array::from_fn(|i| i),
            plan: None,
            lam: 0.0,
            mode: XMode::Free,
            applied: [1.0, 0.0, p.thr],
            level: 0,
            lam_t: 0.0,
            why: [0; 3],
            shown: Vec::new(),
            shown_ok: false,
            first_accept: None,
            blind_ticks: 0,
            outcomes: [[0; 4]; N_ESC],
            runs: 0,
            short_runs: 0,
            run_len: 0,
            cpu_ms: Vec::new(),
            wall_ms: Vec::new(),
            frames: Vec::new(),
        };
        for esc in 0..n_esc() {
            let r = rollout_law(world, p, Law::new(esc), usize::MAX, None);
            if r.ok() {
                x.promote(esc);
                x.plan = Some(XPlan { hold: [1.0, 0.0, p.thr], hold_frames: 0, esc, flown: 0, law: None, path: r.path.iter().chain(&r.tail).copied().collect() });
                x.shown_ok = true;
                x.shown = x.plan.as_ref().unwrap().path.clone();
                break;
            }
        }
        x
    }

    fn promote(&mut self, i: usize) {
        if let Some(pos) = self.order.iter().position(|&x| x == i) {
            self.order[..=pos].rotate_right(1);
        }
    }

    /// Try the escapes in order from the end of a hold (`q`, reached after `pre` frames); `Err(true)` if all failed outright.
    fn try_escapes(&mut self, world: &World, q: &JsbPlant, first: Option<usize>, sr: &mut Search, pre: &[[f64; 3]]) -> Result<Roll, bool> {
        let n = n_esc();
        let mut order: Vec<usize> = self.order.iter().copied().filter(|&e| e < n).collect();
        if let Some(f) = first.filter(|&f| f < n) {
            order.retain(|&e| e != f);
            order.insert(0, f);
        }
        for esc in order {
            let Some(cap) = sr.cap() else { return Err(false) };
            let r = rollout_law(world, q, Law::new(esc), cap, sr.deadline);
            sr.frames += r.frames;
            self.outcomes[esc][r.outcome as usize] += 1;
            self.shown_ok = r.ok();
            self.shown = pre.iter().chain(&r.path).chain(&r.tail).copied().collect();
            if r.ok() {
                return Ok(r);
            }
            if r.outcome == Outcome::Budget {
                return Err(false);
            }
        }
        Err(true)
    }

    /// One 20 ms tick: returns the mode; `applied` and `lam` describe the command flown.
    pub fn tick(&mut self, world: &World, plant: &mut JsbPlant, u_p: &Cmd, dt: f64, filter_on: bool) -> XMode {
        let (c0, w0) = (thread_cpu(), Instant::now());
        let mut base = plant.fork();
        if self.plan.as_ref().is_some_and(|p| p.law.is_some()) {
            base.bumpless_fbw();
        }
        if !filter_on {
            *plant = base;
            plant.advance(u_p, dt);
            self.plan = None;
            self.lam = 0.0;
            self.mode = XMode::Free;
            self.applied = *u_p;
            return XMode::Free;
        }
        let cap = TIME_CAP_MS.load(Ordering::Relaxed);
        let budget = BUDGET.load(Ordering::Relaxed);
        let mut sr = Search { budget, limit: budget, frames: 0, deadline: (cap > 0).then(|| w0 + std::time::Duration::from_millis(cap as u64)) };
        let marks: Vec<usize> = T_MARGIN.iter().map(|&(t, _)| frames(t * hold_scale())).collect();
        let h = hold(world, &base, u_p, &marks);
        sr.frames += h.frames;
        // Levels shallower than the decay floor's give the same λ: start at the deepest one at or below it.
        let floor = self.lam - LAM_DECAY * DT_F;
        let start = if floor <= 1e-3 { 0 } else { T_MARGIN.iter().rposition(|&(_, l)| l <= floor).unwrap_or(0) };
        let margin_first = MARGIN_FIRST.load(Ordering::Relaxed);
        let (mut lam_t, mut free, mut working, mut next) = (self.lam_t, None, None, start);
        if margin_first || start == 0 {
            let to = if margin_first { T_MARGIN.len() } else { 1 };
            sr.limit = if margin_first { budget } else { budget.saturating_sub(RESERVE) };
            let m = self.margin(world, &h, &marks, start, to, &mut sr);
            sr.limit = budget;
            lam_t = match m.pass {
                Some(n) => T_MARGIN[n].1,
                None if margin_first => 1.0,
                None => self.lam_t.max(T_MARGIN[1].1),
            };
            self.level = m.pass.unwrap_or(T_MARGIN.len());
            working = m.roll.as_ref().map(|r| r.esc);
            free = m.roll.filter(|_| m.pass == Some(0));
            next = to;
        }
        let lam = lam_t.max(floor).clamp(0.0, 1.0);
        let is_free = lam <= 1e-3 && free.is_some();
        let accepted = if let (true, Some(r)) = (is_free, free) {
            let path = h.path.iter().chain(&r.path).chain(&r.tail).copied().collect();
            self.adopt(world, plant, base, *u_p, marks[0], r.esc, path, dt);
            self.lam = 0.0;
            self.mode = XMode::Free;
            self.applied = *u_p;
            true
        } else {
            // Blend toward the escape that verified in the margin search (else the last good one).
            let i_b = working.unwrap_or(self.order[0]);
            let u_l = lerp_cmd(u_p, &esc_cmd(&base, i_b), lam);
            let n_look = frames(T_LOOK);
            let hl = hold(world, &base, &u_l, &[n_look]);
            sr.frames += hl.frames;
            let r = match hl.forks[0].as_ref() {
                Some(q) => self.try_escapes(world, q, Some(i_b), &mut sr, &hl.path).map_err(|out| self.why[out as usize] += 1).ok(),
                None => {
                    self.why[2] += 1;
                    None
                }
            };
            match r {
                Some(r) => {
                    let path = hl.path.iter().chain(&r.path).chain(&r.tail).copied().collect();
                    self.adopt(world, plant, base, u_l, n_look, r.esc, path, dt);
                    self.lam = lam;
                    self.mode = XMode::Blend;
                    self.applied = u_l;
                    true
                }
                None => {
                    self.order.rotate_left(1);
                    false
                }
            }
        };
        // Blend check first: measure the margin for the next tick with the budget left.
        if !margin_first && !is_free && next < T_MARGIN.len() {
            let m = self.margin(world, &h, &marks, next, T_MARGIN.len(), &mut sr);
            lam_t = match (m.pass, m.failed) {
                (Some(n), _) => T_MARGIN[n].1,
                (None, Some(f)) => lam_t.max(T_MARGIN.get(f + 1).map_or(1.0, |l| l.1)),
                (None, None) => lam_t,
            };
            self.level = m.pass.unwrap_or(T_MARGIN.len());
        }
        self.lam_t = if is_free { 0.0 } else { lam_t };
        if accepted {
            if self.run_len > 0 && self.run_len <= crate::envfilter::SHORT_RUN {
                self.short_runs += 1;
            }
            self.run_len = 0;
        } else {
            // Gatekeeper fallback: keep flying the committed plan, frame for frame.
            if self.run_len == 0 {
                self.runs += 1;
            }
            self.run_len += 1;
            let plan = match self.plan.as_mut() {
                Some(p) => p,
                None => {
                    self.blind_ticks += 1;
                    self.plan.insert(XPlan { hold: *u_p, hold_frames: 0, esc: self.order[0], flown: 0, law: None, path: Vec::new() })
                }
            };
            plan.fly(world, plant, dt);
            self.lam = 1.0;
            self.mode = XMode::Commit;
            self.applied = [plant.obs.nz, 0.0, 1.0];
        }
        self.first_accept.get_or_insert(accepted);
        self.cpu_ms.push(((thread_cpu() - c0) * 1e3) as f32);
        self.wall_ms.push((w0.elapsed().as_secs_f64() * 1e3) as f32);
        self.frames.push(sr.frames as u32);
        self.mode
    }

    /// First level in `from..to` whose hold then some escape verifies; `failed` is the deepest level that failed outright.
    fn margin(&mut self, world: &World, h: &Hold, marks: &[usize], from: usize, to: usize, sr: &mut Search) -> Margin {
        let mut m = Margin { pass: None, roll: None, failed: None };
        for n in from..to {
            let Some(q) = h.forks[n].as_ref() else {
                m.failed = Some(n);
                continue;
            };
            let pre: Vec<[f64; 3]> = h.path.iter().take(1 + marks[n] / SAMPLE).copied().collect();
            match self.try_escapes(world, q, None, sr, &pre) {
                Ok(r) => {
                    (m.pass, m.roll) = (Some(n), Some(r));
                    return m;
                }
                Err(true) => m.failed = Some(n),
                Err(false) => return m,
            }
        }
        m
    }

    /// Adopt a plan that verified from `base`: the plant becomes `base` and flies the plan's first frames.
    #[allow(clippy::too_many_arguments)]
    fn adopt(&mut self, world: &World, plant: &mut JsbPlant, base: JsbPlant, hold: Cmd, hold_frames: usize, esc: usize, path: Vec<[f64; 3]>, dt: f64) {
        *plant = base;
        let mut plan = XPlan { hold, hold_frames, esc, flown: 0, law: None, path };
        plan.fly(world, plant, dt);
        self.promote(esc);
        self.plan = Some(plan);
    }
}
