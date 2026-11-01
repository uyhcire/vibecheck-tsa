//! The simulated aircraft + safety filter loop (physics 100 Hz, filter 50 Hz),
//! scenarios and random starts. Rendering-free so the harness runs headless.

use crate::escape::*;
use crate::filter::*;
use crate::model::*;
use crate::world::*;
use std::f64::consts::PI;

pub const WIND_SPEED: f64 = 7.0;
/// Gust envelope per axis (m/s): horizontal, vertical.
pub const GUST_XY: f64 = 2.5;
pub const GUST_Z: f64 = 0.5;

#[derive(Clone, Copy, Debug)]
pub struct SimCfg {
    pub filter_on: bool,
    pub filter: FilterCfg,
    /// Steady wind with bounded gusts (the filter knows the steady wind and
    /// the gust envelope).
    pub wind: bool,
    /// A weaker, slower aircraft than the filter's model (not known to it).
    pub model_error: bool,
    pub seed: u64,
}

impl Default for SimCfg {
    fn default() -> Self {
        SimCfg { filter_on: true, filter: FilterCfg { phase: Phase::P1, robust: false }, wind: false, model_error: false, seed: 1 }
    }
}

pub struct Sim<'w> {
    pub world: &'w World,
    pub cfg: SimCfg,
    pub s: State,
    pub k: u64,
    pub prm_true: Params,
    pub prm_ctrl: Params,
    pub fs: FilterState,
    pub wind: [f64; 3],
    wind_mean: [f64; 3],
    gust: [f64; 3],
    rng: Rng,
    pub crashed: bool,
    pub crash_clear: f64,
    pub true_clear: f64,
    pub min_true_clear: f64,
    pub applied: Cmd,
    pub started_safe: bool,
    // metrics
    pub ticks: u64,
    pub active_ticks: u64,
    pub commit_ticks: u64,
    pub inv_viol: u64,
    pub tail_fail: u64,
    pub ms_sum: f64,
    pub ms_max: f64,
    pub du_sum: f64,
    /// JSBSim's c172p in place of the point-mass model (`--jsb`).
    #[cfg(feature = "jsb")]
    pub jsb: Option<crate::jsb::JsbPlant>,
    /// Straight-ahead climb-out filter state (`--env`): the escape being flown, if committed.
    #[cfg(feature = "jsb")]
    pub env_law: Option<crate::envfilter::Law>,
    #[cfg(feature = "jsb")]
    pub env_hold: f64,
    #[cfg(feature = "jsb")]
    pub env_dir: usize,
    /// The escape the filter predicted at its last check.
    #[cfg(feature = "jsb")]
    pub env_pred: Vec<[f64; 3]>,
    #[cfg(feature = "jsb")]
    pub env_gate: Option<crate::envfilter::Gate>,
}

impl<'w> Sim<'w> {
    pub fn new(world: &'w World, s0: State, cfg: SimCfg) -> Sim<'w> {
        let mut rng = Rng::new(cfg.seed ^ 0x51u64);
        let wa = rng.range(0.0, 2.0 * PI);
        let ws = if cfg.wind { WIND_SPEED } else { 0.0 };
        let prm_true = if cfg.model_error { Params::mismatch() } else { Params::nominal() };
        let prm_ctrl = if cfg.filter.robust { Params::mismatch() } else { Params::nominal() };
        let wind_mean = [ws * wa.cos(), ws * wa.sin(), 0.0];
        let mut sim = Sim {
            world,
            cfg,
            s: s0,
            k: 0,
            prm_true,
            prm_ctrl,
            fs: FilterState::new(cfg.filter),
            wind: wind_mean,
            wind_mean,
            gust: [0.0; 3],
            rng,
            crashed: false,
            crash_clear: 0.0,
            true_clear: world.true_clearance([s0[X], s0[Y], s0[Z]]),
            min_true_clear: f64::INFINITY,
            applied: [1.0, 0.0, s0[THR]],
            started_safe: false,
            ticks: 0,
            active_ticks: 0,
            commit_ticks: 0,
            inv_viol: 0,
            tail_fail: 0,
            ms_sum: 0.0,
            ms_max: 0.0,
            du_sum: 0.0,
            #[cfg(feature = "jsb")]
            jsb: None,
            #[cfg(feature = "jsb")]
            env_law: None,
            #[cfg(feature = "jsb")]
            env_hold: 0.0,
            #[cfg(feature = "jsb")]
            env_dir: 0,
            #[cfg(feature = "jsb")]
            env_pred: Vec::new(),
            #[cfg(feature = "jsb")]
            env_gate: None,
        };
        #[cfg(feature = "jsb")]
        if crate::jsb::enabled() {
            let p = crate::jsb::JsbPlant::new(&s0);
            sim.s = p.state();
            if crate::envfilter::kind() == Some(crate::envfilter::Kind::Gate) {
                sim.env_gate = Some(crate::envfilter::Gate::new(world, &p));
            }
            if crate::envfilter::kind().is_some() {
                sim.true_clear = world.airframe_clearance(&sim.s, 200.0);
            }
            sim.jsb = Some(p);
        }
        let s0 = sim.s;
        sim.min_true_clear = sim.true_clear;
        let pred = sim.pred();
        sim.started_safe = sim.fs.init(&pred, &s0, 0);
        sim
    }

    pub fn pred(&self) -> Pred<'w> {
        Pred {
            world: self.world,
            prm: self.prm_ctrl,
            wind: self.wind_mean,
            robust: self.cfg.filter.robust,
            swept: true,
            accept: true,
            gust: self.gust_env().0,
            gust_z: self.gust_env().1,
        }
    }

    /// Gust envelope the filter is certified for: max horizontal and
    /// vertical deviation of the wind from its steady value.
    pub fn gust_env(&self) -> (f64, f64) {
        if self.cfg.wind {
            (GUST_XY * std::f64::consts::SQRT_2, GUST_Z)
        } else {
            (0.0, 0.0)
        }
    }

    /// Switch the filter on/off mid-flight (re-initialises the plan).
    pub fn set_filter(&mut self, on: bool) {
        self.cfg.filter_on = on;
        self.fs = FilterState::new(self.cfg.filter);
        if on {
            let pred = self.pred();
            let (s, k) = (self.s, self.k);
            self.started_safe = self.fs.init(&pred, &s, k);
        }
    }

    pub fn time(&self) -> f64 {
        self.k as f64 * DT
    }

    /// Steady wind plus gusts: a random (Ornstein-Uhlenbeck) process clipped
    /// to the envelope, per axis.
    fn update_wind(&mut self) {
        if !self.cfg.wind {
            self.wind = [0.0; 3];
            return;
        }
        let tau = 4.0;
        let sig = [1.5, 1.5, 0.5];
        let lim = [GUST_XY, GUST_XY, GUST_Z];
        for a in 0..3 {
            let dw = (self.rng.f() - 0.5) * 3.4641; // unit variance
            self.gust[a] += -self.gust[a] / tau * DT_F + sig[a] * (2.0 * DT_F / tau).sqrt() * dw;
            self.gust[a] = self.gust[a].clamp(-lim[a], lim[a]);
            self.wind[a] = self.wind_mean[a] + self.gust[a];
        }
    }

    /// One filter tick: pilot command in, two physics steps out.
    pub fn tick(&mut self, u_p: Cmd) {
        if self.crashed {
            return;
        }
        #[cfg(feature = "jsb")]
        if let (Some(kind), true) = (crate::envfilter::kind(), self.jsb.is_some()) {
            self.env_tick(kind, u_p);
            return;
        }
        self.update_wind();
        let src = if self.cfg.filter_on {
            let pred = self.pred();
            let src = self.fs.tick(&pred, &self.s, self.k, u_p);
            self.ms_sum += self.fs.ms;
            self.ms_max = self.ms_max.max(self.fs.ms);
            if !self.fs.inv_ok {
                self.inv_viol += 1;
            }
            if !self.fs.tail_ok {
                self.tail_fail += 1;
            }
            match self.fs.mode {
                Mode::Commit => {
                    self.commit_ticks += 1;
                    self.active_ticks += 1
                }
                Mode::Blend => self.active_ticks += 1,
                _ => {}
            }
            src
        } else {
            self.fs.mode = Mode::Off;
            self.fs.lam = 0.0;
            CmdSrc::Const(u_p)
        };
        let applied = match src {
            CmdSrc::Const(u) => u,
            CmdSrc::FollowPlan => match self.fs.plan {
                Some(pl) if self.k < pl.hold_end => pl.hold,
                Some(pl) => {
                    let e = pl.eref.unwrap_or_else(|| self.pred().esc_ref(&self.s, pl.esc));
                    esc_law(&self.prm_ctrl, &self.s, pl.esc, (self.k - pl.hold_end) as f64 * DT, &e, &self.wind).cmd
                }
                None => u_p,
            },
        };
        if self.ticks > 0 && self.fs.mode != Mode::Free && self.fs.mode != Mode::Off {
            self.du_sum += (applied[0] - self.applied[0]).abs() + (applied[1] - self.applied[1]).abs();
        }
        self.applied = applied;
        self.ticks += 1;
        for _ in 0..STEPS_PER_TICK {
            self.physics_step(src, u_p);
            if self.crashed {
                break;
            }
        }
    }

    #[cfg(feature = "jsb")]
    fn env_tick(&mut self, fk: crate::envfilter::Kind, u_p: Cmd) {
        use crate::envfilter::{check, Law};
        use crate::jsb::DT_JSB;
        let dt = DT * STEPS_PER_TICK as f64;
        self.ticks += 1;
        let filter_on = self.cfg.filter_on;
        let plant = self.jsb.as_mut().unwrap();
        if let Some(gate) = self.env_gate.as_mut() {
            let accept = gate.tick(self.world, plant, &u_p, dt, filter_on);
            self.env_pred = gate.shown.clone();
            if accept {
                self.applied = u_p;
                self.fs.mode = if filter_on { Mode::Free } else { Mode::Off };
                self.fs.lam = 0.0;
            } else {
                self.applied = [plant.obs.nz, 0.0, 1.0];
                self.fs.mode = Mode::Commit;
                self.fs.lam = 1.0;
                self.commit_ticks += 1;
                self.active_ticks += 1;
            }
            let ms = *gate.cpu_ms.last().unwrap_or(&0.0) as f64;
            self.ms_sum += ms;
            self.ms_max = self.ms_max.max(ms);
            self.env_after_tick();
            return;
        }
        // The pilot's command, one tick ahead; adopted as the next state if the filter accepts it.
        let mut cand = plant.fork();
        cand.advance(&u_p, dt);
        let committed = self.env_law.is_some();
        let accept = if !filter_on {
            true
        } else if committed && (self.env_hold < 2.0 || plant.obs.vned[2] > -1.0) {
            false
        } else {
            let (dir, path) = check(self.world, fk, &cand);
            self.env_pred = path;
            if let Some(d) = dir {
                self.env_dir = d;
            }
            dir.is_some()
        };
        if accept {
            if committed {
                cand.reset_fbw();
            }
            *plant = cand;
            self.env_law = None;
            self.applied = u_p;
            self.fs.mode = if filter_on { Mode::Free } else { Mode::Off };
            self.fs.lam = 0.0;
        } else {
            let mut law = self.env_law.unwrap_or_else(|| Law::new(self.env_dir));
            if !committed {
                self.env_hold = 0.0;
            }
            plant.lag -= dt;
            while plant.lag < -1e-12 {
                law.step(self.world, plant);
                plant.lag += DT_JSB;
            }
            self.env_law = Some(law);
            self.env_hold += dt;
            self.applied = [plant.obs.nz, 0.0, 1.0];
            self.fs.mode = Mode::Commit;
            self.fs.lam = 1.0;
            self.commit_ticks += 1;
            self.active_ticks += 1;
        }
        self.env_after_tick();
    }

    #[cfg(feature = "jsb")]
    fn env_after_tick(&mut self) {
        self.s = self.jsb.as_ref().unwrap().state();
        self.k += STEPS_PER_TICK;
        // Leaving the map climbing is not a crash for these filters: their escapes climb out straight.
        let off = self.s[X].abs() > crate::world::MAP_HALF || self.s[Y].abs() > crate::world::MAP_HALF;
        let c = if off { f64::INFINITY } else { self.world.airframe_clearance(&self.s, 200.0) };
        self.true_clear = c;
        self.min_true_clear = self.min_true_clear.min(c);
        if c < 0.0 {
            self.crashed = true;
            self.crash_clear = c;
        }
    }

    fn physics_step(&mut self, src: CmdSrc, u_p: Cmd) {
        let wind = self.wind;
        let prm = self.prm_true;
        #[cfg(feature = "jsb")]
        if self.jsb.is_some() {
            let u = match src {
                CmdSrc::Const(u) => u,
                // As on the point-mass plant: the escape follows the ground path the filter verified.
                CmdSrc::FollowPlan => match self.fs.plan {
                    Some(pl) if self.k < pl.hold_end => pl.hold,
                    Some(pl) => {
                        let te = (self.k - pl.hold_end) as f64 * DT;
                        let e = pl.eref.unwrap_or_else(|| self.pred().esc_ref(&self.s, pl.esc));
                        esc_law(&self.prm_ctrl, &self.s, pl.esc, te, &e, &wind).cmd
                    }
                    None => u_p,
                },
            };
            let p = self.jsb.as_mut().unwrap();
            p.advance(&u, DT);
            self.s = p.state();
            self.after_step();
            return;
        }
        match src {
            CmdSrc::Const(u) => rk4(&prm, &mut self.s, DT, &wind, |_, _| u),
            CmdSrc::FollowPlan => {
                if let Some(pl) = self.fs.plan {
                    if self.k < pl.hold_end {
                        let u = pl.hold;
                        rk4(&prm, &mut self.s, DT, &wind, |_, _| u);
                    } else {
                        let te = (self.k - pl.hold_end) as f64 * DT;
                        let pc = self.prm_ctrl;
                        let e = pl.eref.unwrap_or_else(|| self.pred().esc_ref(&self.s, pl.esc));
                        rk4(&prm, &mut self.s, DT, &wind, |st, off| esc_law(&pc, st, pl.esc, te + off, &e, &wind).cmd);
                    }
                } else {
                    rk4(&prm, &mut self.s, DT, &wind, |_, _| u_p);
                }
            }
        }
        self.after_step();
    }

    fn after_step(&mut self) {
        self.k += 1;
        let c = self.world.true_clearance([self.s[X], self.s[Y], self.s[Z]]);
        self.true_clear = c;
        self.min_true_clear = self.min_true_clear.min(c);
        if c < 0.0 {
            self.crashed = true;
            self.crash_clear = c;
        }
    }
}

// ---------------------------------------------------------------- starts

fn safe_h(world: &World, s: &State) -> f64 {
    let pred = Pred { world, prm: Params::nominal(), wind: [0.0; 3], robust: false, swept: true, accept: true, gust: 0.0, gust_z: 0.0 };
    pred.best(s, None, &ESC_ORDER, f64::INFINITY).0
}

pub const SCENARIOS: [&str; 5] = ["Tower run", "Dive", "Ridge", "Slow and low", "Tower gap"];
pub const SF_SCENARIOS: [&str; 4] = ["Salesforce run", "Dive", "Nob Hill", "Slow and low"];

/// Scenario names on a map.
pub fn scenario_names(map: MapId) -> &'static [&'static str] {
    match map {
        MapId::Grid => &SCENARIOS,
        MapId::SanFrancisco => &SF_SCENARIOS,
    }
}

/// Tower gap: the 28 m street `x = street_x(GAP_STREET)`, flown north. It runs between the 261 m and 292 m
/// towers of block row 9, crosses the avenue `y = 0`, then passes the 235 m and 352 m towers of row 10
/// (the 352 m one backs onto the tallest tower), with lower blocks and a park beyond (`esclab gaps`).
pub const GAP_STREET: usize = 9;

/// Whether the active filter verifies an escape from `s`: the exact-rollout filters on the JSBSim
/// aircraft, else the point-mass escapes.
pub fn start_verified(world: &World, s: &State) -> bool {
    #[cfg(feature = "jsb")]
    if crate::jsb::enabled() {
        use crate::envfilter::{check, kind, Gate, Kind};
        let p = crate::jsb::JsbPlant::new(s);
        return match kind() {
            Some(Kind::Gate) => Gate::new(world, &p).witness.is_some(),
            Some(k) => check(world, k, &p).0.is_some(),
            None => safe_h(world, s) >= 3.0,
        };
    }
    safe_h(world, s) >= 3.0
}

/// Lined up on the tower-gap street, below the roofs, at the first spot (searched outward from inside the
/// row-9 gap) where the active filter verifies an escape.
fn tower_gap_start(world: &World) -> State {
    let x = street_x(GAP_STREET);
    for agl in [88.0, 85.0, 90.0, 80.0, 75.0, 70.0] {
        for y in [-60.0, -50.0, -70.0, -40.0, -80.0, -30.0] {
            let s = trimmed(x, y, world.terrain(x, y) + agl, 45.0, 0.0, PI / 2.0, 0.7);
            if start_verified(world, &s) {
                return s;
            }
        }
    }
    trimmed(x, -60.0, world.terrain(x, -60.0) + 88.0, 45.0, 0.0, PI / 2.0, 0.7)
}

/// Display only: the aircraft as drawn between ticks. The sim advances in `DT_F` ticks and the screen at its
/// own rate, so drawing `Sim::s` directly moves the aircraft in tick-sized steps held for an uneven number of
/// frames. This keeps the last two ticks' states and returns the state a fraction of a tick past the older
/// one (one tick of display latency). Each state is placed at its tick's sim time: with JSBSim, `Sim::s` is
/// the tick's last frame, which runs `lag` (0 to 1/128 s) ahead of it, so ticks of 2 and 3 frames would
/// otherwise alternate short and long.
#[derive(Clone, Copy, Debug)]
pub struct Drawn {
    prev: State,
    cur: State,
}

impl Drawn {
    pub fn new(sim: &Sim) -> Drawn {
        let s = Drawn::of(sim);
        Drawn { prev: s, cur: s }
    }

    /// After each tick.
    pub fn push(&mut self, sim: &Sim) {
        self.prev = self.cur;
        self.cur = Drawn::of(sim);
    }

    /// `sim.s` moved back to the tick's sim time.
    pub fn of(sim: &Sim) -> State {
        #[allow(unused_mut)]
        let mut s = sim.s;
        #[cfg(feature = "jsb")]
        if let Some(p) = &sim.jsb {
            let v = [p.obs.vned[1], p.obs.vned[0], -p.obs.vned[2]];
            for (i, k) in [X, Y, Z].into_iter().enumerate() {
                s[k] -= v[i] * p.lag;
            }
        }
        s
    }

    /// The state `frac` (0 to 1) of the way from the older tick to the newer; angles take the short way round.
    pub fn at(&self, frac: f64) -> State {
        let t = frac.clamp(0.0, 1.0);
        let mut s = self.cur;
        for i in 0..s.len() {
            let d = self.cur[i] - self.prev[i];
            let d = if i == GAM || i == PSI || i == PHI { (d + PI).rem_euclid(2.0 * PI) - PI } else { d };
            s[i] = self.prev[i] + d * t;
        }
        s
    }
}

/// Deterministic scenario starts, each searched so that a verified escape
/// exists at spawn (inside the safe set).
pub fn scenario_start(world: &World, id: usize) -> State {
    if world.map == MapId::SanFrancisco {
        return sf_scenario_start(world, id);
    }
    let tc = world.tallest_center();
    match id {
        // 60 m up a street, aimed at the tallest tower.
        0 => {
            let sy = street_x(10) + 0.0; // east-west street just south of the tower block
            // Nearest spot with room (h above the blend band), so the pilot flies
            // freely for a few seconds before the filter has to act.
            let mut best = None;
            for need in [45.0, 25.0, 5.0] {
                for d in (500..1800).step_by(25) {
                    let x = tc[0] - d as f64;
                    let y = sy;
                    let z = world.terrain(x, y) + 60.0;
                    let psi = (tc[1] - y).atan2(tc[0] - x);
                    let s = trimmed(x, y, z, 50.0, 0.0, psi, 0.64);
                    if safe_h(world, &s) >= need && world.true_clearance([x, y, z]) > 20.0 {
                        best = Some(s);
                        break;
                    }
                }
                if best.is_some() {
                    break;
                }
            }
            best.unwrap_or_else(|| trimmed(tc[0] - 1500.0, sy, 80.0, 50.0, 0.0, 0.0, 0.64))
        }
        // 700 m above downtown, diving at 30 deg.
        1 => {
            let x = tc[0] - 900.0;
            let y = tc[1] - 300.0;
            let psi = (tc[1] - y).atan2(tc[0] - x);
            let z = world.terrain(tc[0], tc[1]) + 700.0;
            trimmed(x, y, z, 50.0, -30f64.to_radians(), psi, 0.64)
        }
        // Valley floor, heading at the inner ridge.
        2 => {
            let x = 150.0;
            let mut best = None;
            for yy in (0..700).step_by(20) {
                let y = world.ridge_y + 450.0 + yy as f64;
                let z = world.terrain(x, y) + 50.0;
                let s = trimmed(x, y, z, 50.0, 0.0, -PI / 2.0, 0.64);
                if safe_h(world, &s) >= 5.0 {
                    best = Some(s);
                    break;
                }
            }
            best.unwrap_or_else(|| trimmed(x, -1300.0, 60.0, 50.0, 0.0, -PI / 2.0, 0.64))
        }
        4 => tower_gap_start(world),
        // 40 m up at 1.3x stall among mid-rises.
        _ => {
            let v = 1.3 * V_STALL;
            let mut best: Option<(f64, State)> = None;
            for k in 4..17 {
                for j in 2..18 {
                    let x = street_x(k);
                    let y = street_x(j) + 60.0;
                    let r = ((x - 60.0).powi(2) + (y - 60.0).powi(2)).sqrt();
                    if !(650.0..1000.0).contains(&r) {
                        continue;
                    }
                    let z = world.terrain(x, y) + 40.0;
                    let psi = if y > 60.0 { -PI / 2.0 } else { PI / 2.0 };
                    let s = trimmed(x, y, z, v, 0.0, psi, 0.5);
                    // Prefer the most mid-rise-dense spot that is still safe.
                    let h = safe_h(world, &s);
                    if h >= 3.0 {
                        let mut dens = 0.0;
                        for a in -6..=6 {
                            for b in -6..=6 {
                                dens += world.surface(x + a as f64 * 15.0, y + b as f64 * 15.0) - world.terrain(x, y);
                            }
                        }
                        if best.as_ref().map_or(true, |b| dens > b.0) {
                            best = Some((dens, s));
                        }
                    }
                }
            }
            best.map(|b| b.1).unwrap_or_else(|| trimmed(-900.0, -900.0, 50.0, v, 0.0, 0.0, 0.5))
        }
    }
}

/// San Francisco scenarios: the same four ideas on real geometry.
fn sf_scenario_start(world: &World, id: usize) -> State {
    let tc = world.tallest_center();
    let ok = |s: &State, need: f64, room: f64| safe_h(world, s) >= need && world.true_clearance([s[X], s[Y], s[Z]]) > room;
    match id {
        // 60 m up Mission Street, aimed at Salesforce Tower (1st & Mission).
        0 => {
            if let Some(l) = world.street_line("Mission Street") {
                let (c, sn) = (l.dir.cos(), l.dir.sin());
                let along = (tc[0] - l.p0[0]) * c + (tc[1] - l.p0[1]) * sn;
                for need in [45.0, 25.0, 5.0] {
                    for d in (500..1800).step_by(25) {
                        let a = along - d as f64;
                        if a < 0.0 {
                            break;
                        }
                        let (x, y) = (l.p0[0] + a * c, l.p0[1] + a * sn);
                        let z = world.terrain(x, y) + 60.0;
                        let s = trimmed(x, y, z, 50.0, 0.0, (tc[1] - y).atan2(tc[0] - x), 0.64);
                        if ok(&s, need, 20.0) {
                            return s;
                        }
                    }
                }
            }
            trimmed(tc[0] - 1200.0, tc[1] - 1200.0, 260.0, 50.0, 0.0, PI / 4.0, 0.64)
        }
        // 700 m above downtown, diving at 30 deg at the tower.
        1 => {
            let (x, y) = (tc[0] - 900.0, tc[1] - 300.0);
            let z = world.terrain(tc[0], tc[1]) + 700.0;
            trimmed(x, y, z, 50.0, -30f64.to_radians(), (tc[1] - y).atan2(tc[0] - x), 0.64)
        }
        // 50 m above the street, heading up Nob Hill from below: of 16
        // approach bearings, the safe start that faces the most climb.
        2 => {
            let top = world.hilltop_near([-800.0, 200.0], 400.0);
            let mut best: Option<(f64, State)> = None;
            for k in 0..16 {
                let b = k as f64 * PI / 8.0;
                for d in (700..1300).step_by(50) {
                    let (x, y) = (top[0] + d as f64 * b.cos(), top[1] + d as f64 * b.sin());
                    let g = world.terrain(x, y);
                    let s = trimmed(x, y, g + 50.0, 50.0, 0.0, b + PI, 0.64);
                    if ok(&s, 5.0, 15.0) {
                        let climb = top[2] - g;
                        if best.as_ref().map_or(true, |bb| climb > bb.0) {
                            best = Some((climb, s));
                        }
                        break;
                    }
                }
            }
            best.map(|b| b.1).unwrap_or_else(|| trimmed(top[0], top[1] - 1000.0, 120.0, 50.0, 0.0, PI / 2.0, 0.64))
        }
        // 40 m up at 1.3x stall, along a street among mid-rises: the
        // densest safe spot of points every 120 m along streets 600-1500 m
        // from downtown.
        _ => {
            let v = 1.3 * V_STALL;
            let mut best: Option<(f64, State)> = None;
            for st in world.streets.iter().filter(|s| s.is_surface()) {
                for w in st.pts.windows(2) {
                    let (dx, dy) = (w[1][0] - w[0][0], w[1][1] - w[0][1]);
                    let len = (dx * dx + dy * dy).sqrt();
                    let mut a = 60.0;
                    while a < len {
                        let (x, y) = (w[0][0] + dx * a / len, w[0][1] + dy * a / len);
                        a += 120.0;
                        let r = ((x - tc[0]).powi(2) + (y - tc[1]).powi(2)).sqrt();
                        let g = world.terrain(x, y);
                        if !(600.0..1500.0).contains(&r) || world.surface(x, y) > g + 1.0 {
                            continue;
                        }
                        let mut dens = 0.0;
                        for i in -6..=6 {
                            for j in -6..=6 {
                                dens += world.surface(x + i as f64 * 15.0, y + j as f64 * 15.0) - g;
                            }
                        }
                        if best.as_ref().map_or(false, |b| dens <= b.0) {
                            continue;
                        }
                        let s = trimmed(x, y, g + 40.0, v, 0.0, dy.atan2(dx), 0.5);
                        if ok(&s, 3.0, 0.0) {
                            best = Some((dens, s));
                        }
                    }
                }
            }
            best.map(|b| b.1).unwrap_or_else(|| trimmed(-900.0, -900.0, 120.0, v, 0.0, 0.0, 0.5))
        }
    }
}

/// Random start inside the safe set (rejection sampled, deterministic).
pub fn random_start(world: &World, rng: &mut Rng) -> State {
    loop {
        let (x, y) = if rng.chance(0.65) {
            (rng.range(-1250.0, 1250.0), rng.range(-1250.0, 1250.0))
        } else {
            (rng.range(-2300.0, 2300.0), rng.range(-2300.0, 2300.0))
        };
        let agl = rng.range(40f64.ln(), 400f64.ln()).exp();
        let mut top = 0f64;
        for a in -2..=2 {
            for b in -2..=2 {
                top = top.max(world.surface(x + a as f64 * 10.0, y + b as f64 * 10.0));
            }
        }
        let z = top + agl;
        let v = rng.range(30.0, 55.0);
        let gam = rng.range(-15.0, 8.0).to_radians();
        let psi = rng.range(0.0, 2.0 * PI);
        let phi = rng.range(-30.0, 30.0).to_radians();
        let thr = rng.range(0.4, 1.0);
        let s: State = [x, y, z, v, gam, psi, phi, 0.0, gam.cos() / phi.cos(), thr];
        if world.true_clearance([x, y, z]) < 15.0 {
            continue;
        }
        if safe_h(world, &s) >= 3.0 {
            return s;
        }
    }
}
