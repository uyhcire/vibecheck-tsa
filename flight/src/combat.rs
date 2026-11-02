//! Dogfight mode, for fun: a fly (the bandit, flown by `flybrain`) hunts the player with guns and the player can shoot back. Bullets are
//! points under gravity, swept against a sphere around each aircraft every tick. Hits only add smoke (and
//! fire past 60%); an aircraft explodes after `HITS_TO_KILL` hits. Nothing here talks to the safety filter.

use crate::flybrain::Brain;
use crate::model::*;
use crate::pilot::Fbw;
use crate::world::{Rng, World, MAP_HALF};
use std::f64::consts::PI;

/// Muzzle velocity [m/s], bullet lifetime [s], time between rounds [s] (12.5 rounds/s).
pub const MUZZLE_V: f64 = 850.0;
pub const BULLET_LIFE: f64 = 2.5;
pub const FIRE_INTERVAL: f64 = 0.08;
/// Hit sphere around each aircraft [m] and the hits that destroy it.
pub const HIT_R: f64 = 4.5;
pub const HITS_TO_KILL: u32 = 15;
/// The bandit opens fire inside this range when its boresight is within `AIM_CONE` rad of its aim point.
pub const GUN_RANGE: f64 = 650.0;
const AIM_CONE: f64 = 0.045;
/// Seconds before a new bandit appears (after a kill, and at the start).
const RESPAWN: f64 = 6.0;
const FIRST_SPAWN: f64 = 1.5;

pub struct Bullet {
    pub p: [f64; 3],
    pub v: [f64; 3],
    pub age: f64,
    /// Fired by the player (hits the bandit) or by the bandit (hits the player).
    pub player: bool,
    pub tracer: bool,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum FxKind {
    Smoke,
    Fire,
    Flash,
    Spark,
    Dust,
    Debris,
}

/// A visual particle: smoke, fire, flashes, debris. Drawn by the GUI, never collides with anything.
pub struct Puff {
    pub kind: FxKind,
    pub p: [f64; 3],
    pub v: [f64; 3],
    pub age: f64,
    pub life: f64,
    pub size: f64,
    /// Smoke darkness, 0 = light grey, 1 = black.
    pub shade: f64,
}

impl Puff {
    /// Fraction of its life gone.
    pub fn u(&self) -> f64 {
        (self.age / self.life).clamp(0.0, 1.0)
    }
    /// Current radius [m]: smoke and dust grow, fire swells a little, flashes shrink.
    pub fn radius(&self) -> f64 {
        let u = self.u();
        match self.kind {
            FxKind::Smoke | FxKind::Dust => self.size * (1.0 + 2.5 * u),
            FxKind::Fire => self.size * (1.0 + 0.8 * u),
            FxKind::Flash => self.size * (1.0 - 0.5 * u),
            FxKind::Spark | FxKind::Debris => self.size,
        }
    }
    /// Opacity (smoke, dust, debris) or brightness (fire, flash, spark), 0..1.
    pub fn strength(&self) -> f64 {
        let u = self.u();
        match self.kind {
            FxKind::Smoke | FxKind::Dust => 0.6 * (1.0 - u).powf(1.5) * (self.age / 0.15).min(1.0),
            FxKind::Fire => (1.0 - u) * (1.0 - u),
            FxKind::Flash | FxKind::Spark => 1.0 - u,
            FxKind::Debris => 1.0,
        }
    }
}

pub struct Bandit {
    pub s: State,
    /// State at the previous tick (for drawing between ticks and for sweeping bullets).
    pub prev: State,
    pub hits: u32,
    fbw: Fbw,
    rng: Rng,
    aim_off: [f64; 3],
    aim_t: f64,
    /// Bearing of the lead point at the last tick, and its rate (low-passed), for the turn feedforward.
    los_psi: Option<f64>,
    los_rate: f64,
    /// Where the fly saw the target at the last tick (flight-path frame), for the direction's rate.
    prev_t: Option<[f64; 3]>,
    /// > 0: seconds left in the current burst; < 0: pause before the next one.
    burst: f64,
    gun_t: f64,
}

/// The bandit: the nominal aircraft with more power and a higher g limit, so it can catch the player.
pub fn bandit_params() -> Params {
    let mut p = Params::nominal();
    p.power *= 1.3;
    p.t_static *= 1.3;
    p.n_max = 4.5;
    p
}

pub fn pos(s: &State) -> [f64; 3] {
    [s[X], s[Y], s[Z]]
}

/// Flight-path direction (the guns' boresight).
pub fn dir(s: &State) -> [f64; 3] {
    let (sg, cg) = s[GAM].sin_cos();
    let (sp, cp) = s[PSI].sin_cos();
    [cg * cp, cg * sp, sg]
}

pub fn vel(s: &State) -> [f64; 3] {
    let d = dir(s);
    [d[0] * s[V], d[1] * s[V], d[2] * s[V]]
}

fn add(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}
fn sub(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
fn mul(a: [f64; 3], k: f64) -> [f64; 3] {
    [a[0] * k, a[1] * k, a[2] * k]
}
fn dot(a: [f64; 3], b: [f64; 3]) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}
fn norm(a: [f64; 3]) -> f64 {
    dot(a, a).sqrt()
}

fn wrap(a: f64) -> f64 {
    (a + PI).rem_euclid(2.0 * PI) - PI
}

/// Distance from the origin to the segment `a`-`b`, and the closest point.
fn seg_origin(a: [f64; 3], b: [f64; 3]) -> (f64, [f64; 3]) {
    let ab = sub(b, a);
    let t = (-dot(a, ab) / dot(ab, ab).max(1e-12)).clamp(0.0, 1.0);
    let c = add(a, mul(ab, t));
    (norm(c), c)
}

fn rand_dir(rng: &mut Rng) -> [f64; 3] {
    loop {
        let v = [rng.range(-1.0, 1.0), rng.range(-1.0, 1.0), rng.range(-1.0, 1.0)];
        let n = norm(v);
        if n > 0.05 && n <= 1.0 {
            return mul(v, 1.0 / n);
        }
    }
}

/// Where to point the boresight so a round fired now meets a target at `tgt`: rounds carry the shooter's
/// velocity, so the target moves by its velocity relative to the shooter, and gravity drops the round.
pub fn lead_point(shooter: &State, tgt: &State) -> [f64; 3] {
    let rel = sub(pos(tgt), pos(shooter));
    let t = norm(rel) / MUZZLE_V;
    let drift = mul(sub(vel(tgt), vel(shooter)), t);
    add(add(pos(shooter), add(rel, drift)), [0.0, 0.0, 0.5 * G * t * t])
}

/// Inputs and outputs of the bandit's pilot.
pub const NOBS: usize = 11;
pub const NACT: usize = 4;
/// Half-span of the target the fly sees [m] (sets its apparent size).
pub const TARGET_R: f64 = 5.5;

/// What the fly sees and feels. Sight: the direction to the target in its flight-path frame (forward, left, up;
/// with its aim wander), that direction's rate of change [1/s], and the log of the target's apparent angular
/// radius. The fly brain turns these into its LC10 neurons' receptive-field responses (`flybrain::retina`), so
/// it never gets the range, the bearing rate or the lead as numbers. Proprioception: its own speed, flight path,
/// bank and throttle.
pub fn observe(s: &State, t: [f64; 3], t_dot: [f64; 3], d: f64) -> [f32; NOBS] {
    let rho = (TARGET_R / d.max(1.0)).atan();
    let o = [t[0], t[1], t[2], t_dot[0], t_dot[1], t_dot[2], rho.ln(), s[V] / 50.0 - 1.0, s[GAM], s[PHI], s[THR]];
    o.map(|x| x as f32)
}

/// The hand-written pursuit law the fly brain is fine-tuned to imitate: bank for the aim point's bearing rate
/// (so a turning target needs no steady error) plus a correction toward it, climb toward it, throttle back when
/// close, and fire when the nose is on it inside gun range.
pub fn pursuit_law(s: &State, aim: [f64; 3], d: f64, los_rate: f64) -> [f64; NACT] {
    let psi_des = aim[1].atan2(aim[0]);
    let g_des = aim[2].atan2(aim[0].hypot(aim[1]));
    let rate = 1.2 * wrap(psi_des - s[PSI]) + los_rate;
    let phi = (rate * s[V] / G).atan().clamp(-70f64.to_radians(), 70f64.to_radians());
    let thr = if d > 300.0 { 1.0 } else { (0.5 + (d - 150.0) / 300.0).clamp(0.35, 1.0) };
    let on = dot(dir(s), aim) > norm(aim) * AIM_CONE.cos() && d < GUN_RANGE;
    [phi, g_des.clamp(-40f64.to_radians(), 35f64.to_radians()), thr, on as u8 as f64]
}

impl Bandit {
    /// A bandit 1.1-1.6 km from the player, at or above its height and clear of the city, heading at it.
    pub fn spawn(w: &World, player: &State, rng: &mut Rng) -> Bandit {
        let lim = MAP_HALF - 300.0;
        let mut s = trimmed(0.0, 0.0, 600.0, 50.0, 0.0, 0.0, 0.8);
        for _ in 0..40 {
            let a = rng.range(0.0, 2.0 * PI);
            let d = rng.range(1100.0, 1600.0);
            let x = (player[X] + d * a.cos()).clamp(-lim, lim);
            let y = (player[Y] + d * a.sin()).clamp(-lim, lim);
            let mut z = (player[Z] + rng.range(20.0, 120.0)).max(w.surface(x, y) + 120.0);
            while w.true_clearance([x, y, z]) < 60.0 && z < 2000.0 {
                z += 40.0;
            }
            s = trimmed(x, y, z, 50.0, 0.0, (player[Y] - y).atan2(player[X] - x), 0.8);
            if w.true_clearance([x, y, z]) >= 60.0 {
                break;
            }
        }
        Bandit {
            s,
            prev: s,
            hits: 0,
            fbw: Fbw::from_state(&s),
            rng: Rng::new(rng.next_u64()),
            aim_off: [0.0; 3],
            aim_t: 0.0,
            los_psi: None,
            los_rate: 0.0,
            prev_t: None,
            burst: 1.0,
            gun_t: 0.0,
        }
    }

    /// What the pilot sees this tick, and what the hand-written pursuit law would command (the fly brain's
    /// teacher). Updates the aim wander and the bearing-rate filter, so call it once per tick.
    pub fn sense(&mut self, tgt: &State, dt: f64) -> ([f32; NOBS], [f64; NACT]) {
        let s = self.s;
        let rel = sub(pos(tgt), pos(&s));
        let d = norm(rel);
        // Aim wander, re-drawn every 0.3-0.9 s: about 0.8 degrees, so not every burst hits.
        self.aim_t -= dt;
        if self.aim_t <= 0.0 {
            self.aim_t = self.rng.range(0.3, 0.9);
            self.aim_off = mul(rand_dir(&mut self.rng), self.rng.range(0.0, 0.014));
        }
        let lead = sub(lead_point(&s, tgt), pos(&s));
        let mut aim = add(lead, mul(self.aim_off, d));
        if d < 90.0 {
            // Too close: pass above rather than ram.
            aim[2] += 60.0;
        }
        let los = lead[1].atan2(lead[0]);
        if let Some(prev) = self.los_psi {
            let r = (wrap(los - prev) / dt).clamp(-1.0, 1.0);
            self.los_rate += (r - self.los_rate) * 0.2;
        }
        self.los_psi = Some(los);
        // What the fly sees: the target itself (not the lead), wandering with its aim, in its flight-path frame.
        let seen = add(rel, mul(self.aim_off, d));
        let [f, l, u] = airframe_axes(&s, 0.0);
        let n = norm(seen).max(1e-6);
        let t = [dot(seen, f) / n, dot(seen, l) / n, dot(seen, u) / n];
        let t_dot = self.prev_t.map_or([0.0; 3], |p| mul(sub(t, p), 1.0 / dt));
        self.prev_t = Some(t);
        (observe(&s, t, t_dot, d), pursuit_law(&s, aim, d, self.los_rate))
    }

    /// Fly the pilot's command `act` (bank, flight path, throttle, fire), unless a reflex takes over: away from
    /// the city when the path ahead is blocked, toward the middle near the map edge. Returns whether it fires.
    pub fn command(&mut self, w: &World, act: [f64; NACT], dt: f64) -> bool {
        let s = self.s;
        self.fbw.phi_ref = act[0].clamp(-70f64.to_radians(), 70f64.to_radians());
        self.fbw.g_ref = act[1].clamp(-40f64.to_radians(), 35f64.to_radians());
        self.fbw.thr = act[2].clamp(0.3, 1.0);
        let mut avoiding = false;
        let fwd = dir(&s);
        for k in 1..=8 {
            let t = 0.5 * k as f64;
            let q = add(pos(&s), mul(fwd, s[V] * t));
            if q[0].abs() > MAP_HALF - 150.0 || q[1].abs() > MAP_HALF - 150.0 {
                // Map edge ahead: turn toward the middle.
                let back = (-s[Y]).atan2(-s[X]);
                self.fbw.phi_ref = (1.8 * wrap(back - s[PSI])).clamp(-60f64.to_radians(), 60f64.to_radians());
                self.fbw.g_ref = self.fbw.g_ref.max(0.0);
                avoiding = true;
                break;
            }
            if w.true_clearance(q) < 8.0 + 4.0 * t {
                // City ahead: roll wings level and climb.
                self.fbw.phi_ref = 0.0;
                self.fbw.g_ref = 30f64.to_radians();
                self.fbw.thr = 1.0;
                avoiding = true;
                break;
            }
        }
        if self.burst > 0.0 {
            self.burst -= dt;
            if self.burst <= 0.0 {
                self.burst = -self.rng.range(0.6, 1.4);
            }
        } else {
            self.burst += dt;
            if self.burst >= 0.0 {
                self.burst = self.rng.range(0.8, 1.8);
            }
        }
        !avoiding && self.burst > 0.0 && act[3] > 0.5
    }

    /// One tick of the pilot: the fly brain if one is loaded, otherwise the hand-written law.
    fn steer(&mut self, w: &World, tgt: &State, dt: f64, brain: Option<&mut Brain>) -> bool {
        let (obs, law) = self.sense(tgt, dt);
        let act = brain.map_or(law, |b| b.act(&obs));
        self.command(w, act, dt)
    }

    pub fn fly(&mut self) {
        self.prev = self.s;
        let (prm, fbw) = (bandit_params(), self.fbw);
        for _ in 0..STEPS_PER_TICK {
            rk4(&prm, &mut self.s, DT, &[0.0; 3], |st, _| fbw.cmd(&prm, st));
        }
    }
}

pub struct Dogfight {
    pub bandit: Option<Bandit>,
    pub bullets: Vec<Bullet>,
    pub fx: Vec<Puff>,
    pub player_hits: u32,
    pub player_dead: bool,
    pub kills: u32,
    /// Seconds since the player was last hit, and since the last kill (for HUD flashes).
    pub since_hit: f64,
    pub since_kill: f64,
    /// How the last bandit went down.
    pub kill_msg: &'static str,
    /// The bandit's pilot: the fly brain (`flybrain.rs`), or the hand-written law if none is loaded.
    pub brain: Option<Brain>,
    respawn: f64,
    gun_t: f64,
    rounds: u64,
    rng: Rng,
}

impl Dogfight {
    pub fn new(seed: u64, brain: Option<Brain>) -> Dogfight {
        Dogfight {
            brain,
            bandit: None,
            bullets: Vec::new(),
            fx: Vec::new(),
            player_hits: 0,
            player_dead: false,
            kills: 0,
            since_hit: f64::INFINITY,
            since_kill: f64::INFINITY,
            kill_msg: "",
            respawn: FIRST_SPAWN,
            gun_t: 0.0,
            rounds: 0,
            rng: Rng::new(seed ^ 0xD06F),
        }
    }

    /// One 20 ms tick, after the player's sim has ticked from `player_prev` to `player`.
    pub fn tick(&mut self, w: &World, player_prev: &State, player: &State, trigger: bool) {
        let dt = DT_F;
        if self.player_dead {
            return;
        }
        if self.bandit.is_none() {
            if let Some(br) = &mut self.brain {
                br.rest();
            }
            self.respawn -= dt;
            if self.respawn <= 0.0 {
                self.bandit = Some(Bandit::spawn(w, player, &mut self.rng));
            }
        }

        // Guns.
        self.gun_t -= dt;
        if trigger && self.gun_t <= 1e-9 {
            self.gun_t = FIRE_INTERVAL;
            self.fire(player, true);
        }
        if let Some(mut b) = self.bandit.take() {
            let shoot = b.steer(w, player, dt, self.brain.as_mut());
            b.fly();
            b.gun_t -= dt;
            if shoot && b.gun_t <= 1e-9 {
                b.gun_t = FIRE_INTERVAL;
                let s = b.s;
                self.fire(&s, false);
            }
            self.bandit = Some(b);
        }

        // Bullets: swept against the target's motion over the tick, then against the city.
        let bandit_seg = self.bandit.as_ref().map(|b| (pos(&b.prev), pos(&b.s)));
        let player_seg = (pos(player_prev), pos(player));
        let mut hits: Vec<(bool, [f64; 3])> = Vec::new();
        let mut impacts: Vec<[f64; 3]> = Vec::new();
        self.bullets.retain_mut(|b| {
            let p0 = b.p;
            b.v[2] -= G * dt;
            b.p = add(p0, mul(b.v, dt));
            b.age += dt;
            let target = if b.player { bandit_seg } else { Some(player_seg) };
            if let Some((q0, q1)) = target {
                let (d, c) = seg_origin(sub(p0, q0), sub(b.p, q1));
                if d < HIT_R {
                    hits.push((b.player, add(q1, mul(c, 0.4))));
                    return false;
                }
            }
            let off = b.p[0].abs() > MAP_HALF || b.p[1].abs() > MAP_HALF;
            if !off && (b.p[2] < w.terrain(b.p[0], b.p[1]) || w.seg_building_dist(p0, b.p, 0.3) < 0.3) {
                impacts.push(b.p);
                return false;
            }
            !off && b.age < BULLET_LIFE
        });
        for p in impacts {
            self.puff(FxKind::Dust, p, [0.0, 0.0, 1.0], 1.2, 1.5, 0.3);
            self.puff(FxKind::Spark, p, [0.0; 3], 0.08, 0.8, 0.0);
        }
        for (on_bandit, p) in hits {
            let v = if on_bandit { self.bandit.as_ref().map_or([0.0; 3], |b| vel(&b.s)) } else { vel(player) };
            self.puff(FxKind::Spark, p, mul(v, 0.9), 0.1, 1.4, 0.0);
            self.puff(FxKind::Smoke, p, mul(v, 0.3), 1.5, 1.2, 0.6);
            if on_bandit {
                if let Some(b) = &mut self.bandit {
                    b.hits += 1;
                }
            } else {
                self.player_hits += 1;
                self.since_hit = 0.0;
            }
        }

        // Kills: shot down, flown into the city, or a midair.
        if let Some(b) = &self.bandit {
            let (s, h) = (b.s, b.hits);
            let midair = norm(sub(pos(&s), pos(player))) < 2.0 * HIT_R;
            let crashed = w.true_clearance(pos(&s)) < 0.0;
            if h >= HITS_TO_KILL || crashed || midair {
                self.kill_msg = if h >= HITS_TO_KILL { "FLY SWATTED" } else if midair { "MIDAIR" } else { "FLY CRASHED" };
                self.explode(&s);
                self.bandit = None;
                self.kills += 1;
                self.since_kill = 0.0;
                self.respawn = RESPAWN;
                if midair {
                    self.kill_player(player);
                }
            }
        }
        if self.player_hits >= HITS_TO_KILL && !self.player_dead {
            self.kill_player(player);
        }

        // Damage smoke from both aircraft, thicker and darker with hits; fire past 60%.
        let mut smokers = vec![(*player, self.player_hits)];
        if let Some(b) = &self.bandit {
            smokers.push((b.s, b.hits));
        }
        for (s, h) in smokers {
            if h == 0 || (self.player_dead && s == *player) {
                continue;
            }
            let dmg = (h as f64 / HITS_TO_KILL as f64).min(1.0);
            let (p, f, v) = (pos(&s), dir(&s), vel(&s));
            if self.rng.chance((6.0 + 40.0 * dmg) * dt) {
                let q = add(p, mul(f, -2.0));
                let pv = add(mul(v, 0.15), mul(rand_dir(&mut self.rng), 0.8));
                let life = self.rng.range(2.5, 4.5);
                self.puff(FxKind::Smoke, q, pv, 0.8 + 1.4 * dmg, life, 0.25 + 0.75 * dmg);
            }
            if dmg > 0.6 && self.rng.chance(35.0 * dt) {
                let q = add(p, mul(f, 1.5));
                let pv = add(mul(v, 0.6), mul(rand_dir(&mut self.rng), 1.5));
                let life = self.rng.range(0.25, 0.5);
                self.puff(FxKind::Fire, q, pv, 1.0, life, 0.0);
            }
        }
    }

    /// The player is shot down or flew into the city: explode, and stop everything but the effects.
    pub fn kill_player(&mut self, s: &State) {
        if !self.player_dead {
            self.player_dead = true;
            self.bullets.clear();
            self.explode(s);
        }
    }

    /// Advance the effects by a frame (also while the flight is over, so explosions finish).
    pub fn fx_step(&mut self, w: &World, dt: f64) {
        self.since_hit += dt;
        self.since_kill += dt;
        let mut trail = Vec::new();
        for f in &mut self.fx {
            f.age += dt;
            match f.kind {
                FxKind::Debris => {
                    f.v[2] -= G * dt;
                    if f.p[2] < w.terrain(f.p[0], f.p[1]) {
                        f.v = [0.0; 3];
                    } else if self.rng.chance(25.0 * dt) {
                        trail.push(f.p);
                    }
                }
                FxKind::Smoke | FxKind::Dust => {
                    f.v = mul(f.v, (-0.8 * dt).exp());
                    f.v[2] += 0.6 * dt;
                }
                FxKind::Fire => {
                    f.v = mul(f.v, (-2.5 * dt).exp());
                    f.v[2] += 3.0 * dt;
                }
                FxKind::Flash | FxKind::Spark => {}
            }
            f.p = add(f.p, mul(f.v, dt));
        }
        for p in trail {
            let life = self.rng.range(1.5, 3.0);
            self.puff(FxKind::Smoke, p, [0.0, 0.0, 1.0], 0.6, life, 0.8);
        }
        self.fx.retain(|f| f.age < f.life);
        if self.fx.len() > 4000 {
            self.fx.drain(..self.fx.len() - 4000);
        }
    }

    fn fire(&mut self, s: &State, player: bool) {
        self.rounds += 1;
        let spread = if player { 0.003 } else { 0.006 };
        let f = dir(s);
        let d = add(f, mul(rand_dir(&mut self.rng), self.rng.range(0.0, spread)));
        let d = mul(d, 1.0 / norm(d));
        let p = add(pos(s), mul(f, 4.0));
        self.bullets.push(Bullet { p, v: add(vel(s), mul(d, MUZZLE_V)), age: 0.0, player, tracer: self.rounds % 3 == 0 });
        self.puff(FxKind::Flash, p, vel(s), 0.9, 0.05, 0.0);
    }

    fn explode(&mut self, s: &State) {
        let (p, v) = (pos(s), vel(s));
        self.puff(FxKind::Flash, p, mul(v, 0.3), 14.0, 0.3, 0.0);
        for _ in 0..28 {
            let pv = add(mul(v, 0.3), mul(rand_dir(&mut self.rng), self.rng.range(5.0, 35.0)));
            let (size, life) = (self.rng.range(3.0, 6.0), self.rng.range(0.5, 1.4));
            self.puff(FxKind::Fire, p, pv, size, life, 0.0);
        }
        for _ in 0..20 {
            let pv = add(add(mul(v, 0.2), mul(rand_dir(&mut self.rng), self.rng.range(2.0, 12.0))), [0.0, 0.0, 3.0]);
            let (size, life) = (self.rng.range(4.0, 8.0), self.rng.range(4.0, 8.0));
            self.puff(FxKind::Smoke, p, pv, size, life, 0.85);
        }
        for _ in 0..16 {
            let pv = add(add(mul(v, 0.6), mul(rand_dir(&mut self.rng), self.rng.range(10.0, 40.0))), [0.0, 0.0, 10.0]);
            let (size, life) = (self.rng.range(0.4, 1.2), self.rng.range(2.5, 4.0));
            self.puff(FxKind::Debris, p, pv, size, life, 0.0);
        }
    }

    fn puff(&mut self, kind: FxKind, p: [f64; 3], v: [f64; 3], size: f64, life: f64, shade: f64) {
        self.fx.push(Puff { kind, p, v, age: 0.0, life, size, shade });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bandit dead ahead, on the player's flight path and flying the same way, is hit by a burst.
    #[test]
    fn burst_hits_target_ahead() {
        let w = World::new(1337);
        let player = trimmed(0.0, 0.0, 700.0, 50.0, 0.0, 0.0, 0.7);
        let mut df = Dogfight::new(1, None);
        let mut b = Bandit::spawn(&w, &player, &mut Rng::new(3));
        b.s = trimmed(250.0, 0.0, 700.0, 50.0, 0.0, 0.0, 0.7);
        b.prev = b.s;
        df.bandit = Some(b);
        let mut s = player;
        for _ in 0..50 {
            let prev = s;
            rk4(&Params::nominal(), &mut s, DT_F, &[0.0; 3], |_, _| [1.0, 0.0, 0.7]);
            df.tick(&w, &prev, &s, true);
        }
        let hits = df.bandit.as_ref().map_or(HITS_TO_KILL, |b| b.hits);
        assert!(hits >= 5, "only {hits} hits");
    }

    /// The bandit spawns clear of the city and does not fly into it in a minute of chasing a circling player.
    #[test]
    fn bandit_chases_without_crashing() {
        let w = World::new(1337);
        let mut df = Dogfight::new(2, None);
        let mut s = trimmed(0.0, 0.0, 500.0, 50.0, 0.0, 0.0, 0.7);
        let mut fbw = Fbw::from_state(&s);
        fbw.phi_ref = 30f64.to_radians();
        let prm = Params::nominal();
        let mut closest = f64::INFINITY;
        for _ in 0..3000 {
            let prev = s;
            for _ in 0..STEPS_PER_TICK {
                rk4(&prm, &mut s, DT, &[0.0; 3], |st, _| fbw.cmd(&prm, st));
            }
            df.tick(&w, &prev, &s, false);
            if let Some(b) = &df.bandit {
                closest = closest.min(norm(sub(pos(&b.s), pos(&s))));
            }
        }
        assert!(df.kills == 0, "bandit went down: {}", df.kill_msg);
        assert!(closest < GUN_RANGE, "bandit never got within gun range (closest {closest:.0} m)");
    }
}
