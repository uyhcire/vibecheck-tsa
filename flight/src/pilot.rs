//! Pilot side: the fly-by-wire law the keyboard drives (release = hold flight
//! path and bank), a hostile random pilot, and a kamikaze autopilot.

use crate::model::*;
use crate::world::{Rng, World};
use std::f64::consts::PI;

pub const FBW_GDOT: f64 = 15.0 * PI / 180.0;
pub const FBW_PDOT: f64 = 45.0 * PI / 180.0;
pub const FBW_G_MIN: f64 = -50.0 * PI / 180.0;
pub const FBW_G_MAX: f64 = 40.0 * PI / 180.0;
pub const FBW_PHI_MAX: f64 = 70.0 * PI / 180.0;
const FBW_KG: f64 = 1.5;
const FBW_KPHI: f64 = 3.0;

#[derive(Clone, Copy, Debug)]
pub struct Fbw {
    pub g_ref: f64,
    pub phi_ref: f64,
    pub thr: f64,
}

impl Fbw {
    pub fn from_state(s: &State) -> Fbw {
        Fbw { g_ref: s[GAM], phi_ref: s[PHI], thr: s[THR] }
    }
    /// `pitch` > 0 = nose up, `roll` > 0 = roll right; both in -1..1.
    pub fn sticks(&mut self, pitch: f64, roll: f64, dt: f64) {
        self.g_ref = (self.g_ref + pitch * FBW_GDOT * dt).clamp(FBW_G_MIN, FBW_G_MAX);
        self.phi_ref = (self.phi_ref - roll * FBW_PDOT * dt).clamp(-FBW_PHI_MAX, FBW_PHI_MAX);
    }
    pub fn cmd(&self, p: &Params, s: &State) -> Cmd {
        let v = s[V].max(5.0);
        let nc = (s[GAM].cos() + v / G * FBW_KG * (self.g_ref - s[GAM])) / s[PHI].cos().max(0.3);
        let pc = (FBW_KPHI * (self.phi_ref - s[PHI])).clamp(-p.p_max, p.p_max);
        [nc.clamp(p.n_min, p.n_max), pc, self.thr.clamp(0.0, 1.0)]
    }
    /// While the filter acts, slide the references toward the actual attitude
    /// so control hands back smoothly. (Pilot-side state only.)
    pub fn resync(&mut self, s: &State, lam: f64, dt: f64) {
        let a = (lam * 5.0 * dt).min(1.0);
        self.g_ref += (s[GAM].clamp(FBW_G_MIN, FBW_G_MAX) - self.g_ref) * a;
        self.phi_ref += (s[PHI].clamp(-FBW_PHI_MAX, FBW_PHI_MAX) - self.phi_ref) * a;
    }
}

/// Random stick, biased nose-down, with random throttle.
pub struct Hostile {
    rng: Rng,
    sp: f64,
    sr: f64,
    timer: f64,
}

impl Hostile {
    pub fn new(seed: u64) -> Self {
        Hostile { rng: Rng::new(seed ^ 0x4057), sp: 0.0, sr: 0.0, timer: 0.0 }
    }
    pub fn update(&mut self, fbw: &mut Fbw, dt: f64) {
        self.timer -= dt;
        if self.timer <= 0.0 {
            let r = &mut self.rng;
            self.sp = if r.chance(0.25) { -1.0 } else { r.range(-1.0, 0.35) };
            self.sr = if r.chance(0.3) { 0.0 } else { r.range(-1.0, 1.0) };
            if r.chance(0.3) {
                fbw.thr = if r.chance(0.3) { 0.0 } else { r.range(0.2, 1.0) };
            }
            self.timer = r.range(0.4, 2.0);
        }
        fbw.sticks(self.sp, self.sr, dt);
    }
}

/// Picks a building or terrain point and flies straight at it.
pub struct Kamikaze {
    rng: Rng,
    pub target: [f64; 3],
    timer: f64,
}

fn wrap(a: f64) -> f64 {
    let mut a = a % (2.0 * PI);
    if a > PI {
        a -= 2.0 * PI;
    }
    if a < -PI {
        a += 2.0 * PI;
    }
    a
}

impl Kamikaze {
    pub fn new(seed: u64) -> Self {
        Kamikaze { rng: Rng::new(seed ^ 0xCA3E), target: [0.0; 3], timer: 0.0 }
    }

    fn pick(&mut self, w: &World, s: &State) {
        let mut best = None;
        let mut best_score = f64::NEG_INFINITY;
        for (n, b) in w.boxes.iter().enumerate() {
            if b.z1 - b.z0 < 25.0 {
                continue;
            }
            let (cx, cy) = (0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1));
            let (dx, dy) = (cx - s[X], cy - s[Y]);
            let d = (dx * dx + dy * dy).sqrt();
            if !(250.0..2500.0).contains(&d) {
                continue;
            }
            let off = wrap(dy.atan2(dx) - s[PSI]).abs();
            let score = (b.z1 - b.z0).ln() - d / 700.0 - off * 0.8 + self.rng.range(0.0, 1.5);
            if score > best_score {
                best_score = score;
                best = Some(n);
            }
        }
        let terrain_pick = best.is_none() || self.rng.chance(0.25);
        if terrain_pick {
            // Dive at the ground (or ridge / rim) some distance ahead.
            let d = self.rng.range(500.0, 1200.0);
            let a = s[PSI] + self.rng.range(-0.6, 0.6);
            let (x, y) = (s[X] + d * a.cos(), s[Y] + d * a.sin());
            self.target = [x, y, w.terrain(x, y)];
        } else {
            let b = &w.boxes[best.unwrap()];
            self.target = [0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1), b.z0 + 0.45 * (b.z1 - b.z0)];
        }
        self.timer = self.rng.range(12.0, 25.0);
    }

    pub fn update(&mut self, w: &World, s: &State, fbw: &mut Fbw, dt: f64) {
        self.timer -= dt;
        let (dx, dy) = (self.target[0] - s[X], self.target[1] - s[Y]);
        let d = (dx * dx + dy * dy).sqrt();
        let off = wrap(dy.atan2(dx) - s[PSI]);
        if self.timer <= 0.0 || d < 60.0 || (off.abs() > 2.2 && d < 400.0) {
            self.pick(w, s);
        }
        let (dx, dy) = (self.target[0] - s[X], self.target[1] - s[Y]);
        let d = (dx * dx + dy * dy).sqrt().max(1.0);
        let off = wrap(dy.atan2(dx) - s[PSI]);
        fbw.phi_ref = (1.4 * off).clamp(-60f64.to_radians(), 60f64.to_radians());
        let g_des = (self.target[2] - s[Z]).atan2(d) - 3f64.to_radians();
        fbw.g_ref = g_des.clamp(-45f64.to_radians(), 20f64.to_radians());
        fbw.thr = 1.0;
    }
}

pub enum Pilot {
    Manual,
    Hostile(Hostile),
    Kamikaze(Kamikaze),
}
