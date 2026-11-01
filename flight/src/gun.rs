//! Cosmetic machine guns: two wing guns that fire while the trigger is held (Shift, the HOTAS trigger,
//! `--fire`), with tracers, muzzle flashes, and sparks, dust or spray where the rounds hit.
//!
//! Drawn only. `App::update_guns` steps them once per frame from the aircraft as drawn, outside
//! `Sim::tick`. They read the world's collision geometry (the exact building distances and the true
//! terrain the crash check flies against) and write nothing back, so the simulation, the pilot, the
//! safety filter and the harness are the same with or without them.

use crate::photo;
use cityflight::model::G;
use cityflight::world::{MapId, Rng, World, SF_WATER};
use macroquad::prelude::*;

/// Rounds a second from each gun: 800 a minute, a .50 calibre M2's cyclic rate.
pub const RATE: f64 = 800.0 / 60.0;
/// Muzzle velocity (m/s), on top of the aircraft's.
pub const MUZZLE_V: f32 = 870.0;
/// Every third round is a tracer. Odd, so with the guns taking turns each gun's every third round is one.
pub const TRACER_EVERY: u64 = 3;
/// Seconds a round is followed; a tracer fades out over the last `FADE`.
pub const LIFE: f32 = 2.4;
const FADE: f32 = 0.5;
/// Muzzles in body axes (x forward, y left, z up from the CG, as in `c172.rs`): just ahead of each
/// wing's leading edge, inboard of the strut.
pub const MUZZLES: [Vec3; 2] = [Vec3::new(0.75, 2.2, 0.95), Vec3::new(0.75, -2.2, 0.95)];
/// The guns are toed in to cross on the centreline this far ahead (m).
const CONVERGE: f32 = 350.0;
/// Round-to-round dispersion: half-angle of the cone (rad).
const SPREAD: f32 = 0.003;
/// A muzzle flash lasts this long (s).
const FLASH: f32 = 0.03;
/// A tracer is drawn over the path it covered in this long (s), like a camera's shutter.
const STREAK: f32 = 1.0 / 40.0;
/// Glows closer than this to the camera (m) are clipped.
const NEAR: f32 = 0.6;

// Light, as scene-linear HDR radiance for the photoreal renderer (the nav lights are ~3, the strobe 60).
const TRACER_CORE: [f32; 3] = [36.0, 12.0, 3.0];
const TRACER_HALO: [f32; 3] = [8.0, 1.2, 0.3];
const FLASH_CORE: [f32; 3] = [60.0, 38.0, 12.0];
const FLASH_HALO: [f32; 3] = [6.0, 3.0, 0.7];
const HIT_FLASH: [f32; 3] = [40.0, 26.0, 9.0];
const SPARK: [f32; 3] = [28.0, 10.0, 2.0];

/// The guns' firing cycle: while the trigger is held a round every `1 / rate` s, the first as soon as the
/// mechanism is ready (at once after a pause, never sooner than the rate allows after a short burst).
#[derive(Clone, Copy, Debug, Default)]
pub struct Cycle {
    /// Seconds from now until the next round can fire (0: ready).
    wait: f64,
}

impl Cycle {
    /// Run for `dt` seconds. For each round fired, how long before the end of the step it fired, oldest first.
    pub fn run(&mut self, held: bool, dt: f64, rate: f64) -> Vec<f64> {
        let mut fired = Vec::new();
        let mut t = self.wait;
        if held {
            while t < dt {
                fired.push(dt - t);
                t += 1.0 / rate;
            }
        }
        self.wait = (t - dt).max(0.0);
        fired
    }
}

/// A round in flight (world metres, m/s).
#[derive(Clone, Copy, Debug)]
pub struct Round {
    pub p: Vec3,
    pub v: Vec3,
    pub age: f32,
    pub tracer: bool,
}

impl Round {
    /// Fly `dt` seconds under gravity; drag is left out over a round's short life, so this is exact for any step.
    pub fn advance(&mut self, dt: f32) {
        let g = G as f32;
        self.p += self.v * dt - vec3(0.0, 0.0, 0.5 * g * dt * dt);
        self.v.z -= g * dt;
        self.age += dt;
    }
}

/// What a round hit.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Surface {
    /// Anything the aircraft can crash into above the ground: buildings, bridges, freeway curtains.
    Building,
    Ground,
    /// San Francisco's bay and ocean.
    Water,
}

impl Surface {
    /// How long the dust or spray of a hit hangs in the air (s).
    fn life(self) -> f32 {
        match self {
            Surface::Building => 0.9,
            Surface::Ground => 1.4,
            Surface::Water => 1.2,
        }
    }
}

fn d3(p: Vec3) -> [f64; 3] {
    [p.x as f64, p.y as f64, p.z as f64]
}

/// The last `t` in `[lo, hi]` before `inside` turns true (false at `lo`, true at `hi`).
fn bisect(mut lo: f32, mut hi: f32, inside: impl Fn(f32) -> bool) -> f32 {
    for _ in 0..14 {
        let m = 0.5 * (lo + hi);
        if inside(m) {
            hi = m;
        } else {
            lo = m;
        }
    }
    lo
}

/// Where the segment `a`-`b` first meets a building or the ground: the point just short of the surface,
/// the outward normal there, and what it is. Buildings use the exact segment distance
/// (`World::seg_building_dist`), the ground the true terrain (`World::terrain`).
pub fn first_hit(w: &World, a: Vec3, b: Vec3) -> Option<(Vec3, Vec3, Surface)> {
    let at = |t: f32| a.lerp(b, t);
    let below = |t: f32| {
        let p = at(t);
        p.z as f64 <= w.terrain(p.x as f64, p.y as f64)
    };
    // The ground: samples 4 m apart (the terrain mesh is 20 m), then the crossing.
    let n = ((b - a).length() / 4.0).ceil().max(1.0);
    let ground = (1..=n as usize).map(|k| k as f32 / n).find(|&t| below(t)).map(|t| bisect(t - 1.0 / n, t, below));
    // Buildings, up to where it meets the ground.
    let end = ground.unwrap_or(1.0);
    let touches = |t: f32| w.seg_building_dist(d3(a), d3(at(t)), 0.01) < 0.01;
    if touches(end) {
        let p = at(bisect(0.0, end, touches));
        return Some((p, building_normal(w, p, (b - a).normalize_or_zero()), Surface::Building));
    }
    let p = at(ground?);
    let h = |dx: f64, dy: f64| w.terrain(p.x as f64 + dx, p.y as f64 + dy);
    let n = vec3(((h(-1.0, 0.0) - h(1.0, 0.0)) * 0.5) as f32, ((h(0.0, -1.0) - h(0.0, 1.0)) * 0.5) as f32, 1.0).normalize();
    let water = w.map == MapId::SanFrancisco && h(0.0, 0.0) <= SF_WATER + 0.05;
    Some((p, n, if water { Surface::Water } else { Surface::Ground }))
}

/// Outward normal of the building surface hit at `p` coming along `dir`: the gradient of the distance to
/// buildings half a metre back along the path, or straight back along the path if that is too close to tell.
fn building_normal(w: &World, p: Vec3, dir: Vec3) -> Vec3 {
    let q = d3(p - dir * 0.5);
    let d = |o: [f64; 3]| w.building_dist([q[0] + o[0], q[1] + o[1], q[2] + o[2]], 2.0);
    let h = (d([0.0; 3]) * 0.5).min(0.1);
    if h < 0.005 {
        return -dir;
    }
    let g = vec3((d([h, 0.0, 0.0]) - d([-h, 0.0, 0.0])) as f32, (d([0.0, h, 0.0]) - d([0.0, -h, 0.0])) as f32, (d([0.0, 0.0, h]) - d([0.0, 0.0, -h])) as f32);
    g.try_normalize().unwrap_or(-dir)
}

/// A random unit vector.
fn unit(rng: &mut Rng) -> Vec3 {
    let z = rng.range(-1.0, 1.0) as f32;
    let a = rng.range(0.0, std::f64::consts::TAU) as f32;
    let r = (1.0 - z * z).sqrt();
    vec3(r * a.cos(), r * a.sin(), z)
}

/// Where the guns are this frame: the drawn aircraft's position, body axes (forward, left, up) and velocity.
#[derive(Clone, Copy, Debug)]
pub struct Mount {
    pub p: Vec3,
    pub axes: (Vec3, Vec3, Vec3),
    pub vel: Vec3,
}

impl Mount {
    fn rot(&self, q: Vec3) -> Vec3 {
        let (f, l, u) = self.axes;
        f * q.x + l * q.y + u * q.z
    }
    fn muzzle(&self, k: usize) -> Vec3 {
        self.p + self.rot(MUZZLES[k])
    }
    /// Gun `k`'s bore: along the nose, toed in to cross the centreline at `CONVERGE`.
    fn bore(&self, k: usize) -> Vec3 {
        self.rot(vec3(CONVERGE, 0.0, 0.0) - MUZZLES[k]).normalize()
    }
}

#[derive(Clone, Copy, Debug)]
struct Hit {
    p: Vec3,
    n: Vec3,
    on: Surface,
    /// The round's direction of travel.
    dir: Vec3,
}

#[derive(Clone, Copy, Debug)]
struct Impact {
    p: Vec3,
    n: Vec3,
    on: Surface,
    age: f32,
}

#[derive(Clone, Copy, Debug)]
struct Spark {
    p: Vec3,
    v: Vec3,
    age: f32,
    life: f32,
}

/// Fly a round for `dt`; false once it is spent (hit something, left the map, burnt out). Hits go to `hits`.
fn fly(w: &World, r: &mut Round, dt: f32, hits: &mut Vec<Hit>) -> bool {
    let a = r.p;
    r.advance(dt);
    if let Some((p, n, on)) = first_hit(w, a, r.p) {
        hits.push(Hit { p, n, on, dir: r.v.normalize_or_zero() });
        return false;
    }
    r.age < LIFE && w.inside(r.p.x as f64, r.p.y as f64)
}

pub struct Guns {
    cycle: Cycle,
    /// Rounds fired since the last reset (they alternate between the guns; every `TRACER_EVERY`th is a tracer).
    fired: u64,
    rounds: Vec<Round>,
    impacts: Vec<Impact>,
    sparks: Vec<Spark>,
    /// Per gun: seconds since it last fired, and that flash's size and roll.
    flash: [(f32, f32, f32); 2],
    /// The aircraft at the last update, for the muzzle flashes.
    mount: Option<Mount>,
    rng: Rng,
}

impl Guns {
    pub fn new() -> Guns {
        Guns {
            cycle: Cycle::default(),
            fired: 0,
            rounds: Vec::new(),
            impacts: Vec::new(),
            sparks: Vec::new(),
            flash: [(f32::INFINITY, 1.0, 0.0); 2],
            mount: None,
            rng: Rng::new(0x6A11),
        }
    }

    /// Drop everything in flight (reset, new scenario, other map).
    pub fn clear(&mut self) {
        *self = Guns::new();
    }

    /// One frame of `dt` s: fire while `held`, fly the rounds, turn hits into impacts, age the effects.
    pub fn update(&mut self, w: &World, held: bool, dt: f32, m: &Mount) {
        for f in &mut self.flash {
            f.0 += dt;
        }
        let mut hits = Vec::new();
        self.rounds.retain_mut(|r| fly(w, r, dt, &mut hits));
        // New rounds, each from where its muzzle was when it fired.
        for ago in self.cycle.run(held, dt as f64, 2.0 * RATE) {
            let ago = ago as f32;
            let k = (self.fired % 2) as usize;
            let tracer = self.fired % TRACER_EVERY == 0;
            self.fired += 1;
            let dir = (m.bore(k) + unit(&mut self.rng) * SPREAD * self.rng.f() as f32).normalize();
            let mut r = Round { p: m.muzzle(k) - m.vel * ago, v: m.vel + dir * MUZZLE_V, age: 0.0, tracer };
            if fly(w, &mut r, ago, &mut hits) {
                self.rounds.push(r);
            }
            self.flash[k] = (ago, self.rng.range(0.8, 1.25) as f32, self.rng.range(0.0, std::f64::consts::TAU) as f32);
        }
        for h in hits {
            self.impact(h);
        }
        for i in &mut self.impacts {
            i.age += dt;
        }
        self.impacts.retain(|i| i.age < i.on.life());
        for s in &mut self.sparks {
            s.p += s.v * dt;
            s.v = s.v * (-3.0 * dt).exp() - vec3(0.0, 0.0, G as f32 * dt);
            s.age += dt;
        }
        self.sparks.retain(|s| s.age < s.life);
        self.mount = Some(*m);
    }

    /// A hit: dust or spray, and on buildings and the ground, sparks thrown off around the ricochet.
    fn impact(&mut self, h: Hit) {
        self.impacts.push(Impact { p: h.p, n: h.n, on: h.on, age: 0.0 });
        let (count, speed) = match h.on {
            Surface::Building => (5, 45.0),
            Surface::Ground => (2, 20.0),
            Surface::Water => (0, 0.0),
        };
        let bounce = h.dir - h.n * 2.0 * h.dir.dot(h.n);
        for _ in 0..count {
            let d = (bounce * 0.6 + h.n * 0.5 + unit(&mut self.rng) * 0.6).normalize_or(h.n);
            let v = d * speed * self.rng.range(0.4, 1.0) as f32;
            self.sparks.push(Spark { p: h.p + h.n * 0.05, v, age: 0.0, life: self.rng.range(0.15, 0.45) as f32 });
        }
    }

    /// Everything to draw this frame.
    fn sprites(&self, v: &View) -> Vec<Sprite> {
        let mut out = Vec::new();
        // A glow at least `px` of about two pixels wide at its distance.
        let mut glow = |a: Vec3, b: Vec3, r: f32, px: f32, hdr: [f32; 3], alpha: f32| {
            out.push(Sprite::Glow { a, b, r: r.max(px * v.px(b)), hdr, alpha });
        };
        for r in self.rounds.iter().filter(|r| r.tracer) {
            let fade = ((LIFE - r.age) / FADE).min(1.0);
            let tail = r.p - r.v * r.age.min(STREAK);
            glow(tail, r.p, 0.3, 2.5, TRACER_HALO, 0.4 * fade);
            glow(tail, r.p, 0.08, 1.0, TRACER_CORE, fade);
        }
        if let Some(m) = &self.mount {
            for (k, &(t, size, roll)) in self.flash.iter().enumerate() {
                if t >= FLASH {
                    continue;
                }
                let a = 1.0 - t / FLASH;
                let (mz, dir) = (m.muzzle(k), m.bore(k));
                // A flame along the bore and a four-pointed star across it, turned a little each shot.
                let (s, c) = roll.sin_cos();
                let (_, l, u) = m.axes;
                let (p1, p2) = ((l * c + u * s) * 0.3 * size, (u * c - l * s) * 0.3 * size);
                glow(mz + dir * 0.3, mz + dir * 0.3, 0.6 * size, 3.0, FLASH_HALO, 0.6 * a);
                glow(mz, mz + dir * 1.0 * size, 0.14 * size, 1.5, FLASH_CORE, a);
                glow(mz - p1, mz + p1, 0.05 * size, 1.0, FLASH_CORE, a);
                glow(mz - p2, mz + p2, 0.05 * size, 1.0, FLASH_CORE, a);
            }
        }
        for s in &self.sparks {
            glow(s.p - s.v / 60.0, s.p, 0.05, 0.7, SPARK, 1.0 - s.age / s.life);
        }
        for i in &self.impacts {
            if i.age < 0.06 {
                let q = i.p + i.n * 0.2;
                glow(q, q, if i.on == Surface::Building { 0.9 } else { 0.6 }, 3.0, HIT_FLASH, 1.0 - i.age / 0.06);
            }
        }
        // Dust or spray: grows, drifts off the surface and rises, thins out.
        for i in &self.impacts {
            let fade = (1.0 - i.age / i.on.life()).powi(2);
            let grow = 1.0 - (-i.age * 5.0).exp();
            let (r0, r1, rgb, a0, rise) = match i.on {
                Surface::Building => (0.4, 3.0, [0.62, 0.60, 0.57], 0.55, 0.8),
                Surface::Ground => (0.6, 4.5, [0.56, 0.48, 0.37], 0.6, 1.2),
                Surface::Water => (0.5, 2.5, [0.93, 0.95, 0.97], 0.7, 0.4),
            };
            let c = i.p + i.n * (0.3 + 1.5 * grow) + Vec3::Z * rise * i.age;
            out.push(Sprite::Puff { c, r: r0 + (r1 - r0) * grow, rgba: [rgb[0], rgb[1], rgb[2], a0 * fade] });
            if i.on == Surface::Water {
                // The plume thrown up, falling back.
                let up = (9.0 * i.age - 0.5 * G as f32 * i.age * i.age).max(0.0);
                out.push(Sprite::Puff { c: i.p + Vec3::Z * (0.5 + up), r: 0.4 + 1.2 * grow, rgba: [rgb[0], rgb[1], rgb[2], 0.8 * fade] });
            }
        }
        out
    }

    /// Light and dust for the photoreal renderer's overlay pass: light as glow sprites (HDR, they bloom),
    /// dust as soft discs in display colour.
    pub fn photo(&self, ov: &mut Vec<photo::DV>, oi: &mut Vec<u32>, v: &View) {
        let mut sp: Vec<(f32, Sprite)> = self.sprites(v).into_iter().map(|s| (v.depth(s.centre()), s)).collect();
        // Dust is blended in order (back to front); light adds on top.
        sp.sort_by(|a, b| a.1.is_glow().cmp(&b.1.is_glow()).then(b.0.total_cmp(&a.0)));
        for (_, s) in sp {
            match s {
                Sprite::Glow { a, b, r, hdr, alpha } => {
                    let Some((c, x, y)) = v.billboard(a, b, r) else { continue };
                    let base = ov.len() as u32;
                    for (sx, sy) in [(-1.0f32, -1.0f32), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)] {
                        let p = c + x * sx + y * sy;
                        ov.push(photo::DV { pos: p.to_array(), nrm: [0.0; 3], col: [hdr[0], hdr[1], hdr[2], alpha], mat: [7.0, 0.0, 0.0, 0.0], loc: [sx, sy, 0.0, 0.0] });
                    }
                    oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
                }
                Sprite::Puff { c, r, rgba } => {
                    let Some((c, x, y)) = v.billboard(c, c, r) else { continue };
                    let col = [0, 1, 2].map(|k| photo::display_to_scene(rgba[k], 1.0));
                    let dv = |p: Vec3, a: f32| photo::DV { pos: p.to_array(), nrm: [0.0; 3], col: [col[0], col[1], col[2], a], mat: [photo::K_OVERLAY, 0.0, 0.0, 0.0], loc: [0.0; 4] };
                    let base = ov.len() as u32;
                    ov.push(dv(c, rgba[3]));
                    for k in 0..PUFF_SEGS {
                        let t = k as f32 / PUFF_SEGS as f32 * std::f32::consts::TAU;
                        ov.push(dv(c + x * t.cos() + y * t.sin(), 0.0));
                        oi.extend_from_slice(&[base, base + 1 + k, base + 1 + (k + 1) % PUFF_SEGS]);
                    }
                }
            }
        }
    }

    /// The same for the classic renderer, through macroquad (after the aircraft: these write depth).
    pub fn draw(&self, v: &View) {
        // Back to front, by the plane each is drawn on, so a nearer one is never cut by a farther one's quad.
        let mut sp: Vec<(f32, Sprite, (Vec3, Vec3, Vec3))> = self
            .sprites(v)
            .into_iter()
            .filter_map(|s| {
                let (a, b, r) = match s {
                    Sprite::Glow { a, b, r, .. } => (a, b, r),
                    Sprite::Puff { c, r, .. } => (c, c, r),
                };
                v.billboard(a, b, r).map(|q| (v.depth(q.0), s, q))
            })
            .collect();
        sp.sort_by(|a, b| b.0.total_cmp(&a.0));
        let mut batch = Batch::default();
        for (_, s, (c, x, y)) in sp {
            let (col, alpha, round) = match s {
                Sprite::Glow { hdr, alpha, .. } => (Color::new(ldr(hdr[0]), ldr(hdr[1]), ldr(hdr[2]), 1.0), alpha, x.length() < y.length() * 1.05),
                Sprite::Puff { rgba, .. } => (Color::new(rgba[0], rgba[1], rgba[2], 1.0), rgba[3], true),
            };
            let vx = |p: Vec3, a: f32| Vertex::new(p.x, p.y, p.z, 0.0, 0.0, Color { a: alpha * a, ..col });
            if round {
                // A disc fading from the centre.
                let mut vs = vec![vx(c, 1.0)];
                let mut is = Vec::new();
                for k in 0..PUFF_SEGS as u16 {
                    let t = k as f32 / PUFF_SEGS as f32 * std::f32::consts::TAU;
                    vs.push(vx(c + x * t.cos() + y * t.sin(), 0.0));
                    is.extend_from_slice(&[0, 1 + k, 1 + (k + 1) % PUFF_SEGS as u16]);
                }
                batch.add(&vs, &is);
            } else {
                // A streak: solid along its middle, fading to its ends and sides.
                let (along, wa) = ([-1.0f32, -0.35, 0.35, 1.0], [0.0f32, 1.0, 1.0, 0.0]);
                let mut vs = Vec::with_capacity(12);
                for (s, w) in along.iter().zip(wa) {
                    for (t, wt) in [(-1.0f32, 0.0f32), (0.0, 1.0), (1.0, 0.0)] {
                        vs.push(vx(c + x * *s + y * t, w * wt));
                    }
                }
                let mut is = Vec::with_capacity(36);
                for i in 0..3u16 {
                    for j in 0..2u16 {
                        let q = i * 3 + j;
                        is.extend_from_slice(&[q, q + 3, q + 4, q, q + 4, q + 1]);
                    }
                }
                batch.add(&vs, &is);
            }
        }
        batch.flush();
    }
}

const PUFF_SEGS: u32 = 12;

/// HDR light to a display colour for the classic renderer (a soft exposure curve: bright cores go white-hot).
fn ldr(c: f32) -> f32 {
    1.0 - (-0.12 * c).exp()
}

/// Something to draw: light (tracer, flash, spark) as a glow over the segment `a`-`b` (a dot when they
/// meet), `r` wide, in HDR scene-linear colour; or a soft disc of dust or spray in display colour.
enum Sprite {
    Glow { a: Vec3, b: Vec3, r: f32, hdr: [f32; 3], alpha: f32 },
    Puff { c: Vec3, r: f32, rgba: [f32; 4] },
}

impl Sprite {
    fn is_glow(&self) -> bool {
        matches!(self, Sprite::Glow { .. })
    }
    fn centre(&self) -> Vec3 {
        match *self {
            Sprite::Glow { a, b, .. } => 0.5 * (a + b),
            Sprite::Puff { c, .. } => c,
        }
    }
}

/// The camera, for camera-facing sprites.
pub struct View {
    pub pos: Vec3,
    /// Unit forward, right and up.
    pub fwd: Vec3,
    pub right: Vec3,
    pub up: Vec3,
}

impl View {
    pub fn of(cam: &Camera3D) -> View {
        let fwd = (cam.target - cam.position).normalize();
        let right = fwd.cross(cam.up).normalize();
        View { pos: cam.position, fwd, right, up: right.cross(fwd) }
    }

    fn depth(&self, p: Vec3) -> f32 {
        (p - self.pos).dot(self.fwd)
    }

    /// About two pixels at `p`'s distance (m).
    fn px(&self, p: Vec3) -> f32 {
        self.depth(p).max(0.0) * 0.001
    }

    /// A camera-facing quad over the segment `a`-`b`, widened by `r` all round: its centre and its half
    /// extents along and across the segment as seen. It lies square to the view, pulled up to `r` toward
    /// the camera so a wall it sits on doesn't cut it, and scaled so it covers the same pixels; a segment
    /// seen end-on becomes a dot. `None` if it is all behind the camera.
    fn billboard(&self, a: Vec3, b: Vec3, r: f32) -> Option<(Vec3, Vec3, Vec3)> {
        let (da, db) = (self.depth(a), self.depth(b));
        if da < NEAR && db < NEAR {
            return None;
        }
        let clip = |p: Vec3, dp: f32, q: Vec3, dq: f32| if dp < NEAR { p + (q - p) * ((NEAR - dp) / (dq - dp)) } else { p };
        let (a, b) = (clip(a, da, b, db), clip(b, db, a, da));
        let dm = self.depth(0.5 * (a + b));
        let plane = (dm - r).max(0.5 * dm).max(NEAR.min(dm));
        let k = plane / dm;
        // Both ends, moved along their lines of sight onto the plane: same place on screen.
        let onto = |p: Vec3| self.pos + (p - self.pos) * (plane / self.depth(p));
        let (a, b) = (onto(a), onto(b));
        let (r, d) = (r * k, b - a);
        let len = d.length();
        let along = if len > 1e-3 * r { d / len } else { self.right };
        let across = along.cross(self.fwd).normalize_or(self.up);
        Some((0.5 * (a + b), along * (0.5 * len + r), across * r))
    }
}

/// Triangles for macroquad, flushed before a draw call would exceed its default capacity (5,000 indices).
#[derive(Default)]
struct Batch {
    v: Vec<Vertex>,
    i: Vec<u16>,
}

impl Batch {
    fn add(&mut self, v: &[Vertex], i: &[u16]) {
        if self.i.len() + i.len() > 4800 || self.v.len() + v.len() > 9600 {
            self.flush();
        }
        let base = self.v.len() as u16;
        self.v.extend_from_slice(v);
        self.i.extend(i.iter().map(|k| k + base));
    }

    fn flush(&mut self) {
        if !self.i.is_empty() {
            draw_mesh(&Mesh { vertices: std::mem::take(&mut self.v), indices: std::mem::take(&mut self.i), texture: None });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycle_fires_at_the_rate_at_any_frame_rate() {
        for fps in [30.0, 60.0, 144.0] {
            let mut c = Cycle::default();
            let n: usize = (0..(2.0 * fps) as usize).map(|_| c.run(true, 1.0 / fps, RATE).len()).sum();
            // Rounds at 0, 0.075, ..., 1.95 s: the first at once.
            assert_eq!(n, 27, "{fps} fps");
        }
        let mut c = Cycle::default();
        assert!(c.run(false, 0.1, 20.0).is_empty());
        let ago = c.run(true, 0.12, 20.0);
        assert_eq!(ago.len(), 3);
        assert!(ago.windows(2).all(|w| (w[0] - w[1] - 0.05).abs() < 1e-9) && (ago[0] - 0.12).abs() < 1e-9);
    }

    #[test]
    fn cycle_waits_out_the_rate_between_bursts() {
        let mut c = Cycle::default();
        assert_eq!(c.run(true, 0.01, 10.0).len(), 1);
        // Released and pressed again within the 0.1 s cycle: the next round waits for it.
        assert!(c.run(false, 0.03, 10.0).is_empty());
        assert!(c.run(true, 0.05, 10.0).is_empty());
        let ago = c.run(true, 0.02, 10.0);
        assert_eq!(ago.len(), 1);
        assert!((ago[0] - 0.01).abs() < 1e-9);
        // After a long pause it fires at once.
        assert!(c.run(false, 1.0, 10.0).is_empty());
        assert_eq!(c.run(true, 0.001, 10.0).len(), 1);
    }

    #[test]
    fn rounds_fall_under_gravity() {
        let mut r = Round { p: vec3(0.0, 0.0, 300.0), v: vec3(MUZZLE_V, 0.0, 0.0), age: 0.0, tracer: true };
        for _ in 0..60 {
            r.advance(1.0 / 60.0);
        }
        assert!((r.p.x - MUZZLE_V).abs() < 0.05 && (r.p.z - (300.0 - 0.5 * G as f32)).abs() < 0.01);
        assert!((r.v.z + G as f32).abs() < 1e-3 && (r.age - 1.0).abs() < 1e-5);
    }

    #[test]
    fn end_on_streaks_are_dots() {
        let v = View { pos: Vec3::ZERO, fwd: Vec3::X, right: -Vec3::Y, up: Vec3::Z };
        // Straight away from the camera: a dot of radius r (the plane pulled in by r, scaled to match).
        let (c, x, y) = v.billboard(vec3(100.0, 0.0, 0.0), vec3(120.0, 0.0, 0.0), 1.0).unwrap();
        let k = 109.0 / 110.0;
        assert!((c - vec3(109.0, 0.0, 0.0)).length() < 1e-3 && (x.length() - k).abs() < 1e-3 && (y.length() - k).abs() < 1e-3);
        assert!(x.dot(v.fwd).abs() < 1e-6 && y.dot(v.fwd).abs() < 1e-6);
        // Across the view: its full length plus r at each end.
        let (_, x, _) = v.billboard(vec3(100.0, -10.0, 0.0), vec3(100.0, 10.0, 0.0), 1.0).unwrap();
        assert!((x.length() - 11.0 * 99.0 / 100.0).abs() < 1e-3);
        assert!(v.billboard(vec3(-5.0, 0.0, 0.0), vec3(0.3, 0.0, 0.0), 1.0).is_none());
    }

    #[test]
    fn rounds_stop_at_buildings_and_the_ground() {
        let w = World::new(1337);
        // At the tallest tower's top tier, from the west: the hit is on its west face, facing back.
        let b = w.boxes[w.tallest];
        let (y, z) = (0.5 * (b.y0 + b.y1) as f32, b.z1 as f32 - 5.0);
        let (p, n, on) = first_hit(&w, vec3(b.x0 as f32 - 40.0, y, z), vec3(b.x0 as f32 + 5.0, y, z)).unwrap();
        assert_eq!(on, Surface::Building);
        assert!((p.x - b.x0 as f32).abs() < 0.02 && n.x < -0.99, "{p} {n}");
        // Straight down outside the city: on the terrain, facing up.
        let (gx, gy) = (2000.0f32, 1900.0f32);
        let g = w.terrain(gx as f64, gy as f64) as f32;
        let (p, n, on) = first_hit(&w, vec3(gx, gy, g + 3.0), vec3(gx, gy, g - 3.0)).unwrap();
        assert!(on == Surface::Ground && (p.z - g).abs() < 0.01 && n.z > 0.5);
        // Into the open sky: nothing.
        assert!(first_hit(&w, vec3(gx, gy, g + 900.0), vec3(gx + 15.0, gy, g + 905.0)).is_none());

        // Holding the trigger at the tower: rounds stop on the face and leave impacts there; none get through.
        let mut guns = Guns::new();
        let mut m = Mount { p: vec3(b.x0 as f32 - 300.0, y, z), axes: (Vec3::X, Vec3::Y, Vec3::Z), vel: Vec3::X * 50.0 };
        for _ in 0..90 {
            m.p += m.vel / 60.0;
            guns.update(&w, true, 1.0 / 60.0, &m);
            assert!(guns.rounds.iter().all(|r| r.p.x < b.x0 as f32));
        }
        assert!(guns.fired >= 39 && guns.impacts.len() > 10);
        assert!(guns.impacts.iter().all(|i| i.on == Surface::Building && (i.p.x - b.x0 as f32).abs() < 0.05));
        // The rounds still in flight when the trigger is let go hit too; then everything fades.
        for _ in 0..240 {
            guns.update(&w, false, 1.0 / 60.0, &m);
        }
        assert!(guns.rounds.is_empty() && guns.impacts.is_empty() && guns.sparks.is_empty());
    }
}
