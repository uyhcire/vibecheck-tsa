//! Procedural Cessna 172-style mesh in body axes (x forward, y left, z up, origin at the CG).

use macroquad::prelude::*;

pub const P_FUSELAGE: f32 = 0.0;
pub const P_WING: f32 = 1.0;
pub const P_TAIL: f32 = 2.0;
pub const P_SURFACE: f32 = 3.0;
pub const P_STRUT: f32 = 4.0;
pub const P_FAIRING: f32 = 5.0;
pub const P_TIRE: f32 = 6.0;
pub const P_SPINNER: f32 = 7.0;
pub const P_PROP: f32 = 8.0;
pub const P_PANEL: f32 = 9.0;
pub const P_TRIM: f32 = 10.0;

pub const PROP_X: f32 = 2.30;
pub const PROP_Z: f32 = -0.05;
pub const PROP_R: f32 = 0.95;
/// Pilot's eye (left seat), body axes.
pub const EYE: Vec3 = Vec3::new(0.10, 0.27, 0.74);

#[derive(Clone, Copy, Default)]
pub struct Controls {
    /// Trailing-edge-down deflections in radians; aileron positive rolls right.
    pub elevator: f32,
    pub aileron: f32,
    pub rudder: f32,
}

#[derive(Clone, Copy)]
pub struct AV {
    pub pos: Vec3,
    pub nrm: Vec3,
    pub part: f32,
}

#[derive(Default)]
pub struct Mesh {
    pub v: Vec<AV>,
    pub i: Vec<u32>,
}

impl Mesh {
    fn tri(&mut self, a: Vec3, b: Vec3, c: Vec3, part: f32) {
        let n = (b - a).cross(c - a).normalize_or_zero();
        let base = self.v.len() as u32;
        for p in [a, b, c] {
            self.v.push(AV { pos: p, nrm: n, part });
        }
        self.i.extend_from_slice(&[base, base + 1, base + 2]);
    }
    fn quad(&mut self, a: Vec3, b: Vec3, c: Vec3, d: Vec3, part: f32) {
        self.tri(a, b, c, part);
        self.tri(a, c, d, part);
    }
    fn rings(&mut self, r0: &[(Vec3, Vec3)], r1: &[(Vec3, Vec3)], part: f32) {
        let n = r0.len();
        for k in 0..n {
            let k1 = (k + 1) % n;
            let base = self.v.len() as u32;
            for (p, nn) in [r0[k], r0[k1], r1[k1], r1[k]] {
                self.v.push(AV { pos: p, nrm: nn, part });
            }
            self.i.extend_from_slice(&[base, base + 2, base + 1, base, base + 3, base + 2]);
        }
    }
}

fn superellipse_ring(x: f32, cz: f32, hw: f32, hh: f32, e: f32, segs: usize) -> Vec<(Vec3, Vec3)> {
    (0..segs)
        .map(|k| {
            let t = k as f32 / segs as f32 * std::f32::consts::TAU;
            let (c, s) = (t.cos(), t.sin());
            let f = |v: f32| v.signum() * v.abs().powf(2.0 / e);
            let p = vec3(x, hw * f(c), cz + hh * f(s));
            let nrm = vec3(0.0, f(c) / hw.max(1e-3), f(s) / hh.max(1e-3)).normalize_or_zero();
            (p, nrm)
        })
        .collect()
}

fn airfoil(m: &mut Mesh, le0: Vec3, te0: Vec3, le1: Vec3, te1: Vec3, up: Vec3, tc: f32, part: f32) {
    const PROF: [(f32, f32); 7] = [(0.0, 0.0), (0.05, 0.6), (0.15, 0.95), (0.3, 1.0), (0.55, 0.8), (0.8, 0.45), (1.0, 0.05)];
    let section = |le: Vec3, te: Vec3| -> Vec<(Vec3, Vec3)> {
        let ch = (te - le).length();
        let fwd = (le - te).normalize();
        let mut pts = Vec::new();
        for &(u, t) in PROF.iter() {
            pts.push((le + (te - le) * u + up * (t * tc * ch * 0.62), up));
        }
        for &(u, t) in PROF.iter().rev().skip(1).take(PROF.len() - 2) {
            pts.push((le + (te - le) * u - up * (t * tc * ch * 0.38), -up));
        }
        let n = pts.len();
        (0..n)
            .map(|k| {
                let a = pts[(k + n - 1) % n].0;
                let b = pts[(k + 1) % n].0;
                let side = (le1 - le0).normalize_or_zero();
                let mut nn = (b - a).cross(side).normalize_or_zero();
                if nn.dot(pts[k].1) < 0.0 && k != 0 {
                    nn = -nn;
                }
                if k == 0 {
                    nn = fwd;
                }
                (pts[k].0, nn)
            })
            .collect()
    };
    let s0 = section(le0, te0);
    let s1 = section(le1, te1);
    m.rings(&s0, &s1, part);
    let c0 = s0.iter().fold(Vec3::ZERO, |a, p| a + p.0) / s0.len() as f32;
    let c1 = s1.iter().fold(Vec3::ZERO, |a, p| a + p.0) / s1.len() as f32;
    for k in 0..s0.len() {
        let k1 = (k + 1) % s0.len();
        m.tri(c0, s0[k1].0, s0[k].0, part);
        m.tri(c1, s1[k].0, s1[k1].0, part);
    }
}

fn ellipsoid(m: &mut Mesh, c: Vec3, r: Vec3, part: f32) {
    let (nu, nv) = (14, 8);
    let p = |i: usize, j: usize| {
        let th = i as f32 / nu as f32 * std::f32::consts::TAU;
        let ph = j as f32 / nv as f32 * std::f32::consts::PI - std::f32::consts::FRAC_PI_2;
        let d = vec3(ph.cos() * th.cos(), ph.cos() * th.sin(), ph.sin());
        (c + d * r, (d / r).normalize())
    };
    for j in 0..nv {
        let r0: Vec<_> = (0..nu).map(|i| p(i, j)).collect();
        let r1: Vec<_> = (0..nu).map(|i| p(i, j + 1)).collect();
        m.rings(&r0, &r1, part);
    }
}

fn cylinder(m: &mut Mesh, a: Vec3, b: Vec3, r0: f32, r1: f32, squash: f32, part: f32) {
    let axis = (b - a).normalize();
    let t = if axis.z.abs() < 0.9 { axis.cross(Vec3::Z).normalize() } else { axis.cross(Vec3::X).normalize() };
    let s = axis.cross(t);
    let segs = 12;
    let ring = |c: Vec3, r: f32| -> Vec<(Vec3, Vec3)> {
        (0..segs)
            .map(|k| {
                let th = k as f32 / segs as f32 * std::f32::consts::TAU;
                let d = t * th.cos() + s * th.sin() * squash;
                (c + d * r, (t * th.cos() + s * th.sin() / squash.max(0.05)).normalize())
            })
            .collect()
    };
    let (ra, rb) = (ring(a, r0), ring(b, r1));
    m.rings(&ra, &rb, part);
    for k in 0..segs {
        let k1 = (k + 1) % segs;
        m.tri(a, ra[k1].0, ra[k].0, part);
        m.tri(b, rb[k].0, rb[k1].0, part);
    }
}

fn rot_about(p: Vec3, a: Vec3, axis: Vec3, ang: f32) -> Vec3 {
    a + Quat::from_axis_angle(axis.normalize(), ang) * (p - a)
}

fn hinged(m: &mut Mesh, build: impl FnOnce(&mut Mesh), h0: Vec3, h1: Vec3, ang: f32) {
    let start = m.v.len();
    build(m);
    let axis = (h1 - h0).normalize();
    let q = Quat::from_axis_angle(axis, ang);
    for v in &mut m.v[start..] {
        v.pos = rot_about(v.pos, h0, axis, ang);
        v.nrm = q * v.nrm;
    }
}

pub fn build(c: &Controls, cockpit: bool) -> Mesh {
    let mut m = Mesh::default();
    let sections: [(f32, f32, f32, f32, f32); 12] = [
        (2.28, -0.05, 0.34, 0.34, 2.4),
        (2.05, -0.02, 0.46, 0.46, 2.6),
        (1.55, 0.0, 0.50, 0.48, 2.8),
        (1.10, 0.04, 0.54, 0.52, 3.0),
        (0.70, 0.18, 0.56, 0.70, 3.0),
        (0.00, 0.18, 0.57, 0.72, 3.2),
        (-1.20, 0.18, 0.55, 0.70, 3.0),
        (-2.00, 0.20, 0.45, 0.55, 2.8),
        (-3.20, 0.24, 0.30, 0.38, 2.6),
        (-4.40, 0.28, 0.17, 0.26, 2.4),
        (-5.45, 0.32, 0.07, 0.12, 2.2),
        (-5.70, 0.34, 0.02, 0.04, 2.0),
    ];
    let rings: Vec<Vec<(Vec3, Vec3)>> = sections.iter().map(|s| superellipse_ring(s.0, s.1, s.2, s.3, s.4, 28)).collect();
    for k in 0..rings.len() - 1 {
        m.rings(&rings[k + 1], &rings[k], if cockpit { P_TRIM } else { P_FUSELAGE });
    }
    let spin0: Vec<(Vec3, Vec3)> = superellipse_ring(PROP_X - 0.02, PROP_Z, 0.19, 0.19, 2.0, 16);
    let tip = vec3(PROP_X + 0.42, PROP_Z, 0.0);
    for k in 0..spin0.len() {
        let k1 = (k + 1) % spin0.len();
        m.tri(spin0[k].0, tip, spin0[k1].0, P_SPINNER);
    }
    let wz = 0.90;
    for side in [1.0f32, -1.0] {
        let y = |v: f32| v * side;
        let dz = |v: f32| wz + v.abs() * 0.03;
        let (le_in, te_in) = (0.55, -1.08);
        let root = (vec3(le_in, y(0.50), dz(0.5)), vec3(te_in, y(0.50), dz(0.5)));
        let mid = (vec3(le_in, y(2.60), dz(2.6)), vec3(te_in, y(2.60), dz(2.6)));
        let tipp = (vec3(0.42, y(5.50), dz(5.5)), vec3(-0.70, y(5.50), dz(5.5)));
        let at = |s: f32| -> (Vec3, Vec3) {
            let t = (s - 2.6) / (5.5 - 2.6);
            (mid.0.lerp(tipp.0, t), mid.1.lerp(tipp.1, t))
        };
        let (a0, a1) = (at(2.9), at(4.9));
        let ail_c = 0.36;
        let cut = |p: (Vec3, Vec3)| (p.0, p.1 + (p.0 - p.1).normalize() * ail_c);
        let (l0, r0) = if side > 0.0 { (root, mid) } else { (mid, root) };
        airfoil(&mut m, l0.0, l0.1, r0.0, r0.1, Vec3::Z, 0.15, P_WING);
        let (c29, c49) = (at(2.9), at(4.9));
        let (l1, r1) = if side > 0.0 { (mid, c29) } else { (c29, mid) };
        airfoil(&mut m, l1.0, l1.1, r1.0, r1.1, Vec3::Z, 0.14, P_WING);
        let (l2, r2) = if side > 0.0 { (cut(a0), cut(a1)) } else { (cut(a1), cut(a0)) };
        airfoil(&mut m, l2.0, l2.1, r2.0, r2.1, Vec3::Z, 0.15, P_WING);
        let (l3, r3) = if side > 0.0 { (c49, tipp) } else { (tipp, c49) };
        airfoil(&mut m, l3.0, l3.1, r3.0, r3.1, Vec3::Z, 0.12, P_WING);
        let (h0, h1) = (cut(a0).1, cut(a1).1);
        hinged(
            &mut m,
            |m| {
                let (l, r) = if side > 0.0 { ((h0, a0.1), (h1, a1.1)) } else { ((h1, a1.1), (h0, a0.1)) };
                airfoil(m, l.0, l.1, r.0, r.1, Vec3::Z, 0.10, P_SURFACE);
            },
            h0,
            h1,
            -c.aileron,
        );
        cylinder(&mut m, vec3(-0.15, y(0.52), -0.30), vec3(-0.05, y(2.55), dz(2.55) - 0.05), 0.055, 0.045, 0.35, P_STRUT);
        let wheel = vec3(-0.62, y(1.25), -1.10);
        cylinder(&mut m, vec3(-0.50, y(0.38), -0.42), wheel + vec3(0.0, -y(0.06), 0.12), 0.07, 0.05, 0.3, P_STRUT);
        cylinder(&mut m, wheel - vec3(0.0, 0.07, 0.0), wheel + vec3(0.0, 0.07, 0.0), 0.25, 0.25, 1.0, P_TIRE);
        ellipsoid(&mut m, wheel + vec3(0.0, 0.0, 0.07), vec3(0.55, 0.12, 0.21), P_FAIRING);
    }
    let nw = vec3(1.62, 0.0, -1.15);
    cylinder(&mut m, vec3(1.48, 0.0, -0.40), nw + vec3(0.0, 0.0, 0.1), 0.06, 0.05, 1.0, P_STRUT);
    cylinder(&mut m, nw - vec3(0.0, 0.06, 0.0), nw + vec3(0.0, 0.06, 0.0), 0.2, 0.2, 1.0, P_TIRE);
    ellipsoid(&mut m, nw + vec3(0.0, 0.0, 0.07), vec3(0.42, 0.1, 0.17), P_FAIRING);
    let tz = 0.30;
    for side in [1.0f32, -1.0] {
        let (r_le, r_te, t_le, t_te) = (vec3(-4.70, 0.0, tz), vec3(-5.30, 0.0, tz), vec3(-4.98, side * 1.72, tz), vec3(-5.36, side * 1.72, tz));
        let (l, r) = if side > 0.0 { ((r_le, r_te), (t_le, t_te)) } else { ((t_le, t_te), (r_le, r_te)) };
        airfoil(&mut m, l.0, l.1, r.0, r.1, Vec3::Z, 0.10, P_TAIL);
        let (e0, e1) = (vec3(-5.75, 0.0, tz), vec3(-5.68, side * 1.72, tz));
        hinged(
            &mut m,
            |m| {
                let (l, r) = if side > 0.0 { ((r_te, e0), (t_te, e1)) } else { ((t_te, e1), (r_te, e0)) };
                airfoil(m, l.0, l.1, r.0, r.1, Vec3::Z, 0.08, P_SURFACE);
            },
            if side > 0.0 { r_te } else { t_te },
            if side > 0.0 { t_te } else { r_te },
            -c.elevator,
        );
    }
    let (f_le0, f_te0, f_le1, f_te1) = (vec3(-4.25, 0.0, 0.50), vec3(-5.30, 0.0, 0.42), vec3(-5.10, 0.0, 1.35), vec3(-5.40, 0.0, 1.35));
    airfoil(&mut m, f_le1, f_te1, f_le0, f_te0, Vec3::Y, 0.10, P_TAIL);
    m.tri(vec3(-3.10, 0.0, 0.62), vec3(-4.25, 0.0, 0.50), vec3(-4.45, 0.0, 0.78), P_TAIL);
    hinged(
        &mut m,
        |m| airfoil(m, f_te1, vec3(-5.78, 0.0, 1.30), f_te0, vec3(-5.72, 0.0, 0.38), Vec3::Y, 0.08, P_SURFACE),
        f_te0,
        f_te1,
        c.rudder,
    );
    if cockpit {
        // Instrument panel and glare shield; the shell above is trim, its windows are cut in the shader.
        let x0 = 0.78;
        m.quad(vec3(x0, 0.54, 0.02), vec3(x0, -0.54, 0.02), vec3(x0, -0.54, 0.40), vec3(x0, 0.54, 0.40), P_PANEL);
        m.quad(vec3(x0, 0.54, 0.40), vec3(x0, -0.54, 0.40), vec3(1.12, -0.54, 0.55), vec3(1.12, 0.54, 0.55), P_PANEL);
        for y in [0.53f32, -0.53] {
            cylinder(&mut m, vec3(1.08, y, 0.52), vec3(0.70, y * 1.02, 0.88), 0.022, 0.022, 1.0, P_TRIM);
        }
    }
    m
}

/// The propeller disc as a quad in body axes; its fragments draw the blades (rolling shutter, motion blur).
pub fn prop_disc() -> [Vec3; 4] {
    let (x, r, z) = (PROP_X + 0.03, PROP_R, PROP_Z);
    [vec3(x, -r, z - r), vec3(x, r, z - r), vec3(x, r, z + r), vec3(x, -r, z + r)]
}
