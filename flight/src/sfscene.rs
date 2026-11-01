//! San Francisco for the photoreal renderer: footprint buildings, the Bay Bridge West Span and the elevated
//! freeways, the Golden Gate Bridge, the aerial-photo ground and the Bay Area backdrop. Geometry and
//! textures only; `photo.rs` shades them with the grid city's materials. The collision geometry is untouched.

use crate::photo::{srgb_to_lin, K_CLUTTER, K_FACADE, K_ROOF, K_TERRAIN, PV};
use cityflight::world::*;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/data/sf/");

/// Ground detail-mask resolution (texels per side).
const MASK: usize = 4096;

/// Backdrop extent (half-size, m), terrain grid (nodes, spacing), as `data/sf/fetch_backdrop.py` writes it.
const BACK_HALF: f64 = 40000.0;
const BACK_N: usize = 801;
const BACK_SP: f64 = 100.0;

/// Tints for the clutter material, which multiplies the concrete texture (linear, about 0.45 on average).
const ORANGE: [f32; 3] = [1.15, 0.17, 0.095];
const CONCRETE: [f32; 3] = [0.95, 0.93, 0.90];
const ROADWAY: [f32; 3] = [0.30, 0.30, 0.32];
const STEEL: [f32; 3] = [0.62, 0.66, 0.72];

fn hash01(x: i64, y: i64) -> f64 {
    let mut r = Rng::new((x as u64).wrapping_mul(0x9E37_79B1) ^ (y as u64).wrapping_mul(0x85EB_CA77));
    r.f()
}

fn mix3(a: [f64; 3], b: [f64; 3], t: f64) -> [f64; 3] {
    [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]
}

fn smoothstep(e0: f64, e1: f64, x: f64) -> f64 {
    let t = ((x - e0) / (e1 - e0)).clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

/// A square JPEG as RGBA with row 0 at the south edge, and its side; `None` if missing or not square.
fn load_square(path: &str) -> Option<(Vec<u8>, usize)> {
    let bytes = std::fs::read(path).ok()?;
    let img = image::load_from_memory_with_format(&bytes, image::ImageFormat::Jpeg).ok()?.to_rgba8();
    let n = img.width() as usize;
    if img.height() as usize != n {
        return None;
    }
    let raw = img.into_raw();
    let mut px = vec![0u8; raw.len()];
    for r in 0..n {
        px[r * n * 4..(r + 1) * n * 4].copy_from_slice(&raw[(n - 1 - r) * n * 4..(n - r) * n * 4]);
    }
    Some((px, n))
}

/// An aerial photo is lit already (sun and sky, plus haze); the renderer lights the ground again. Scale it
/// to plausible albedo in linear light (bright concrete about 0.35), with a little more contrast.
fn photo_to_albedo(px: &mut [u8]) {
    let lut: Vec<u8> = (0..256)
        .map(|v| {
            let l = srgb_to_lin(v as f32 / 255.0);
            let a = 0.55 * l.powf(1.1);
            let c = if a <= 0.0031308 { 12.92 * a } else { 1.055 * a.powf(1.0 / 2.4) - 0.055 };
            (c.clamp(0.0, 1.0) * 255.0 + 0.5) as u8
        })
        .collect();
    for p in px.chunks_exact_mut(4) {
        for c in &mut p[..3] {
            *c = lut[*c as usize];
        }
    }
}

/// Vegetation weight of an aerial-photo pixel: green above both red and blue.
fn green(p: &[u8]) -> f64 {
    smoothstep(4.0, 30.0, p[1] as f64 - (p[0].max(p[2])) as f64)
}

// ---------------------------------------------------------------- ground

/// OSM streets rasterised over the square: 0 none, 1 sidewalk, 2 asphalt, 3 centre line.
fn street_mask(w: &World) -> Vec<u8> {
    let mut m = vec![0u8; MASK * MASK];
    let px = 2.0 * MAP_HALF / MASK as f64;
    for st in w.streets.iter().filter(|s| !s.bridge) {
        let hw = [11.0, 10.0, 9.0, 8.0, 7.0, 5.5, 5.5, 4.0, 4.0, 4.0, 4.0][st.class as usize];
        let walk = st.class >= 2 && st.class <= 6;
        let line = st.class <= 3;
        for seg in st.pts.windows(2) {
            let (a, b) = (seg[0], seg[1]);
            let (dx, dy) = (b[0] - a[0], b[1] - a[1]);
            let l2 = (dx * dx + dy * dy).max(1e-9);
            let ti = |v: f64| (((v + MAP_HALF) / px).floor().max(0.0) as usize).min(MASK - 1);
            for j in ti(a[1].min(b[1]) - hw)..=ti(a[1].max(b[1]) + hw) {
                let y = -MAP_HALF + (j as f64 + 0.5) * px;
                for i in ti(a[0].min(b[0]) - hw)..=ti(a[0].max(b[0]) + hw) {
                    let x = -MAP_HALF + (i as f64 + 0.5) * px;
                    let t = (((x - a[0]) * dx + (y - a[1]) * dy) / l2).clamp(0.0, 1.0);
                    let d = ((x - a[0] - t * dx).powi(2) + (y - a[1] - t * dy).powi(2)).sqrt();
                    let along = t * l2.sqrt();
                    let code = if d > hw {
                        0
                    } else if line && d < 0.8 && (along / 9.0).rem_euclid(1.0) < 0.55 {
                        3
                    } else if walk && d > hw - 2.2 {
                        1
                    } else {
                        2
                    };
                    // Where streets overlap, asphalt beats a centre line beats a sidewalk.
                    let rank = |c: u8| [0, 1, 3, 2][c as usize];
                    let c = &mut m[j * MASK + i];
                    if rank(code) > rank(*c) {
                        *c = code;
                    }
                }
            }
        }
    }
    m
}

/// Ground colour without the aerial photo: bay water, paved lots, OSM streets.
fn painted(w: &World, street: u8, x: f64, y: f64) -> [f64; 3] {
    let speck = hash01((x / 6.0).floor() as i64, (y / 6.0).floor() as i64);
    if w.terrain(x, y) <= SF_WATER + 0.05 {
        let ripple = 0.5 + 0.5 * ((x * 0.013 + y * 0.007).sin() * (y * 0.011 - x * 0.005).cos());
        return mix3([0.12, 0.26, 0.35], [0.16, 0.32, 0.41], 0.6 * ripple + 0.4 * speck);
    }
    match street {
        1 => [0.62, 0.61, 0.58],
        2 => mix3([0.21, 0.21, 0.23], [0.26, 0.26, 0.28], speck * 0.5),
        3 => [0.85, 0.85, 0.82],
        _ => mix3([0.54, 0.53, 0.49], [0.62, 0.61, 0.57], speck),
    }
}

/// Ground colour painted from OpenStreetMap and the terrain (RGBA, `MASK` per side, row 0 south): what the
/// ground shows without the aerial photo, and the classic renderer's San Francisco ground.
pub fn painted_ground(w: &World) -> Vec<u8> {
    let streets = street_mask(w);
    let px = 2.0 * MAP_HALF / MASK as f64;
    let mut alb = vec![0u8; MASK * MASK * 4];
    for j in 0..MASK {
        let y = -MAP_HALF + (j as f64 + 0.5) * px;
        for i in 0..MASK {
            let x = -MAP_HALF + (i as f64 + 0.5) * px;
            let k = j * MASK + i;
            let c = painted(w, streets[k], x, y);
            for (o, v) in c.iter().enumerate() {
                alb[k * 4 + o] = (v.clamp(0.0, 1.0) * 255.0) as u8;
            }
            alb[k * 4 + 3] = 255;
        }
    }
    alb
}

/// Ground albedo (sRGB, occlusion in A) and detail mask (asphalt, grass, rock; concrete is the rest), each
/// with its side in texels. With `sf_naip.jpg` (USDA NAIP, public domain) the albedo is the aerial photo;
/// without it, streets are painted from OpenStreetMap. Water gets no detail weights.
pub fn ground(w: &World) -> (Vec<u8>, usize, Vec<u8>, usize) {
    let streets = street_mask(w);
    let photo = load_square(&format!("{DATA}sf_naip.jpg"));
    let px = 2.0 * MAP_HALF / MASK as f64;
    let mut mask = vec![0u8; MASK * MASK * 4];
    for j in 0..MASK {
        let y = -MAP_HALF + (j as f64 + 0.5) * px;
        for i in 0..MASK {
            let x = -MAP_HALF + (i as f64 + 0.5) * px;
            let k = j * MASK + i;
            mask[k * 4 + 3] = 255;
            if w.terrain(x, y) <= SF_WATER + 0.05 {
                continue;
            }
            let grass = match &photo {
                Some((p, n)) => green(&p[((j * n / MASK) * n + i * n / MASK) * 4..]),
                None => 0.0,
            };
            let asphalt = if streets[k] >= 2 { 1.0 } else { 0.0 };
            mask[k * 4] = (asphalt * 255.0) as u8;
            mask[k * 4 + 1] = ((1.0 - asphalt) * grass * 255.0) as u8;
        }
    }
    match photo {
        Some((mut p, n)) => {
            photo_to_albedo(&mut p);
            (p, n, mask, MASK)
        }
        None => (painted_ground(w), MASK, mask, MASK),
    }
}

// ---------------------------------------------------------------- backdrop

/// The Bay Area beyond the flyable square: vertices, indices, imagery (side `n`) and its detail mask (side
/// `mask_n`). Visual only. It reaches 100 m under the square's edge and sinks 2 m there, so no crack shows.
pub struct Backdrop {
    pub v: Vec<PV>,
    pub i: Vec<u32>,
    pub alb: Vec<u8>,
    pub n: usize,
    pub mask: Vec<u8>,
    pub mask_n: usize,
}

/// Backdrop terrain heights (row 0 south, floored at the water level), if `backdrop_dem.f32` is present.
fn backdrop_dem() -> Option<Vec<f32>> {
    let raw = std::fs::read(format!("{DATA}backdrop_dem.f32")).ok()?;
    if raw.len() != BACK_N * BACK_N * 4 {
        return None;
    }
    Some(raw.chunks_exact(4).map(|c| f32::from_le_bytes(c.try_into().unwrap()).max(SF_WATER as f32)).collect())
}

/// Backdrop height at (x, y), bilinear; the water level off the grid or without the file.
fn dem_at(dem: &Option<Vec<f32>>, x: f64, y: f64) -> f64 {
    let Some(d) = dem else { return SF_WATER };
    let fx = ((x + BACK_HALF) / BACK_SP).clamp(0.0, (BACK_N - 1) as f64 - 1e-9);
    let fy = ((y + BACK_HALF) / BACK_SP).clamp(0.0, (BACK_N - 1) as f64 - 1e-9);
    let (i, j) = (fx as usize, fy as usize);
    let (tx, ty) = (fx - i as f64, fy - j as f64);
    let h = |a: usize, b: usize| d[b * BACK_N + a] as f64;
    let a = h(i, j) + (h(i + 1, j) - h(i, j)) * tx;
    let b = h(i, j + 1) + (h(i + 1, j + 1) - h(i, j + 1)) * tx;
    a + (b - a) * ty
}

/// The backdrop from `data/sf/fetch_backdrop.py`'s files, or `None` if either is missing. NAIP has no data
/// over open ocean; those (black) pixels become water.
pub fn backdrop(w: &World) -> Option<Backdrop> {
    let dem = backdrop_dem()?;
    let (mut alb, n) = load_square(&format!("{DATA}backdrop.jpg"))?;
    for c in alb.chunks_exact_mut(4) {
        if c[0] < 10 && c[1] < 10 && c[2] < 10 {
            c[..3].copy_from_slice(&[52, 92, 108]);
        }
    }
    let mask_n = 2048;
    let mut mask = vec![0u8; mask_n * mask_n * 4];
    for j in 0..mask_n {
        for i in 0..mask_n {
            let p = &alb[((j * n / mask_n) * n + i * n / mask_n) * 4..];
            let k = (j * mask_n + i) * 4;
            mask[k + 1] = (green(p) * 255.0) as u8;
            mask[k + 3] = 255;
        }
    }
    photo_to_albedo(&mut alb);
    let h = |i: usize, j: usize| dem[j.min(BACK_N - 1) * BACK_N + i.min(BACK_N - 1)];
    let inner = MAP_HALF - BACK_SP;
    let mut v = Vec::with_capacity(BACK_N * BACK_N);
    for j in 0..BACK_N {
        for i in 0..BACK_N {
            let (x, y) = (-BACK_HALF + i as f64 * BACK_SP, -BACK_HALF + j as f64 * BACK_SP);
            let dx = h(i + 1, j) - h(i.saturating_sub(1), j);
            let dy = h(i, j + 1) - h(i, j.saturating_sub(1));
            let len = (dx * dx + dy * dy + (2.0 * BACK_SP as f32).powi(2)).sqrt();
            // On and inside the square's edge, follow the map's own terrain (2 m below it).
            let z = if x.abs() <= MAP_HALF + 1.0 && y.abs() <= MAP_HALF + 1.0 { w.terrain(x, y) as f32 - 2.0 } else { h(i, j) };
            v.push(PV {
                pos: [x as f32, y as f32, z],
                nrm: [-dx / len, -dy / len, 2.0 * BACK_SP as f32 / len],
                col: [1.0, 1.0, 1.0],
                uv: [((x + BACK_HALF) / (2.0 * BACK_HALF)) as f32, ((y + BACK_HALF) / (2.0 * BACK_HALF)) as f32],
                mat: [K_TERRAIN, 0.0, 0.0, 0.0],
                fac: [0.0; 4],
            });
        }
    }
    let mut idx: Vec<u32> = Vec::with_capacity(BACK_N * BACK_N * 6);
    for j in 0..BACK_N - 1 {
        for i in 0..BACK_N - 1 {
            let (x0, y0) = (-BACK_HALF + i as f64 * BACK_SP, -BACK_HALF + j as f64 * BACK_SP);
            if x0 >= -inner - 1.0 && x0 + BACK_SP <= inner + 1.0 && y0 >= -inner - 1.0 && y0 + BACK_SP <= inner + 1.0 {
                continue;
            }
            let a = (j * BACK_N + i) as u32;
            let (b, c, d) = (a + 1, a + BACK_N as u32 + 1, a + BACK_N as u32);
            idx.extend_from_slice(&[a, b, c, a, c, d]);
        }
    }
    Some(Backdrop { v, i: idx, alb, n, mask, mask_n })
}

// ---------------------------------------------------------------- mesh helpers

#[derive(Default)]
struct Mesh {
    v: Vec<PV>,
    i: Vec<u32>,
}

fn clutter(metal: f32) -> [f32; 4] {
    [K_CLUTTER, 0.0, metal, 0.0]
}

impl Mesh {
    fn quad(&mut self, n: [f32; 3], q: [[f32; 3]; 4], col: [f32; 3], uv: [f32; 2], mat: [f32; 4], fac: [f32; 4]) {
        let base = self.v.len() as u32;
        for pos in q {
            self.v.push(PV { pos, nrm: n, col, uv, mat, fac });
        }
        self.i.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
    }

    /// Vertical quad along `p` → `q` (outward to the right), bottoms `z[0]`, `z[1]` and tops `z[2]`, `z[3]`.
    fn wall(&mut self, p: [f64; 2], q: [f64; 2], z: [f32; 4], col: [f32; 3], mat: [f32; 4]) {
        let (ex, ey) = ((q[0] - p[0]) as f32, (q[1] - p[1]) as f32);
        let l = (ex * ex + ey * ey).sqrt().max(1e-4);
        let (px, py, qx, qy) = (p[0] as f32, p[1] as f32, q[0] as f32, q[1] as f32);
        self.quad([ey / l, -ex / l, 0.0], [[px, py, z[0]], [qx, qy, z[1]], [qx, qy, z[3]], [px, py, z[2]]], col, [0.0; 2], mat, [0.0; 4]);
    }

    /// Horizontal convex polygon (a fan), facing up or down.
    fn cap(&mut self, poly: &[[f64; 2]], z: f32, up: bool, col: [f32; 3], mat: [f32; 4], fac: [f32; 4]) {
        let i0 = self.v.len() as u32;
        for p in poly {
            self.v.push(PV { pos: [p[0] as f32, p[1] as f32, z], nrm: [0.0, 0.0, if up { 1.0 } else { -1.0 }], col, uv: [0.0; 2], mat, fac });
        }
        for t in 1..poly.len().saturating_sub(1) as u32 {
            self.i.extend_from_slice(&[i0, i0 + t, i0 + t + 1]);
        }
    }

    /// A solid of a counter-clockwise convex footprint, clutter material.
    fn prism(&mut self, poly: &[[f64; 2]], z0: f64, z1: f64, col: [f32; 3], metal: f32) {
        let (a, b) = (z0 as f32, z1 as f32);
        for e in 0..poly.len() {
            self.wall(poly[e], poly[(e + 1) % poly.len()], [a, a, b, b], col, clutter(metal));
        }
        self.cap(poly, b, true, col, clutter(metal), [0.0; 4]);
    }

    /// A box around centre `c`, half-lengths `ha` along the unit `u` and `hc` across it, `z0..z1`.
    fn obox(&mut self, c: [f64; 2], u: [f64; 2], ha: f64, hc: f64, z0: f64, z1: f64, col: [f32; 3], metal: f32) {
        let n = [-u[1], u[0]];
        let at = |a: f64, b: f64| [c[0] + u[0] * a + n[0] * b, c[1] + u[1] * a + n[1] * b];
        let poly = [at(-ha, -hc), at(ha, -hc), at(ha, hc), at(-ha, hc)];
        self.prism(&poly, z0, z1, col, metal);
        self.cap(&poly, z0 as f32, false, col, clutter(metal), [0.0; 4]);
    }

    /// A square tube of half-size `r` from `a` to `b` (cables, suspenders, ribs).
    fn tube(&mut self, a: [f64; 3], b: [f64; 3], r: f64, col: [f32; 3], metal: f32) {
        let d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
        let h = (d[0] * d[0] + d[1] * d[1]).sqrt();
        let len = (h * h + d[2] * d[2]).sqrt().max(1e-9);
        // Cross-section axes: horizontal and vertical for a sloping tube, east and north for a vertical one.
        let (e1, e2) = if h < 0.3 * len { ([r, 0.0, 0.0], [0.0, r, 0.0]) } else { ([-d[1] / h * r, d[0] / h * r, 0.0], [0.0, 0.0, r]) };
        let off = |p: [f64; 3], s: f64, t: f64| [(p[0] + e1[0] * s + e2[0] * t) as f32, (p[1] + e1[1] * s + e2[1] * t) as f32, (p[2] + e1[2] * s + e2[2] * t) as f32];
        let unit = |v: [f64; 3], k: f64| [(v[0] / r * k) as f32, (v[1] / r * k) as f32, (v[2] / r * k) as f32];
        for (n, s0, t0, s1, t1) in [
            (unit(e2, 1.0), -1.0, 1.0, 1.0, 1.0),
            (unit(e2, -1.0), 1.0, -1.0, -1.0, -1.0),
            (unit(e1, 1.0), 1.0, 1.0, 1.0, -1.0),
            (unit(e1, -1.0), -1.0, -1.0, -1.0, 1.0),
        ] {
            self.quad(n, [off(a, s0, t0), off(b, s0, t0), off(b, s1, t1), off(a, s1, t1)], col, [0.0; 2], clutter(metal), [0.0; 4]);
        }
    }
}

/// Is `p` inside the counter-clockwise convex `poly`, at least `margin` from every edge?
fn inside_convex(poly: &[[f64; 2]], p: [f64; 2], margin: f64) -> bool {
    (0..poly.len()).all(|e| {
        let (a, b) = (poly[e], poly[(e + 1) % poly.len()]);
        let (ex, ey) = (b[0] - a[0], b[1] - a[1]);
        let l = (ex * ex + ey * ey).sqrt().max(1e-9);
        (ex * (p[1] - a[1]) - ey * (p[0] - a[0])) / l >= margin
    })
}

// ---------------------------------------------------------------- buildings

/// How a building is drawn, shared by every piece it overlaps: the lowest base, the highest roof and the
/// colour variation.
#[derive(Clone, Copy)]
struct Look {
    base: f64,
    top: f64,
    tint: f32,
}

/// Do two convex polygons overlap with positive area (separating axes)?
fn convex_overlap(a: &[[f64; 2]], b: &[[f64; 2]]) -> bool {
    for poly in [a, b] {
        for e in 0..poly.len() {
            let (p, q) = (poly[e], poly[(e + 1) % poly.len()]);
            let (nx, ny) = (q[1] - p[1], p[0] - q[0]);
            let l = (nx * nx + ny * ny).sqrt().max(1e-12);
            let proj = |s: &[[f64; 2]]| s.iter().map(|r| (r[0] * nx + r[1] * ny) / l).fold((f64::INFINITY, f64::NEG_INFINITY), |(lo, hi), v| (lo.min(v), hi.max(v)));
            let ((a0, a1), (b0, b1)) = (proj(a), proj(b));
            if a1 <= b0 + 0.05 || b1 <= a0 + 0.05 {
                return false;
            }
        }
    }
    true
}

/// DataSF and OSM overlap, and so do the convex pieces of one footprint, which leaves coplanar faces that
/// flicker when they differ. Pieces inside a piece at least as tall, and needle-thin slivers (under 0.5 m
/// wide or 1 m²), are not drawn; overlapping pieces whose roofs are within 1 m share one look.
fn render_looks(w: &World) -> Vec<Option<Look>> {
    let n = w.boxes.len();
    let outlines: Vec<Vec<[f64; 2]>> = w.boxes.iter().map(|b| w.outline(b)).collect();
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(p: &mut [usize], mut x: usize) -> usize {
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    let mut hidden = vec![false; n];
    let solid = |b: &Building| b.kind == Kind::Building || b.kind == Kind::BridgeTower;
    for (k, o) in outlines.iter().enumerate() {
        let (mut area, mut width) = (0.0, f64::INFINITY);
        for e in 0..o.len() {
            let (p, q) = (o[e], o[(e + 1) % o.len()]);
            area += p[0] * q[1] - q[0] * p[1];
            let (ex, ey) = (q[0] - p[0], q[1] - p[1]);
            let l = (ex * ex + ey * ey).sqrt().max(1e-9);
            let ext = o.iter().map(|r| ((r[0] - p[0]) * ey - (r[1] - p[1]) * ex).abs() / l).fold(0.0, f64::max);
            width = width.min(ext);
        }
        if solid(&w.boxes[k]) && (0.5 * area < 1.0 || width < 0.5) {
            hidden[k] = true;
        }
    }
    const C: f64 = 40.0;
    let mut grid: std::collections::HashMap<(i32, i32), Vec<usize>> = std::collections::HashMap::new();
    for (k, b) in w.boxes.iter().enumerate() {
        if !solid(b) {
            continue;
        }
        for j in (b.y0 / C).floor() as i32..=(b.y1 / C).floor() as i32 {
            for i in (b.x0 / C).floor() as i32..=(b.x1 / C).floor() as i32 {
                grid.entry((i, j)).or_default().push(k);
            }
        }
    }
    let mut seen = std::collections::HashSet::new();
    for cell in grid.values() {
        for (ia, &a) in cell.iter().enumerate() {
            for &b in &cell[ia + 1..] {
                let (ba, bb) = (&w.boxes[a], &w.boxes[b]);
                if ba.x1 < bb.x0 || bb.x1 < ba.x0 || ba.y1 < bb.y0 || bb.y1 < ba.y0 || !seen.insert((a.min(b), a.max(b))) {
                    continue;
                }
                if !convex_overlap(&outlines[a], &outlines[b]) {
                    continue;
                }
                let inside = |x: usize, y: usize| outlines[x].iter().all(|q| pt_poly_dist2(*q, &outlines[y]) < 1e-6);
                if w.boxes[a].z1 <= w.boxes[b].z1 + 0.05 && inside(a, b) {
                    hidden[a] = true;
                } else if w.boxes[b].z1 <= w.boxes[a].z1 + 0.05 && inside(b, a) {
                    hidden[b] = true;
                }
                if (w.boxes[a].z1 - w.boxes[b].z1).abs() < 1.0 {
                    let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
                    parent[ra] = rb;
                }
            }
        }
    }
    let mut group: Vec<Option<Look>> = vec![None; n];
    for k in 0..n {
        let r = find(&mut parent, k);
        let b = &w.boxes[k];
        let g = group[r].get_or_insert(Look { base: f64::INFINITY, top: f64::NEG_INFINITY, tint: w.boxes[r].tint });
        g.base = g.base.min(b.z0);
        g.top = g.top.max(b.z1);
    }
    (0..n)
        .map(|k| {
            if hidden[k] {
                return None;
            }
            let b = &w.boxes[k];
            if !solid(b) {
                return Some(Look { base: b.z0, top: b.z1, tint: b.tint });
            }
            group[find(&mut parent, k)]
        })
        .collect()
}

/// San Francisco wall colours (sRGB): painted rowhouses, light mid-rises, the grid city's tower palette.
fn sf_color(tint: f32, height: f64) -> [f32; 3] {
    const ROW: [[f32; 3]; 9] = [
        [0.93, 0.89, 0.80],
        [0.72, 0.81, 0.88],
        [0.76, 0.86, 0.79],
        [0.91, 0.79, 0.76],
        [0.95, 0.88, 0.64],
        [0.68, 0.72, 0.77],
        [0.94, 0.94, 0.91],
        [0.74, 0.77, 0.67],
        [0.86, 0.80, 0.70],
    ];
    const MID: [[f32; 3]; 7] = [
        [0.88, 0.86, 0.81],
        [0.80, 0.78, 0.74],
        [0.92, 0.90, 0.85],
        [0.74, 0.70, 0.64],
        [0.70, 0.50, 0.42],
        [0.84, 0.82, 0.78],
        [0.66, 0.68, 0.70],
    ];
    const TALL: [[f32; 3]; 4] = [[0.50, 0.58, 0.67], [0.40, 0.46, 0.53], [0.66, 0.70, 0.74], [0.56, 0.62, 0.58]];
    let pick = |pal: &[[f32; 3]]| pal[((tint * (pal.len() as f32 - 0.001)) as usize).min(pal.len() - 1)];
    if height < 20.0 {
        pick(&ROW)
    } else if height <= 70.0 {
        pick(&MID)
    } else {
        pick(&TALL)
    }
}

impl Mesh {
    /// One convex piece of a building: a facade per footprint edge, the roof, and render-only rooftop units
    /// (low and inset, inside the filter's clearance margin) on the top piece.
    fn building(&mut self, w: &World, b: &Building, look: Look) {
        let poly = w.outline(b);
        let seed = look.tint;
        let height = look.top - look.base;
        let pick = |opts: &[usize]| opts[((seed * 977.0) as usize) % opts.len()];
        // Towers as in the grid city; below them mostly light stone and stucco, some brick.
        let ft = if height > 70.0 {
            pick(&[0, 1, 2, 0, 1])
        } else if height > 30.0 {
            pick(&[1, 2, 4, 4, 3])
        } else {
            pick(&[4, 4, 4, 3, 5])
        };
        let (_, cols, rows, _) = crate::assets::FACADES[ft];
        let floor_h = if ft >= 3 { 3.2 } else { 3.6 } * (0.95 + 0.1 * (seed * 31.0).fract());
        let col_nom = floor_h * rows / cols;
        let c = sf_color(look.tint, height);
        let c = [srgb_to_lin(c[0]), srgb_to_lin(c[1]), srgb_to_lin(c[2])];
        let lum = (0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2]).max(1e-3);
        // Painted rowhouses keep more of their colour than the grid city's towers.
        let k = if height < 20.0 { 0.55 } else { 0.3 };
        let tint = [1.0 - k + k * c[0] / lum, 1.0 - k + k * c[1] / lum, 1.0 - k + k * c[2] / lum];
        let base = look.base as f32;
        let (z0, z1) = (b.z0 as f32, b.z1 as f32);
        let mat = [K_FACADE, seed, base, z1];
        let uv = [ft as f32, if z0 <= base + 0.5 { 1.0 } else { 0.0 }];
        for e in 0..poly.len() {
            let (p, q) = (poly[e], poly[(e + 1) % poly.len()]);
            let (ex, ey) = ((q[0] - p[0]) as f32, (q[1] - p[1]) as f32);
            let l = (ex * ex + ey * ey).sqrt();
            if l < 0.05 {
                continue;
            }
            let (dx, dy) = (ex / l, ey / l);
            let (px, py, qx, qy) = (p[0] as f32, p[1] as f32, q[0] as f32, q[1] as f32);
            let ncol = (l / col_nom).round().max(1.0);
            let fac = [px * dx + py * dy, l / ncol, floor_h, l];
            self.quad([dy, -dx, 0.0], [[px, py, z0], [qx, qy, z0], [qx, qy, z1], [px, py, z1]], tint, uv, mat, fac);
        }
        let (x0, x1) = (b.x0 as f32, b.x1 as f32);
        let (y0, y1) = (b.y0 as f32, b.y1 as f32);
        let roof_t = if (seed * 53.0).fract() < 0.55 { 0.0 } else { 1.0 };
        let rg = 0.55 + 0.6 * (seed * 71.0).fract();
        let roof_tint = [rg * (0.85 + 0.15 * tint[0]), rg * (0.85 + 0.15 * tint[1]), rg * (0.85 + 0.15 * tint[2])];
        self.cap(&poly, z1, true, roof_tint, [K_ROOF, seed, roof_t, 0.0], [x0, y0, x1, y1]);
        if b.z1 < look.top - 0.05 || x1 - x0 < 12.0 || y1 - y0 < 12.0 {
            return;
        }
        let mut r = Rng::new((seed as f64 * 1e6) as u64 + b.p0 as u64 * 31 + 7);
        let n = 1 + (r.f() * 4.0) as usize;
        for _ in 0..n {
            let (sx, sy) = (r.range(1.2, 3.0), r.range(1.2, 3.0));
            let sz = r.range(0.8, 1.6);
            let c = [r.range(b.x0, b.x1), r.range(b.y0, b.y1)];
            if !inside_convex(&poly, c, 3.0 + sx.max(sy)) {
                continue;
            }
            let g = r.range(0.75, 1.05) as f32;
            let metal = if r.f() < 0.5 { 0.6 } else { 0.0 };
            self.obox(c, [1.0, 0.0], sx, sy, b.z1, b.z1 + sz, [g, g, g * 1.02], metal);
        }
    }
}

// ---------------------------------------------------------------- Bay Bridge and freeways

/// The Bay Bridge West Span as it looks: a deck slab per collision piece, two main cables and suspenders.
/// Its collision curtain (water to cables) is not drawn.
fn bay_bridge(w: &World, m: &mut Mesh) {
    let pieces: Vec<&Building> = w.boxes.iter().filter(|b| b.kind == Kind::Bridge).collect();
    if pieces.len() < 2 {
        return;
    }
    let cen: Vec<[f64; 2]> = pieces
        .iter()
        .map(|b| {
            let o = w.outline(b);
            let n = o.len() as f64;
            [o.iter().map(|q| q[0]).sum::<f64>() / n, o.iter().map(|q| q[1]).sum::<f64>() / n]
        })
        .collect();
    let k = cen.len() as f64;
    let (cx, cy) = (cen.iter().map(|c| c[0]).sum::<f64>() / k, cen.iter().map(|c| c[1]).sum::<f64>() / k);
    let (mut sxx, mut sxy, mut syy) = (0.0, 0.0, 0.0);
    for c in &cen {
        let (dx, dy) = (c[0] - cx, c[1] - cy);
        sxx += dx * dx;
        sxy += dx * dy;
        syy += dy * dy;
    }
    let th = 0.5 * (2.0 * sxy).atan2(sxx - syy);
    let (ux, uy) = (th.cos(), th.sin());
    let (nx, ny) = (-uy, ux);
    let mut order: Vec<usize> = (0..pieces.len()).collect();
    order.sort_by(|&a, &b| {
        let pa = (cen[a][0] - cx) * ux + (cen[a][1] - cy) * uy;
        let pb = (cen[b][0] - cx) * ux + (cen[b][1] - cy) * uy;
        pa.partial_cmp(&pb).unwrap()
    });
    // Per piece: centre, half-width across the bridge, cable and deck height.
    let info: Vec<([f64; 2], f64, f64, f64)> = order
        .iter()
        .map(|&i| {
            let b = pieces[i];
            let c = cen[i];
            let hw = w.outline(b).iter().map(|q| ((q[0] - c[0]) * nx + (q[1] - c[1]) * ny).abs()).fold(0.0, f64::max);
            let cable = b.z1 - 1.0;
            let deck = (b.z1 - 8.0).min(66.0).max(w.terrain(c[0], c[1]) + 6.0);
            (c, hw, cable, deck)
        })
        .collect();
    for (k, &i) in order.iter().enumerate() {
        let o = w.outline(pieces[i]);
        let (c, hw, cable, deck) = info[k];
        let (d0, d1) = ((deck - 7.0) as f32, deck as f32);
        for e in 0..o.len() {
            m.wall(o[e], o[(e + 1) % o.len()], [d0, d0, d1, d1], STEEL, clutter(0.4));
        }
        m.cap(&o, d1, true, ROADWAY, clutter(0.0), [0.0; 4]);
        m.cap(&o, d0, false, STEEL, clutter(0.4), [0.0; 4]);
        for side in [-1.0, 1.0] {
            let off = side * (hw - 1.5).max(1.0);
            let p = [c[0] + nx * off, c[1] + ny * off];
            if cable - deck > 4.0 {
                m.tube([p[0], p[1], deck], [p[0], p[1], cable], 0.25, STEEL, 0.6);
            }
            if let Some(&(c2, hw2, cable2, _)) = info.get(k + 1) {
                let off2 = side * (hw2 - 1.5).max(1.0);
                m.tube([p[0], p[1], cable], [c2[0] + nx * off2, c2[1] + ny * off2, cable2], 0.6, STEEL, 0.6);
            }
        }
    }
}

/// Elevated freeways as they look: a deck 6 m below the top of their collision curtain (which reaches 24 m
/// above the ground) on one pillar per slice. The curtains are not drawn.
fn viaducts(w: &World, m: &mut Mesh) {
    for b in w.boxes.iter().filter(|b| b.kind == Kind::Viaduct) {
        let o = w.outline(b);
        let n = o.len();
        let top = (b.z1 - 6.0).max(b.z0 + 8.5);
        let deck0 = top - 2.2;
        for e in 0..n {
            m.wall(o[e], o[(e + 1) % n], [deck0 as f32, deck0 as f32, top as f32, top as f32], CONCRETE, clutter(0.0));
        }
        m.cap(&o, top as f32, true, ROADWAY, clutter(0.0), [0.0; 4]);
        m.cap(&o, deck0 as f32, false, CONCRETE, clutter(0.0), [0.0; 4]);
        let c = [o.iter().map(|q| q[0]).sum::<f64>() / n as f64, o.iter().map(|q| q[1]).sum::<f64>() / n as f64];
        m.obox(c, [1.0, 0.0], 1.2, 1.2, b.z0, deck0, CONCRETE, 0.0);
    }
}

// ---------------------------------------------------------------- Golden Gate Bridge

/// South tower centre (map metres), the unit vector to the north tower, main and side spans (m).
const GG_S: [f64; 2] = [-6432.1, 2515.1];
const GG_U: [f64; 2] = [-0.09788, 0.99520];
const GG_MAIN: f64 = 1280.1;
const GG_SIDE: f64 = 343.0;
/// Deck extent along the axis from the south tower: the San Francisco approach to the north abutment.
const GG_DECK: (f64, f64) = (-676.0, 1660.0);
/// One tower's parts from OpenStreetMap (both towers' parts agree to 5 cm): centre and half-size across the
/// bridge, centre and half-size along it, bottom and top above the water (m).
const GG_TOWER: [[f64; 6]; 18] = [
    [-13.75, 4.81, -0.01, 7.82, 13.0, 21.0],
    [13.72, 4.81, -0.03, 7.82, 13.0, 21.0],
    [-13.74, 3.77, 0.01, 6.91, 21.0, 74.0],
    [13.73, 3.77, -0.01, 6.91, 21.0, 74.0],
    [-0.01, 9.98, -0.01, 1.88, 24.0, 26.0],
    [-0.01, 9.98, -0.01, 1.88, 50.0, 52.0],
    [-13.74, 3.77, 0.01, 5.84, 74.0, 123.0],
    [13.73, 3.77, -0.01, 5.84, 74.0, 123.0],
    [-0.01, 9.98, -0.01, 1.88, 111.0, 121.0],
    [-13.74, 3.77, 0.02, 4.89, 123.0, 162.0],
    [13.73, 3.77, 0.01, 4.89, 123.0, 162.0],
    [-0.01, 9.98, -0.01, 1.88, 151.0, 161.0],
    [-13.72, 2.69, 0.02, 4.89, 162.0, 195.0],
    [13.74, 2.69, 0.01, 4.89, 162.0, 195.0],
    [0.01, 11.04, -0.01, 1.87, 185.0, 193.0],
    [-13.73, 1.62, 0.02, 3.74, 195.0, 225.0],
    [13.74, 1.62, 0.00, 3.74, 195.0, 225.0],
    [-0.01, 12.13, -0.01, 1.86, 215.0, 223.0],
];
/// Cable planes across the axis (m), cable top at the towers and suspender spacing (50 ft).
const GG_CABLE: f64 = 13.73;
const GG_SUSP: f64 = 15.24;

/// Point `s` along the axis from the south tower and `a` across it (left positive).
fn gg_at(s: f64, a: f64) -> [f64; 2] {
    [GG_S[0] + GG_U[0] * s - GG_U[1] * a, GG_S[1] + GG_U[1] * s + GG_U[0] * a]
}

/// Roadway height at `s`: cambered from 70 m at the towers to 75 m mid-span (67 m clearance below the
/// stiffening truss), 66 m at the anchorages, easing down the approaches.
fn gg_deck(s: f64) -> f64 {
    let w = SF_WATER;
    if (0.0..=GG_MAIN).contains(&s) {
        let t = (s - 0.5 * GG_MAIN) / (0.5 * GG_MAIN);
        w + 70.0 + 5.0 * (1.0 - t * t)
    } else if s < 0.0 {
        if s >= -GG_SIDE {
            w + 70.0 + 4.0 * s / GG_SIDE
        } else {
            w + 66.0 - 4.0 * (-GG_SIDE - s) / (-GG_SIDE - GG_DECK.0)
        }
    } else {
        let t = s - GG_MAIN;
        if t <= GG_SIDE {
            w + 70.0 - 4.0 * t / GG_SIDE
        } else {
            w + 66.0 - 4.0 * (t - GG_SIDE) / (GG_DECK.1 - GG_MAIN - GG_SIDE)
        }
    }
}

/// Main-cable height at `s`: a parabola from the tower tops to just above the deck mid-span, and the side
/// spans sagging down to the anchorages at deck level.
fn gg_cable(s: f64) -> f64 {
    let top = SF_WATER + 225.0;
    if (0.0..=GG_MAIN).contains(&s) {
        let t = (s - 0.5 * GG_MAIN) / (0.5 * GG_MAIN);
        let low = gg_deck(0.5 * GG_MAIN) + 1.5;
        low + (top - low) * t * t
    } else {
        let t = if s < 0.0 { (s + GG_SIDE) / GG_SIDE } else { (GG_MAIN + GG_SIDE - s) / GG_SIDE };
        let anchor = gg_deck(if s < 0.0 { -GG_SIDE } else { GG_MAIN + GG_SIDE }) + 2.0;
        anchor + (top - anchor) * t - 12.0 * 4.0 * t * (1.0 - t)
    }
}

/// The Golden Gate Bridge, visual only (it stands 3.4 km outside the flyable square): towers from
/// OpenStreetMap, piers, the deck and stiffening truss, main cables and suspenders, the anchorage pylons,
/// the Fort Point arch and the San Francisco approach, in International Orange.
fn golden_gate(m: &mut Mesh, dem: &Option<Vec<f32>>) {
    let ground = |s: f64, a: f64| {
        let p = gg_at(s, a);
        dem_at(dem, p[0], p[1])
    };
    let w = SF_WATER;
    let u = GG_U;
    for s0 in [0.0, GG_MAIN] {
        // Concrete pier up to the legs' pedestals, then the tower.
        m.obox(gg_at(s0, 0.0), u, 16.0, 24.0, w - 2.0, w + 13.0, CONCRETE, 0.0);
        for p in GG_TOWER {
            m.obox(gg_at(s0 + p[2], p[0]), u, p[3], p[1], w + p[4], w + p[5], ORANGE, 0.0);
        }
    }
    // Deck: stiffening truss on the suspended spans, a shallower girder on the approaches.
    let step = 10.0;
    let mut s = GG_DECK.0;
    while s < GG_DECK.1 - 1e-6 {
        let s1 = (s + step).min(GG_DECK.1);
        let suspended = s >= -GG_SIDE && s1 <= GG_MAIN + GG_SIDE;
        let (hw, depth) = if suspended { (GG_CABLE + 0.5, 7.6) } else { (12.0, 4.0) };
        let (t0, t1) = (gg_deck(s), gg_deck(s1));
        let (l0, l1, r0, r1) = (gg_at(s, hw), gg_at(s1, hw), gg_at(s, -hw), gg_at(s1, -hw));
        let z = |a: f64, b: f64, c: f64, d: f64| [a as f32, b as f32, c as f32, d as f32];
        m.wall(r0, r1, z(t0 - depth, t1 - depth, t0 + 1.2, t1 + 1.2), ORANGE, clutter(0.0));
        m.wall(l1, l0, z(t1 - depth, t0 - depth, t1 + 1.2, t0 + 1.2), ORANGE, clutter(0.0));
        let ring = |a: [f64; 2], b: [f64; 2], c: [f64; 2], d: [f64; 2], za: f64, zb: f64| {
            [[a[0] as f32, a[1] as f32, za as f32], [b[0] as f32, b[1] as f32, zb as f32], [c[0] as f32, c[1] as f32, zb as f32], [d[0] as f32, d[1] as f32, za as f32]]
        };
        m.quad([0.0, 0.0, 1.0], ring(r0, r1, l1, l0, t0, t1), ROADWAY, [0.0; 2], clutter(0.0), [0.0; 4]);
        m.quad([0.0, 0.0, -1.0], ring(l0, l1, r1, r0, t0 - depth, t1 - depth), ORANGE, [0.0; 2], clutter(0.0), [0.0; 4]);
        s = s1;
    }
    // Main cables and suspenders, from anchorage to anchorage.
    for side in [-1.0, 1.0] {
        let a = side * GG_CABLE;
        let mut s = -GG_SIDE;
        while s < GG_MAIN + GG_SIDE - 1e-6 {
            let s1 = (s + GG_SUSP).min(GG_MAIN + GG_SIDE);
            let (p, q) = (gg_at(s, a), gg_at(s1, a));
            m.tube([p[0], p[1], gg_cable(s)], [q[0], q[1], gg_cable(s1)], 0.6, ORANGE, 0.0);
            let near_tower = s1.abs() < 8.0 || (s1 - GG_MAIN).abs() < 8.0;
            if s1 < GG_MAIN + GG_SIDE - 1.0 && !near_tower && gg_cable(s1) - gg_deck(s1) > 3.0 {
                m.tube([q[0], q[1], gg_deck(s1)], [q[0], q[1], gg_cable(s1)], 0.15, ORANGE, 0.0);
            }
            s = s1;
        }
    }
    // Anchorage pylons at the ends of the side spans, the Fort Point arch south of them, and the approach
    // piers.
    for (sc, ha, hc) in [(-GG_SIDE + 4.0, 20.0, 25.0), (GG_MAIN + GG_SIDE, 22.0, 26.0), (-459.0, 6.0, 16.0)] {
        let g = ground(sc, 0.0).min(gg_deck(sc) - 10.0);
        m.obox(gg_at(sc, 0.0), u, ha, hc, g - 2.0, gg_deck(sc) + 10.0, CONCRETE, 0.0);
    }
    for a in [-10.0, 10.0] {
        let (sa, sb) = (-459.0 + 6.0, -GG_SIDE + 4.0 - 20.0);
        let n = 16;
        for k in 0..n {
            let rib = |t: f64| {
                let s = sa + (sb - sa) * t;
                let g = ground(s, a);
                let p = gg_at(s, a);
                [p[0], p[1], g + (gg_deck(s) - 4.0 - g) * (std::f64::consts::PI * t).sin()]
            };
            m.tube(rib(k as f64 / n as f64), rib((k + 1) as f64 / n as f64), 1.4, ORANGE, 0.0);
        }
    }
    let mut s = GG_DECK.0 + 20.0;
    while s < -459.0 - 10.0 {
        let g = ground(s, 0.0).min(gg_deck(s) - 4.0);
        m.obox(gg_at(s, 0.0), u, 2.0, 9.0, g - 2.0, gg_deck(s) - 4.0, CONCRETE, 0.0);
        s += 45.0;
    }
}

/// Everything San Francisco draws with the building shader: footprint buildings, bridge towers, the Bay
/// Bridge, the elevated freeways and the Golden Gate Bridge.
pub fn building_mesh(w: &World) -> (Vec<PV>, Vec<u32>) {
    let mut m = Mesh::default();
    let looks = render_looks(w);
    for (k, b) in w.boxes.iter().enumerate() {
        let Some(look) = looks[k] else { continue };
        match b.kind {
            Kind::Building => m.building(w, b, look),
            Kind::BridgeTower => m.prism(&w.outline(b), b.z0, b.z1, STEEL, 0.5),
            Kind::Bridge | Kind::Viaduct => {}
        }
    }
    bay_bridge(w, &mut m);
    viaducts(w, &mut m);
    golden_gate(&mut m, &backdrop_dem());
    (m.v, m.i)
}
