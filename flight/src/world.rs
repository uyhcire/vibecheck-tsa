//! Procedural city + terrain, the true collision geometry, and the 2.5D
//! clearance maps used by the safety filter.
//!
//! Truth: terrain is the piecewise-linear surface over a 20 m vertex grid
//! (each quad split along the same diagonal the renderer uses), buildings
//! are axis-aligned boxes. Collisions are always checked against this.
//!
//! Safety map: a 5 m max-height raster of the truth, dilated sideways by
//! `LAT_CELLS` cells and raised by `VERT_MARGIN`. A point with
//! `z - Hc(cell) >= 0` is at least `VERT_MARGIN` above anything within
//! `LAT_CELLS*CELL` metres horizontally. Path segments are checked against
//! every cell they cross (`swept_max`), so the guarantee covers the whole
//! continuous path, not just samples. Off-map is a wall.
//!
//! New plans are accepted against `hc_acc`, dilated one cell more than the
//! `hc` map that invariant re-checks use, so a re-check of a path within one
//! cell (5 m) of a verified one cannot fail on lateral grounds.

use std::sync::OnceLock;

pub const MAP_HALF: f64 = 3000.0;
pub const CELL: f64 = 5.0;
pub const NC: usize = 1200;
pub const TSP: f64 = 20.0;
pub const TN: usize = 301;
pub const LAT_CELLS: usize = 3;
/// Guaranteed lateral margin of the cell lookup.
pub const LAT_MARGIN: f64 = LAT_CELLS as f64 * CELL;
pub const VERT_MARGIN: f64 = 10.0;
pub const WALL: f32 = 1.0e5;
/// Aircraft modelled as a sphere of this radius (half the wingspan).
pub const R_BODY: f64 = 4.5;
pub const CITY_HALF: f64 = 1200.0;
pub const STREET_PITCH: f64 = 120.0;
const BUCKET: f64 = 40.0;
const NB: usize = 150;

/// Robust (Phase 3) maps: extra lateral dilation, in cells (check maps; the
/// acceptance maps use one more cell each).
pub const ROBUST_CELLS: [usize; 4] = [5, 7, 10, 13];

// ---------------------------------------------------------------- RNG / noise

#[derive(Clone)]
pub struct Rng(pub u64);
impl Rng {
    pub fn new(seed: u64) -> Self {
        let mut r = Rng(seed ^ 0x9E37_79B9_7F4A_7C15);
        r.next_u64();
        r
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn f(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
    pub fn range(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * self.f()
    }
    pub fn chance(&mut self, p: f64) -> bool {
        self.f() < p
    }
}

fn hash2(seed: u64, ix: i64, iy: i64) -> f64 {
    let mut r = Rng(seed ^ (ix as u64).wrapping_mul(0x9E37_79B1) ^ (iy as u64).wrapping_mul(0x85EB_CA77_C2B2_AE63));
    r.next_u64();
    r.f() * 2.0 - 1.0
}

fn vnoise(seed: u64, x: f64, y: f64) -> f64 {
    let ix = x.floor();
    let iy = y.floor();
    let fx = x - ix;
    let fy = y - iy;
    let q = |t: f64| t * t * t * (t * (t * 6.0 - 15.0) + 10.0);
    let (ux, uy) = (q(fx), q(fy));
    let (ix, iy) = (ix as i64, iy as i64);
    let a = hash2(seed, ix, iy);
    let b = hash2(seed, ix + 1, iy);
    let c = hash2(seed, ix, iy + 1);
    let d = hash2(seed, ix + 1, iy + 1);
    a + (b - a) * ux + (c - a) * uy + (a - b - c + d) * ux * uy
}

fn fbm(seed: u64, x: f64, y: f64, oct: u32) -> f64 {
    let (mut s, mut amp, mut f, mut norm) = (0.0, 1.0, 1.0, 0.0);
    for o in 0..oct {
        s += amp * vnoise(seed.wrapping_add(o as u64 * 7919), x * f, y * f);
        norm += amp;
        amp *= 0.5;
        f *= 2.03;
    }
    s / norm
}

pub fn smoothstep(e0: f64, e1: f64, x: f64) -> f64 {
    let t = ((x - e0) / (e1 - e0)).clamp(0.0, 1.0);
    t * t * (3.0 - 2.0 * t)
}

// ---------------------------------------------------------------- world

#[derive(Clone, Copy, Debug)]
pub struct Building {
    pub x0: f64,
    pub x1: f64,
    pub y0: f64,
    pub y1: f64,
    pub z0: f64,
    pub z1: f64,
    /// 0..1 colour variation for rendering.
    pub tint: f32,
    /// Index of the lot this box belongs to (tiers of a tower share it).
    pub lot: u32,
}

impl Building {
    pub fn dist(&self, p: [f64; 3]) -> f64 {
        let dx = (self.x0 - p[0]).max(0.0).max(p[0] - self.x1);
        let dy = (self.y0 - p[1]).max(0.0).max(p[1] - self.y1);
        let dz = (self.z0 - p[2]).max(0.0).max(p[2] - self.z1);
        (dx * dx + dy * dy + dz * dz).sqrt()
    }
}

pub struct World {
    pub seed: u64,
    /// Terrain vertex heights, `TN x TN`, index `j*TN + i`.
    pub terr: Vec<f32>,
    pub boxes: Vec<Building>,
    /// Raw max height of the truth geometry per 5 m cell.
    pub raw: Vec<f32>,
    /// Base clearance map (dilated + vertical margin), used for re-checks.
    pub hc: Vec<f32>,
    /// One cell wider: used to accept new plans.
    pub hc_acc: Vec<f32>,
    robust: OnceLock<[Vec<Vec<f32>>; 2]>,
    buckets: Vec<Vec<u32>>,
    pub tallest: usize,
    pub parks: Vec<[f64; 4]>,
    pub street_w: Vec<f64>,
    /// Ridge crest line `y` and half-length in x.
    pub ridge_y: f64,
}

pub fn street_x(k: usize) -> f64 {
    -CITY_HALF + STREET_PITCH * k as f64
}

impl World {
    pub fn new(seed: u64) -> World {
        let mut w = World {
            seed,
            terr: vec![0.0; TN * TN],
            boxes: Vec::new(),
            raw: vec![0.0; NC * NC],
            hc: vec![0.0; NC * NC],
            hc_acc: Vec::new(),
            robust: OnceLock::new(),
            buckets: vec![Vec::new(); NB * NB],
            tallest: 0,
            parks: Vec::new(),
            street_w: Vec::new(),
            ridge_y: -2050.0,
        };
        w.gen_terrain();
        w.gen_city();
        w.rasterize();
        w.hc = dilate(&w.raw, LAT_CELLS, VERT_MARGIN as f32);
        w.hc_acc = dilate(&w.raw, LAT_CELLS + 1, VERT_MARGIN as f32);
        w.build_buckets();
        w
    }

    fn terrain_fn(&self, x: f64, y: f64) -> f64 {
        let s = self.seed;
        let m = x.abs().max(y.abs());
        let city = 1.0 - smoothstep(1250.0, 1650.0, m);
        let base = 6.0 + 5.0 * fbm(s, x / 900.0, y / 900.0, 4);
        let hill_amp = (1.0 - city) * (60.0 + 45.0 * fbm(s + 1, x / 600.0, y / 600.0, 3));
        let valley = smoothstep(-1950.0, -1820.0, y)
            * (1.0 - smoothstep(-1300.0, -1200.0, y))
            * (1.0 - smoothstep(1400.0, 1750.0, x.abs()));
        let hills = hill_amp * (0.5 + 0.5 * fbm(s + 2, x / 450.0, y / 450.0, 3)).max(0.0) * (1.0 - 0.9 * valley);
        let ridge = 285.0
            * (-((y - self.ridge_y) / 150.0).powi(2)).exp()
            * (1.0 - smoothstep(1500.0, 1950.0, x.abs()))
            * (0.92 + 0.08 * fbm(s + 4, x / 200.0, 0.0, 2));
        let rim_t = smoothstep(2250.0, 2880.0, m);
        let rim = rim_t * (780.0 + 130.0 * fbm(s + 3, x / 380.0, y / 380.0, 3));
        base + hills + ridge + rim
    }

    fn gen_terrain(&mut self) {
        for j in 0..TN {
            for i in 0..TN {
                let x = -MAP_HALF + i as f64 * TSP;
                let y = -MAP_HALF + j as f64 * TSP;
                self.terr[j * TN + i] = self.terrain_fn(x, y) as f32;
            }
        }
    }

    /// True terrain height: barycentric on the render triangulation.
    #[inline]
    pub fn terrain(&self, x: f64, y: f64) -> f64 {
        let fx = ((x + MAP_HALF) / TSP).clamp(0.0, (TN - 1) as f64 - 1e-9);
        let fy = ((y + MAP_HALF) / TSP).clamp(0.0, (TN - 1) as f64 - 1e-9);
        let i = fx as usize;
        let j = fy as usize;
        let u = fx - i as f64;
        let v = fy - j as f64;
        let h00 = self.terr[j * TN + i] as f64;
        let h10 = self.terr[j * TN + i + 1] as f64;
        let h01 = self.terr[(j + 1) * TN + i] as f64;
        let h11 = self.terr[(j + 1) * TN + i + 1] as f64;
        if u >= v {
            h00 + u * (h10 - h00) + v * (h11 - h10)
        } else {
            h00 + v * (h01 - h00) + u * (h11 - h01)
        }
    }

    pub fn is_park(&self, x: f64, y: f64) -> bool {
        self.parks.iter().any(|p| x >= p[0] && x <= p[1] && y >= p[2] && y <= p[3])
    }

    fn add_box(&mut self, x0: f64, x1: f64, y0: f64, y1: f64, h: f64, tint: f32, lot: u32) {
        let mut zmin = f64::INFINITY;
        for (x, y) in [(x0, y0), (x1, y0), (x0, y1), (x1, y1)] {
            zmin = zmin.min(self.terrain(x, y));
        }
        let zc = self.terrain(0.5 * (x0 + x1), 0.5 * (y0 + y1));
        self.boxes.push(Building { x0, x1, y0, y1, z0: zmin - 1.5, z1: zc + h, tint, lot });
    }

    /// A building of height `h`; tall ones get setback tiers.
    fn add_building(&mut self, x0: f64, x1: f64, y0: f64, y1: f64, h: f64, tint: f32, lot: u32) {
        if h < 110.0 {
            self.add_box(x0, x1, y0, y1, h, tint, lot);
            return;
        }
        let (cx, cy) = (0.5 * (x0 + x1), 0.5 * (y0 + y1));
        let (hx, hy) = (0.5 * (x1 - x0), 0.5 * (y1 - y0));
        for (f, s) in [(0.55, 1.0), (0.82, 0.72), (1.0, 0.46)] {
            self.add_box(cx - hx * s, cx + hx * s, cy - hy * s, cy + hy * s, h * f, tint, lot);
        }
    }

    fn gen_city(&mut self) {
        let mut rng = Rng::new(self.seed ^ 0xC17);
        let nlines = 21;
        self.street_w = (0..nlines).map(|k| if k % 5 == 0 { 40.0 } else { 28.0 }).collect();
        let park_blocks: [(usize, usize); 9] =
            [(6, 12), (6, 13), (7, 12), (7, 13), (14, 5), (3, 3), (16, 15), (12, 2), (2, 16)];
        let (dcx, dcy) = (60.0, 60.0);
        let mut lot = 0u32;
        for bj in 0..20 {
            for bi in 0..20 {
                let bx0 = street_x(bi) + self.street_w[bi] / 2.0;
                let bx1 = street_x(bi + 1) - self.street_w[bi + 1] / 2.0;
                let by0 = street_x(bj) + self.street_w[bj] / 2.0;
                let by1 = street_x(bj + 1) - self.street_w[bj + 1] / 2.0;
                if park_blocks.contains(&(bi, bj)) {
                    self.parks.push([bx0, bx1, by0, by1]);
                    continue;
                }
                let (cx, cy) = (0.5 * (bx0 + bx1), 0.5 * (by0 + by1));
                let r = ((cx - dcx).powi(2) + (cy - dcy).powi(2)).sqrt();
                let hmax = 10.0 + 440.0 * (-(r / 430.0).powi(2)).exp();
                if (bi, bj) == (10, 10) {
                    // The tallest tower, with a low podium around it.
                    self.add_box(bx0 + 4.0, bx1 - 4.0, by0 + 4.0, by1 - 4.0, 18.0, 0.5, lot);
                    lot += 1;
                    self.add_building(cx - 26.0, cx + 26.0, cy - 26.0, cy + 26.0, 450.0, 0.9, lot);
                    self.tallest = self.boxes.len() - 1;
                    lot += 1;
                    continue;
                }
                let (nx, ny, p_fill, tall) = if hmax > 120.0 {
                    if rng.chance(0.5) { (2, 1, 0.85, true) } else { (1, 2, 0.85, true) }
                } else if hmax > 25.0 {
                    (2, 2, 0.9, false)
                } else {
                    (3, 3, 0.72, false)
                };
                let lw = (bx1 - bx0) / nx as f64;
                let lh = (by1 - by0) / ny as f64;
                for ly in 0..ny {
                    for lx in 0..nx {
                        if !rng.chance(p_fill) {
                            continue;
                        }
                        let fx = rng.range(0.62, 0.9);
                        let fy = rng.range(0.62, 0.9);
                        let x0 = bx0 + lx as f64 * lw + lw * (1.0 - fx) * rng.f();
                        let y0 = by0 + ly as f64 * lh + lh * (1.0 - fy) * rng.f();
                        let (x1, y1) = (x0 + lw * fx, y0 + lh * fy);
                        let h = if tall {
                            hmax * rng.range(0.42, 0.95)
                        } else if hmax > 25.0 {
                            (hmax * rng.range(0.5, 1.0)).max(12.0)
                        } else {
                            rng.range(7.0, 16.0)
                        };
                        let tint = rng.f() as f32;
                        self.add_building(x0, x1, y0, y1, h, tint, lot);
                        lot += 1;
                    }
                }
            }
        }
    }

    fn rasterize(&mut self) {
        // Terrain: cells are aligned with quarter-quads, so the triangulation
        // diagonal only meets cell corners; the max over a cell is the max of
        // its four corners.
        let np = NC + 1;
        let mut corner = vec![0f32; np * np];
        for j in 0..np {
            for i in 0..np {
                corner[j * np + i] =
                    self.terrain(-MAP_HALF + i as f64 * CELL, -MAP_HALF + j as f64 * CELL) as f32;
            }
        }
        for j in 0..NC {
            for i in 0..NC {
                let a = corner[j * np + i]
                    .max(corner[j * np + i + 1])
                    .max(corner[(j + 1) * np + i])
                    .max(corner[(j + 1) * np + i + 1]);
                self.raw[j * NC + i] = a;
            }
        }
        for b in &self.boxes {
            let ci = |v: f64| (((v + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
            for j in ci(b.y0)..=ci(b.y1) {
                for i in ci(b.x0)..=ci(b.x1) {
                    let c = &mut self.raw[j * NC + i];
                    *c = c.max(b.z1 as f32);
                }
            }
        }
    }

    fn build_buckets(&mut self) {
        for (n, b) in self.boxes.iter().enumerate() {
            let bi = |v: f64| (((v + MAP_HALF) / BUCKET).floor().max(0.0) as usize).min(NB - 1);
            for j in bi(b.y0)..=bi(b.y1) {
                for i in bi(b.x0)..=bi(b.x1) {
                    self.buckets[j * NB + i].push(n as u32);
                }
            }
        }
    }

    /// Robust maps (lazily built): one per entry of `ROBUST_CELLS`;
    /// `[0]` for re-checks, `[1]` (one cell wider) for acceptance.
    pub fn robust_maps(&self, accept: bool) -> &Vec<Vec<f32>> {
        let m = self.robust.get_or_init(|| {
            let mk = |extra: usize| ROBUST_CELLS.iter().map(|&r| dilate(&self.raw, r + extra, VERT_MARGIN as f32)).collect();
            [mk(0), mk(1)]
        });
        &m[accept as usize]
    }

    /// Distance from `p` to the nearest building surface, capped at `cap`.
    pub fn building_dist(&self, p: [f64; 3], cap: f64) -> f64 {
        let lo = |v: f64| (((v - cap + MAP_HALF) / BUCKET).floor().max(0.0) as usize).min(NB - 1);
        let hi = |v: f64| (((v + cap + MAP_HALF) / BUCKET).floor().max(0.0) as usize).min(NB - 1);
        let mut d = cap;
        for j in lo(p[1])..=hi(p[1]) {
            for i in lo(p[0])..=hi(p[0]) {
                for &n in &self.buckets[j * NB + i] {
                    d = d.min(self.boxes[n as usize].dist(p));
                }
            }
        }
        d
    }

    /// True clearance of the aircraft body (negative = collision).
    pub fn true_clearance(&self, p: [f64; 3]) -> f64 {
        if p[0].abs() > MAP_HALF || p[1].abs() > MAP_HALF {
            return -1.0;
        }
        let mut c = p[2] - R_BODY - self.terrain(p[0], p[1]);
        for k in 0..8 {
            let a = k as f64 * std::f64::consts::FRAC_PI_4;
            let t = self.terrain(p[0] + R_BODY * a.cos(), p[1] + R_BODY * a.sin());
            c = c.min(p[2] - t);
        }
        c.min(self.building_dist(p, 200.0) - R_BODY)
    }

    /// Ground or roof height directly below `(x, y)` (raw cell max).
    pub fn surface(&self, x: f64, y: f64) -> f64 {
        let i = (((x + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
        let j = (((y + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
        self.raw[j * NC + i] as f64
    }

    pub fn tallest_center(&self) -> [f64; 3] {
        let b = &self.boxes[self.tallest];
        [0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1), b.z1]
    }
}

/// Bilinear lookup in a clearance map; out of bounds is a wall.
#[inline]
pub fn hc_at(map: &[f32], x: f64, y: f64) -> f64 {
    let fx = (x + MAP_HALF) / CELL - 0.5;
    let fy = (y + MAP_HALF) / CELL - 0.5;
    let ix = fx.floor();
    let iy = fy.floor();
    let tx = fx - ix;
    let ty = fy - iy;
    let (ix, iy) = (ix as i64, iy as i64);
    let n = NC as i64;
    let get = |i: i64, j: i64| -> f64 {
        if i < 0 || j < 0 || i >= n || j >= n {
            WALL as f64
        } else {
            map[(j * n + i) as usize] as f64
        }
    };
    let a = get(ix, iy);
    let b = get(ix + 1, iy);
    let c = get(ix, iy + 1);
    let d = get(ix + 1, iy + 1);
    (a * (1.0 - tx) + b * tx) * (1.0 - ty) + (c * (1.0 - tx) + d * tx) * ty
}

#[inline]
fn cell_at(map: &[f32], i: i64, j: i64) -> f64 {
    let n = NC as i64;
    if i < 0 || j < 0 || i >= n || j >= n {
        WALL as f64
    } else {
        map[(j * n + i) as usize] as f64
    }
}

/// Max of the map over every cell the segment (x0,y0)-(x1,y1) crosses.
#[inline]
pub fn swept_max(map: &[f32], x0: f64, y0: f64, x1: f64, y1: f64) -> f64 {
    let (fx0, fy0) = ((x0 + MAP_HALF) / CELL, (y0 + MAP_HALF) / CELL);
    let (fx1, fy1) = ((x1 + MAP_HALF) / CELL, (y1 + MAP_HALF) / CELL);
    let (mut i, mut j) = (fx0.floor() as i64, fy0.floor() as i64);
    let (i1, j1) = (fx1.floor() as i64, fy1.floor() as i64);
    let mut m = cell_at(map, i, j);
    let (dx, dy) = (fx1 - fx0, fy1 - fy0);
    let (si, sj) = (if dx > 0.0 { 1 } else { -1 }, if dy > 0.0 { 1 } else { -1 });
    let mut tmx = if dx != 0.0 { ((if si > 0 { i + 1 } else { i }) as f64 - fx0) / dx } else { f64::INFINITY };
    let mut tmy = if dy != 0.0 { ((if sj > 0 { j + 1 } else { j }) as f64 - fy0) / dy } else { f64::INFINITY };
    let tdx = if dx != 0.0 { 1.0 / dx.abs() } else { f64::INFINITY };
    let tdy = if dy != 0.0 { 1.0 / dy.abs() } else { f64::INFINITY };
    let n = (i1 - i).abs() + (j1 - j).abs();
    for _ in 0..n {
        if tmx < tmy {
            i += si;
            tmx += tdx;
        } else {
            j += sj;
            tmy += tdy;
        }
        m = m.max(cell_at(map, i, j));
    }
    m
}

/// Square (Chebyshev) max filter of radius `r` cells, out-of-map = wall,
/// then add the vertical margin.
pub fn dilate(raw: &[f32], r: usize, vm: f32) -> Vec<f32> {
    let n = NC as i64;
    let r = r as i64;
    let mut tmp = vec![0f32; NC * NC];
    for j in 0..n {
        for i in 0..n {
            let mut m = f32::MIN;
            for d in -r..=r {
                let ii = i + d;
                let v = if ii < 0 || ii >= n { WALL } else { raw[(j * n + ii) as usize] };
                m = m.max(v);
            }
            tmp[(j * n + i) as usize] = m;
        }
    }
    let mut out = vec![0f32; NC * NC];
    for j in 0..n {
        for i in 0..n {
            let mut m = f32::MIN;
            for d in -r..=r {
                let jj = j + d;
                let v = if jj < 0 || jj >= n { WALL } else { tmp[(jj * n + i) as usize] };
                m = m.max(v);
            }
            out[(j * n + i) as usize] = m + vm;
        }
    }
    out
}
