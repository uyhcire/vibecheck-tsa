//! The maps (terrain + buildings), the true collision geometry, and the 2.5D
//! clearance maps used by the safety filter. Two maps share all of this:
//! the procedural grid city (`MapId::Grid`) and San Francisco, built from
//! DataSF footprints, OpenStreetMap and USGS terrain (`MapId::SanFrancisco`,
//! see `data/sf/`).
//!
//! Truth: terrain is the piecewise-linear surface over a 20 m vertex grid
//! (each quad split along the same diagonal the renderer uses). Buildings
//! are vertical prisms: axis-aligned boxes in the grid city, convex polygon
//! footprints in San Francisco. Collisions are always checked against this.
//!
//! Safety checks: buildings are checked exactly, as the distance from each
//! predicted path segment to each nearby prism (`seg_building_dist`). Terrain
//! uses a 2.5 m max-height raster, dilated sideways by `LAT_CELLS` cells and
//! raised by `VERT_MARGIN`: a point with `z - Hc(cell) >= 0` is at least
//! `VERT_MARGIN` above any terrain within `LAT_MARGIN` metres horizontally.
//! Path segments are checked against every terrain cell they cross, at the
//! segment's own height inside that cell (`swept_clear`), so both checks
//! cover the whole continuous path, not just samples. Off-map is a wall.
//!
//! New plans are accepted against `hc_acc`, dilated one cell more than the
//! `hc` map that invariant re-checks use, so a re-check of a path within one
//! cell of a verified one cannot fail on lateral grounds. (Building distance
//! is continuous, so it only needs a small extra margin for new plans.)

use crate::model::{wing_tips, State, WING_R, WING_TIP, X, Y, Z};
use std::sync::OnceLock;

/// The grid city's half-size (m): its map runs from -GRID_HALF to GRID_HALF on both axes. Other maps carry
/// their own bounds (`World::x0` ..).
pub const GRID_HALF: f64 = 3000.0;
/// Clearance-map cell (m) and terrain vertex spacing (m).
pub const CELL: f64 = 2.5;
pub const TSP: f64 = 20.0;
/// The grid city's half-size, clearance-map cells and terrain vertices per side under their names from before
/// the San Francisco map, for the grid-only tools (`gate/`, `Tools/city-export`, the Lean city gate's export).
pub const MAP_HALF: f64 = GRID_HALF;
pub const NC: usize = (2.0 * GRID_HALF / CELL) as usize;
pub const TN: usize = (2.0 * GRID_HALF / TSP) as usize + 1;
/// Lateral margin 7.5 m = aircraft radius 4.5 m + 3 m.
pub const LAT_CELLS: usize = 3;
/// Guaranteed lateral margin of the cell lookup.
pub const LAT_MARGIN: f64 = LAT_CELLS as f64 * CELL;
/// Vertical margin 6.5 m = aircraft radius 4.5 m + 2 m.
pub const VERT_MARGIN: f64 = 6.5;
pub const WALL: f32 = 1.0e5;
/// Aircraft modelled as a sphere of this radius (half the wingspan).
pub const R_BODY: f64 = 4.5;
pub const CITY_HALF: f64 = 1200.0;
pub const STREET_PITCH: f64 = 120.0;
const BUCKET: f64 = 40.0;
/// Most vertices a building footprint may have.
pub const MAX_POLY: usize = 32;
/// San Francisco water surface (NAVD88 m); terrain is never below it.
pub const SF_WATER: f64 = 1.0;
/// Street-axis field: cell size, blur radius (cells), and the street length
/// and coherence needed before escapes snap to a street direction.
const AXIS_CELL: f64 = 50.0;
const AXIS_BLUR: usize = 3;
const AXIS_MIN_LEN: f32 = 150.0;
const AXIS_MIN_COHERENCE: f32 = 0.6;

static SF_BIN: &[u8] = include_bytes!("../data/sf/sf_world.bin");

/// Which map to fly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapId {
    /// Procedural grid city with a ridge and a mountain rim.
    Grid,
    /// Downtown San Francisco, 6 km square around Kearny & Market.
    SanFrancisco,
}

impl MapId {
    pub const ALL: [MapId; 2] = [MapId::Grid, MapId::SanFrancisco];

    /// `grid` / `city`, or `sf` / `san-francisco`.
    pub fn parse(s: &str) -> Option<MapId> {
        match s.to_ascii_lowercase().as_str() {
            "grid" | "city" | "procedural" => Some(MapId::Grid),
            "sf" | "san-francisco" | "sanfrancisco" | "san_francisco" => Some(MapId::SanFrancisco),
            _ => None,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            MapId::Grid => "Grid city",
            MapId::SanFrancisco => "San Francisco",
        }
    }
    pub fn key(self) -> &'static str {
        match self {
            MapId::Grid => "grid",
            MapId::SanFrancisco => "sf",
        }
    }
    pub fn next(self) -> MapId {
        match self {
            MapId::Grid => MapId::SanFrancisco,
            MapId::SanFrancisco => MapId::Grid,
        }
    }
}

/// Robust (Phase 3) maps: extra lateral dilation, in cells (check maps; the
/// acceptance maps use one more cell each).
pub const ROBUST_CELLS: [usize; 4] = [5, 8, 12, 18];

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

/// What a prism stands for (rendering only; all are solid obstacles).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Building,
    /// Bay Bridge West Span: a curtain from the water up to its cables.
    Bridge,
    /// Elevated freeway: a curtain from the ground up past its deck.
    Viaduct,
    /// A bridge tower or anchorage (a building inside the bridge envelope).
    BridgeTower,
    /// Part of the Golden Gate Bridge (`golden_gate`), drawn by the renderer's own model of it.
    GoldenGate,
}

/// A vertical prism: footprint x [z0, z1]. `x0..y1` is the footprint's
/// bounding box; the footprint itself is that box (`pn == 0`) or the convex
/// polygon `World::pts[p0 .. p0 + pn]`, counter-clockwise.
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
    /// Index of the lot this box belongs to (tiers of a tower, or pieces of
    /// one footprint, share it).
    pub lot: u32,
    pub p0: u32,
    pub pn: u32,
    pub kind: Kind,
}

impl Building {
    fn aabb(x0: f64, x1: f64, y0: f64, y1: f64, z0: f64, z1: f64, tint: f32, lot: u32) -> Building {
        Building { x0, x1, y0, y1, z0, z1, tint, lot, p0: 0, pn: 0, kind: Kind::Building }
    }
}

/// An OpenStreetMap street centreline (San Francisco).
#[derive(Clone, Debug)]
pub struct Street {
    /// Index into `STREET_CLASSES`.
    pub class: u8,
    pub bridge: bool,
    /// Index into `World::street_names`.
    pub name: u16,
    pub pts: Vec<[f64; 2]>,
}

pub const STREET_CLASSES: [&str; 11] = [
    "motorway",
    "trunk",
    "primary",
    "secondary",
    "tertiary",
    "unclassified",
    "residential",
    "motorway_link",
    "trunk_link",
    "primary_link",
    "secondary_link",
];

impl Street {
    /// A city street at ground level: not a motorway, ramp or bridge. (Trunk
    /// roads count: in San Francisco they are surface streets such as Van
    /// Ness Avenue and Lombard Street, signed as US-101.)
    pub fn is_surface(&self) -> bool {
        (1..=6).contains(&self.class) && !self.bridge
    }
}

/// A straight street fitted as a line: from `p0`, `len` metres along `dir`.
#[derive(Clone, Copy, Debug)]
pub struct StreetLine {
    pub p0: [f64; 2],
    pub dir: f64,
    pub len: f64,
    /// RMS distance of the street's points from the line (m).
    pub rms: f64,
}

pub struct World {
    pub map: MapId,
    pub seed: u64,
    /// The flyable rectangle (map metres); outside it is a wall.
    pub x0: f64,
    pub y0: f64,
    pub x1: f64,
    pub y1: f64,
    /// Terrain vertices across and up (`TSP` apart from (x0, y0)).
    pub tnx: usize,
    pub tny: usize,
    /// Terrain vertex heights, `tnx x tny`, index `j*tnx + i`.
    pub terr: Vec<f32>,
    pub boxes: Vec<Building>,
    /// Raw max height of the truth geometry (terrain + buildings) per cell.
    pub raw: CellMap,
    /// Raw max terrain height per cell (the safety maps are built from it).
    pub raw_terr: CellMap,
    /// Highest raw cell (terrain or roof) on the map (m).
    pub raw_top: f64,
    /// Base clearance map (dilated + vertical margin), used for re-checks.
    pub hc: CellMap,
    /// One cell wider: used to accept new plans.
    pub hc_acc: CellMap,
    robust: OnceLock<[Vec<CellMap>; 2]>,
    /// Building buckets (`BUCKET` squares from (x0, y0)), `nbx x nby`.
    nbx: usize,
    nby: usize,
    buckets: Vec<Vec<u32>>,
    /// Tallest box top in each bucket (to skip buckets a segment is above).
    bucket_top: Vec<f32>,
    pub tallest: usize,
    /// Grid city only: parks, street widths, ridge crest line `y`.
    pub parks: Vec<[f64; 4]>,
    pub street_w: Vec<f64>,
    pub ridge_y: f64,
    /// Footprint vertices of polygon buildings (`Building::p0`).
    pub pts: Vec<[f64; 2]>,
    /// San Francisco only: street centrelines and their names.
    pub streets: Vec<Street>,
    pub street_names: Vec<String>,
    /// San Francisco only: per `AXIS_CELL` cell (`nax x nay` from (x0, y0)), blurred street length
    /// weighted by (cos 4θ, sin 4θ, 1) of the street direction θ.
    nax: usize,
    nay: usize,
    axis: Vec<[f32; 3]>,
}

/// Values on the `CELL` grid over a world's rectangle: cell (i, j) covers [x0 + i CELL, x0 + (i + 1) CELL) by
/// [y0 + j CELL, y0 + (j + 1) CELL), index `j*nx + i`. Out of bounds reads as a wall.
#[derive(Clone, Default)]
pub struct CellMap {
    pub x0: f64,
    pub y0: f64,
    pub nx: usize,
    pub ny: usize,
    pub v: Vec<f32>,
}

impl CellMap {
    fn new(x0: f64, y0: f64, nx: usize, ny: usize, fill: f32) -> CellMap {
        CellMap { x0, y0, nx, ny, v: vec![fill; nx * ny] }
    }

    /// Cell (i, j); `WALL` outside the map.
    #[inline]
    pub fn get(&self, i: i64, j: i64) -> f64 {
        if i < 0 || j < 0 || i >= self.nx as i64 || j >= self.ny as i64 {
            WALL as f64
        } else {
            self.v[j as usize * self.nx + i as usize] as f64
        }
    }

    /// The cell holding (x, y), clamped to the map.
    #[inline]
    pub fn cell(&self, x: f64, y: f64) -> (usize, usize) {
        let i = (((x - self.x0) / CELL).floor().max(0.0) as usize).min(self.nx - 1);
        let j = (((y - self.y0) / CELL).floor().max(0.0) as usize).min(self.ny - 1);
        (i, j)
    }
}

pub fn street_x(k: usize) -> f64 {
    -CITY_HALF + STREET_PITCH * k as f64
}

/// Little-endian reader for `sf_world.bin`.
struct Rd<'a> {
    b: &'a [u8],
    o: usize,
}

impl Rd<'_> {
    fn take(&mut self, n: usize) -> &[u8] {
        let s = &self.b[self.o..self.o + n];
        self.o += n;
        s
    }
    fn u8(&mut self) -> u8 {
        self.take(1)[0]
    }
    fn u16(&mut self) -> u16 {
        u16::from_le_bytes(self.take(2).try_into().unwrap())
    }
    fn u32(&mut self) -> u32 {
        u32::from_le_bytes(self.take(4).try_into().unwrap())
    }
    fn f32(&mut self) -> f32 {
        f32::from_le_bytes(self.take(4).try_into().unwrap())
    }
    fn f64(&mut self) -> f64 {
        f64::from_le_bytes(self.take(8).try_into().unwrap())
    }
    fn xy(&mut self) -> [f64; 2] {
        [self.f32() as f64, self.f32() as f64]
    }
}

/// Convex hull, counter-clockwise, without collinear points (monotone chain).
pub fn convex_hull(pts: &[[f64; 2]]) -> Vec<[f64; 2]> {
    let mut p = pts.to_vec();
    p.sort_by(|a, b| a.partial_cmp(b).unwrap());
    p.dedup();
    if p.len() < 3 {
        return p;
    }
    let cross = |o: [f64; 2], a: [f64; 2], b: [f64; 2]| (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    let mut h: Vec<[f64; 2]> = Vec::with_capacity(2 * p.len());
    for pass in 0..2 {
        let start = h.len();
        let it: Box<dyn Iterator<Item = &[f64; 2]>> = if pass == 0 { Box::new(p.iter()) } else { Box::new(p.iter().rev()) };
        for &q in it {
            while h.len() >= start + 2 && cross(h[h.len() - 2], h[h.len() - 1], q) <= 0.0 {
                h.pop();
            }
            h.push(q);
        }
        h.pop();
    }
    h
}

impl World {
    pub fn load(map: MapId) -> World {
        match map {
            MapId::Grid => World::new(1337),
            MapId::SanFrancisco => World::san_francisco(),
        }
    }

    /// An empty world over the rectangle [x0, x1] x [y0, y1]; its sides must be whole multiples of `TSP`.
    fn empty(map: MapId, seed: u64, [x0, y0, x1, y1]: [f64; 4]) -> World {
        let steps = |a: f64, b: f64, d: f64| {
            let n = (b - a) / d;
            assert!((n - n.round()).abs() < 1e-9 && n >= 1.0, "map side {} m is not a multiple of {d} m", b - a);
            n.round() as usize
        };
        let (tnx, tny) = (steps(x0, x1, TSP) + 1, steps(y0, y1, TSP) + 1);
        let (ncx, ncy) = (steps(x0, x1, CELL), steps(y0, y1, CELL));
        let (nbx, nby) = (((x1 - x0) / BUCKET).ceil() as usize, ((y1 - y0) / BUCKET).ceil() as usize);
        World {
            map,
            seed,
            x0,
            y0,
            x1,
            y1,
            tnx,
            tny,
            terr: vec![0.0; tnx * tny],
            boxes: Vec::new(),
            raw: CellMap::new(x0, y0, ncx, ncy, 0.0),
            raw_terr: CellMap::default(),
            raw_top: 0.0,
            hc: CellMap::new(x0, y0, ncx, ncy, 0.0),
            hc_acc: CellMap::default(),
            robust: OnceLock::new(),
            nbx,
            nby,
            buckets: vec![Vec::new(); nbx * nby],
            bucket_top: vec![f32::MIN; nbx * nby],
            tallest: 0,
            parks: Vec::new(),
            street_w: Vec::new(),
            ridge_y: -2050.0,
            pts: Vec::new(),
            streets: Vec::new(),
            street_names: Vec::new(),
            nax: ((x1 - x0) / AXIS_CELL).ceil() as usize,
            nay: ((y1 - y0) / AXIS_CELL).ceil() as usize,
            axis: Vec::new(),
        }
    }

    /// Is (x, y) on the map (inside its rectangle)?
    #[inline]
    pub fn inside(&self, x: f64, y: f64) -> bool {
        x >= self.x0 && x <= self.x1 && y >= self.y0 && y <= self.y1
    }

    /// The rectangle's centre.
    pub fn center(&self) -> [f64; 2] {
        [0.5 * (self.x0 + self.x1), 0.5 * (self.y0 + self.y1)]
    }

    fn finish(&mut self) {
        self.rasterize();
        self.raw_top = self.raw.v.iter().fold(f64::MIN, |m, &h| m.max(h as f64));
        self.hc = dilate(&self.raw_terr, LAT_CELLS, VERT_MARGIN as f32);
        self.hc_acc = dilate(&self.raw_terr, LAT_CELLS + 1, VERT_MARGIN as f32);
        self.build_buckets();
    }

    /// The procedural grid city.
    pub fn new(seed: u64) -> World {
        let mut w = World::empty(MapId::Grid, seed, [-GRID_HALF, -GRID_HALF, GRID_HALF, GRID_HALF]);
        w.gen_terrain();
        w.gen_city();
        w.finish();
        w
    }

    /// San Francisco from `data/sf/sf_world.bin` (see `data/sf/build.py`).
    pub fn san_francisco() -> World {
        let mut r = Rd { b: SF_BIN, o: 0 };
        assert_eq!(r.take(4), b"SFW1", "sf_world.bin: bad magic");
        assert_eq!(r.u32(), 2, "sf_world.bin: unknown version");
        let (_lon, _lat, _e0, _n0) = (r.f64(), r.f64(), r.f64(), r.f64());
        let bounds = [r.f64(), r.f64(), r.f64(), r.f64()];
        let mut w = World::empty(MapId::SanFrancisco, 0, bounds);
        assert_eq!((r.u32() as usize, r.u32() as usize, r.f32() as f64), (w.tnx, w.tny, TSP), "sf_world.bin: terrain grid");
        for h in w.terr.iter_mut() {
            *h = r.f32().max(SF_WATER as f32);
        }
        let n = r.u32() as usize;
        w.boxes.reserve(n);
        for _ in 0..n {
            let (z0, z1, kind, nv, _pad, group) = (r.f32() as f64, r.f32() as f64, r.u8(), r.u8(), r.u16(), r.u32());
            let raw: Vec<[f64; 2]> = (0..nv).map(|_| r.xy()).collect();
            // f32 rounding can bend a nearly straight edge inward: re-hull
            // (it can only grow the footprint). A needle that rounding
            // flattened to a line becomes a 10 cm wide rectangle around it.
            let mut poly = convex_hull(&raw);
            if poly.len() < 3 {
                let (p, q) = (poly[0], *poly.last().unwrap());
                let (dx, dy) = (q[0] - p[0], q[1] - p[1]);
                let l = (dx * dx + dy * dy).sqrt().max(1e-9);
                let (nx, ny) = (-dy / l * 0.05, dx / l * 0.05);
                let (ex, ey) = (dx / l * 0.05, dy / l * 0.05);
                poly = convex_hull(&[
                    [p[0] - ex + nx, p[1] - ey + ny],
                    [p[0] - ex - nx, p[1] - ey - ny],
                    [q[0] + ex + nx, q[1] + ey + ny],
                    [q[0] + ex - nx, q[1] + ey - ny],
                ]);
            }
            assert!((3..=MAX_POLY).contains(&poly.len()), "sf_world.bin: footprint with {} vertices", poly.len());
            let (mut x0, mut x1, mut y0, mut y1) = (f64::INFINITY, f64::NEG_INFINITY, f64::INFINITY, f64::NEG_INFINITY);
            for q in &poly {
                (x0, x1, y0, y1) = (x0.min(q[0]), x1.max(q[0]), y0.min(q[1]), y1.max(q[1]));
            }
            let zb = w.terrain_min_under(&poly).min(z0) - 1.5;
            let kind = match kind {
                2 => Kind::Bridge,
                3 => Kind::Viaduct,
                _ => Kind::Building,
            };
            let mut hr = Rng(group as u64 ^ 0x5F0C);
            let tint = hr.f() as f32;
            w.boxes.push(Building {
                x0,
                x1,
                y0,
                y1,
                z0: zb,
                z1: z1.max(zb + 2.0),
                tint,
                lot: group,
                p0: w.pts.len() as u32,
                pn: poly.len() as u32,
                kind,
            });
            w.pts.extend_from_slice(&poly);
        }
        let nn = r.u32() as usize;
        for _ in 0..nn {
            let len = r.u16() as usize;
            w.street_names.push(String::from_utf8_lossy(r.take(len)).into_owned());
        }
        let ns = r.u32() as usize;
        for _ in 0..ns {
            let (class, flags, name, np) = (r.u8(), r.u8(), r.u16(), r.u32() as usize);
            let pts = (0..np).map(|_| r.xy()).collect();
            w.streets.push(Street { class, bridge: flags & 1 != 0, name, pts });
        }
        assert_eq!(r.o, SF_BIN.len(), "sf_world.bin: trailing bytes");
        w.add_golden_gate();
        // OSM maps the Bay Bridge towers and anchorage as buildings: mark the
        // ones standing inside the bridge curtain (rendering only).
        let bridge: Vec<usize> = (0..w.boxes.len()).filter(|&k| w.boxes[k].kind == Kind::Bridge).collect();
        for k in 0..w.boxes.len() {
            let b = w.boxes[k];
            if b.kind != Kind::Building {
                continue;
            }
            let c = [0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1)];
            if bridge.iter().any(|&q| pt_poly_dist2(c, w.footprint(&w.boxes[q])) < 25.0) {
                w.boxes[k].kind = Kind::BridgeTower;
            }
        }
        // Tallest from its base (Salesforce Tower), not highest on the map (Sutro Tower, on a 254 m hill).
        let height = |k: usize| w.boxes[k].z1 - w.boxes[k].z0;
        w.tallest = (0..w.boxes.len())
            .filter(|&k| w.boxes[k].kind == Kind::Building)
            .max_by(|&a, &b| height(a).partial_cmp(&height(b)).unwrap())
            .unwrap_or(0);
        w.build_axis();
        w.finish();
        w
    }

    /// A convex prism over `poly` (any order), `z0..z1`.
    fn push_prism(&mut self, poly: &[[f64; 2]], z0: f64, z1: f64, kind: Kind, lot: u32) {
        let poly = convex_hull(poly);
        let (mut x0, mut x1, mut y0, mut y1) = (f64::INFINITY, f64::NEG_INFINITY, f64::INFINITY, f64::NEG_INFINITY);
        for q in &poly {
            (x0, x1, y0, y1) = (x0.min(q[0]), x1.max(q[0]), y0.min(q[1]), y1.max(q[1]));
        }
        let (p0, pn) = (self.pts.len() as u32, poly.len() as u32);
        self.boxes.push(Building { x0, x1, y0, y1, z0, z1, tint: 0.5, lot, p0, pn, kind });
        self.pts.extend_from_slice(&poly);
    }

    /// The Golden Gate Bridge's obstacles (`golden_gate`): the towers and their piers; the deck in 10 m
    /// slices up to its railings; in each cable plane a thin wall from the roadway up past the main cable,
    /// which holds the cable and its suspenders; the anchorage pylons; the Fort Point arch filled down to the
    /// ground; the approach piers. Everything the renderer draws of the bridge lies inside these, and the
    /// space under the deck between the towers stays open.
    fn add_golden_gate(&mut self) {
        use crate::golden_gate as gg;
        let lot = self.boxes.iter().map(|b| b.lot).max().map_or(0, |l| l + 1);
        let rect = |s0: f64, s1: f64, a0: f64, a1: f64| [gg::at(s0, a0), gg::at(s1, a0), gg::at(s1, a1), gg::at(s0, a1)];
        let water = SF_WATER;
        let mut parts: Vec<([[f64; 2]; 4], f64, f64)> = Vec::new();
        for c in [0.0, gg::MAIN] {
            let (pa, pc, top) = gg::PIER;
            parts.push((rect(c - pa, c + pa, -pc, pc), water - 2.0, water + top));
            for p in gg::TOWER {
                parts.push((rect(c + p[2] - p[3], c + p[2] + p[3], p[0] - p[1], p[0] + p[1]), water + p[4], water + p[5]));
            }
        }
        let mut s = gg::DECK.0;
        while s < gg::DECK.1 - 1e-6 {
            let s1 = (s + 10.0).min(gg::DECK.1);
            let ((hw0, d0), (hw1, d1)) = (gg::deck_section(s), gg::deck_section(s1));
            let (hw, depth) = (hw0.max(hw1), d0.max(d1));
            let (t0, t1) = (gg::deck(s), gg::deck(s1));
            parts.push((rect(s, s1, -hw, hw), t0.min(t1) - depth, t0.max(t1) + gg::RAIL));
            s = s1;
        }
        let st = gg::cable_stations();
        for side in [-1.0, 1.0] {
            let a = side * gg::CABLE;
            for w in st.windows(2) {
                let top = gg::cable(w[0]).max(gg::cable(w[1])) + gg::CABLE_R;
                parts.push((rect(w[0], w[1], a - gg::CABLE_R, a + gg::CABLE_R), gg::deck(w[0]).min(gg::deck(w[1])), top));
            }
        }
        let mut ground = Vec::new();
        for (sc, ha, hc) in gg::PYLONS {
            ground.push((rect(sc - ha, sc + ha, -hc, hc), gg::deck(sc) - 10.0, gg::deck(sc) + 10.0));
        }
        let (sa, sb, ar) = gg::ARCH;
        let hw = ar + gg::ARCH_R;
        ground.push((rect(sa, sb, -hw, hw), f64::INFINITY, gg::deck(sa).max(gg::deck(sb)) - 4.0 + gg::ARCH_R));
        let ((first, step, last), (pa, pc)) = (gg::APPROACH_PIERS, gg::APPROACH_PIER);
        let mut s = first;
        while s < last {
            ground.push((rect(s - pa, s + pa, -pc, pc), gg::deck(s) - 4.0, gg::deck(s) - 4.0));
            s += step;
        }
        // Standing on the ground: from 2 m below the lowest terrain under them (or `cap`, if lower).
        for (poly, cap, top) in ground {
            parts.push((poly, self.terrain_min_under(&poly).min(cap) - 2.0, top));
        }
        for (poly, z0, z1) in parts {
            self.push_prism(&poly, z0, z1, Kind::GoldenGate, lot);
        }
    }

    /// Lowest terrain under a footprint: at its vertices, edge midpoints and
    /// the grid nodes inside.
    fn terrain_min_under(&self, poly: &[[f64; 2]]) -> f64 {
        let n = poly.len();
        let mut m = f64::INFINITY;
        for i in 0..n {
            let (a, b) = (poly[i], poly[(i + 1) % n]);
            m = m.min(self.terrain(a[0], a[1])).min(self.terrain(0.5 * (a[0] + b[0]), 0.5 * (a[1] + b[1])));
        }
        let (mut x0, mut x1, mut y0, mut y1) = (f64::INFINITY, f64::NEG_INFINITY, f64::INFINITY, f64::NEG_INFINITY);
        for q in poly {
            (x0, x1, y0, y1) = (x0.min(q[0]), x1.max(q[0]), y0.min(q[1]), y1.max(q[1]));
        }
        let gx = |v: f64| ((v - self.x0) / TSP).clamp(0.0, (self.tnx - 1) as f64);
        let gy = |v: f64| ((v - self.y0) / TSP).clamp(0.0, (self.tny - 1) as f64);
        for j in gy(y0).ceil() as usize..=gy(y1).floor() as usize {
            for i in gx(x0).ceil() as usize..=gx(x1).floor() as usize {
                let (x, y) = (self.x0 + i as f64 * TSP, self.y0 + j as f64 * TSP);
                if pt_poly_dist2([x, y], poly) == 0.0 {
                    m = m.min(self.terr[j * self.tnx + i] as f64);
                }
            }
        }
        m
    }

    /// Footprint polygon of a polygon building (empty for a box).
    #[inline]
    pub fn footprint(&self, b: &Building) -> &[[f64; 2]] {
        &self.pts[b.p0 as usize..(b.p0 + b.pn) as usize]
    }

    /// Footprint corners, counter-clockwise, for boxes and polygons alike.
    pub fn outline(&self, b: &Building) -> Vec<[f64; 2]> {
        if b.pn == 0 {
            vec![[b.x0, b.y0], [b.x1, b.y0], [b.x1, b.y1], [b.x0, b.y1]]
        } else {
            self.footprint(b).to_vec()
        }
    }

    /// Exact squared distance from `p` to building `b`.
    #[inline]
    pub fn bld_dist2(&self, b: &Building, p: [f64; 3]) -> f64 {
        if b.pn == 0 {
            let dx = (b.x0 - p[0]).max(0.0).max(p[0] - b.x1);
            let dy = (b.y0 - p[1]).max(0.0).max(p[1] - b.y1);
            let dz = (b.z0 - p[2]).max(0.0).max(p[2] - b.z1);
            dx * dx + dy * dy + dz * dz
        } else {
            pt_prism_dist2(p, self.footprint(b), b.z0, b.z1)
        }
    }

    /// Exact squared distance from the segment `a`-`b` to building `bx`, or
    /// anything >= `stop` if it is at least that far.
    #[inline]
    pub fn seg_bld_dist2(&self, bx: &Building, a: [f64; 3], b: [f64; 3], stop: f64) -> f64 {
        let box_d2 = seg_aabb_dist2(a, b, [bx.x0, bx.y0, bx.z0], [bx.x1, bx.y1, bx.z1]);
        if bx.pn == 0 || box_d2 >= stop {
            box_d2
        } else {
            seg_prism_dist2(a, b, self.footprint(bx), bx.z0, bx.z1)
        }
    }

    /// Street-axis field from the street centrelines (San Francisco).
    fn build_axis(&mut self) {
        let (nax, nay) = (self.nax, self.nay);
        let mut acc = vec![[0f32; 3]; nax * nay];
        for st in self.streets.iter().filter(|s| s.is_surface()) {
            for w in st.pts.windows(2) {
                let (dx, dy) = (w[1][0] - w[0][0], w[1][1] - w[0][1]);
                let len = (dx * dx + dy * dy).sqrt();
                if len < 5.0 {
                    continue;
                }
                let th = 4.0 * dy.atan2(dx);
                let k = (len / 25.0).ceil() as usize;
                for s in 0..k {
                    let f = (s as f64 + 0.5) / k as f64;
                    let (x, y) = (w[0][0] + f * dx, w[0][1] + f * dy);
                    let (i, j) = (((x - self.x0) / AXIS_CELL).floor(), ((y - self.y0) / AXIS_CELL).floor());
                    if i < 0.0 || j < 0.0 || i >= nax as f64 || j >= nay as f64 {
                        continue;
                    }
                    let c = &mut acc[j as usize * nax + i as usize];
                    let l = (len / k as f64) as f32;
                    c[0] += l * th.cos() as f32;
                    c[1] += l * th.sin() as f32;
                    c[2] += l;
                }
            }
        }
        // Separable box blur.
        let r = AXIS_BLUR as i64;
        let (nx, ny) = (nax as i64, nay as i64);
        let mut tmp = vec![[0f32; 3]; nax * nay];
        for j in 0..ny {
            for i in 0..nx {
                let mut s = [0f32; 3];
                for d in -r..=r {
                    let ii = i + d;
                    if (0..nx).contains(&ii) {
                        let c = acc[(j * nx + ii) as usize];
                        (s[0], s[1], s[2]) = (s[0] + c[0], s[1] + c[1], s[2] + c[2]);
                    }
                }
                tmp[(j * nx + i) as usize] = s;
            }
        }
        self.axis = vec![[0f32; 3]; nax * nay];
        for j in 0..ny {
            for i in 0..nx {
                let mut s = [0f32; 3];
                for d in -r..=r {
                    let jj = j + d;
                    if (0..ny).contains(&jj) {
                        let c = tmp[(jj * nx + i) as usize];
                        (s[0], s[1], s[2]) = (s[0] + c[0], s[1] + c[1], s[2] + c[2]);
                    }
                }
                self.axis[(j * nx + i) as usize] = s;
            }
        }
    }

    /// Street grid direction at (x, y), modulo 90 deg, if the streets around
    /// agree on one: the grid city is axis-aligned everywhere; in San
    /// Francisco it comes from the street centrelines (none where grids meet,
    /// as along Market Street, or away from streets). Continuous in position.
    pub fn street_axis(&self, x: f64, y: f64) -> Option<f64> {
        if self.map == MapId::Grid {
            return Some(0.0);
        }
        let fx = (x - self.x0) / AXIS_CELL - 0.5;
        let fy = (y - self.y0) / AXIS_CELL - 0.5;
        let (ix, iy) = (fx.floor(), fy.floor());
        let (tx, ty) = ((fx - ix) as f32, (fy - iy) as f32);
        let get = |i: f64, j: f64| -> [f32; 3] {
            if i < 0.0 || j < 0.0 || i >= self.nax as f64 || j >= self.nay as f64 {
                [0.0; 3]
            } else {
                self.axis[j as usize * self.nax + i as usize]
            }
        };
        let (a, b, c, d) = (get(ix, iy), get(ix + 1.0, iy), get(ix, iy + 1.0), get(ix + 1.0, iy + 1.0));
        let mut s = [0f32; 3];
        for k in 0..3 {
            s[k] = (a[k] * (1.0 - tx) + b[k] * tx) * (1.0 - ty) + (c[k] * (1.0 - tx) + d[k] * tx) * ty;
        }
        if s[2] < AXIS_MIN_LEN || (s[0] * s[0] + s[1] * s[1]).sqrt() < AXIS_MIN_COHERENCE * s[2] {
            return None;
        }
        Some((s[1] as f64).atan2(s[0] as f64) / 4.0)
    }

    /// The longest straight run of the named street (San Francisco): the
    /// street segment whose line collects the most street length within
    /// `STRAIGHT_TOL` m and `STRAIGHT_ANGLE` of it, refitted to those
    /// segments. Streets bend (Mission Street turns south at 13th), so a
    /// plain fit over all of it would miss the street.
    pub fn street_line(&self, name: &str) -> Option<StreetLine> {
        const STRAIGHT_TOL: f64 = 4.0;
        const STRAIGHT_ANGLE: f64 = 0.05;
        let k = self.street_names.iter().position(|n| n == name)? as u16;
        let segs: Vec<([f64; 2], [f64; 2])> = self
            .streets
            .iter()
            .filter(|s| s.name == k && s.is_surface())
            .flat_map(|s| s.pts.windows(2).map(|w| (w[0], w[1])))
            .filter(|(a, b)| {
                let inside = |p: &[f64; 2]| p[0] > self.x0 + 50.0 && p[0] < self.x1 - 50.0 && p[1] > self.y0 + 50.0 && p[1] < self.y1 - 50.0;
                inside(a) && inside(b) && ((b[0] - a[0]).powi(2) + (b[1] - a[1]).powi(2)).sqrt() > 1.0
            })
            .collect();
        let on_line = |(a, b): &([f64; 2], [f64; 2]), o: [f64; 2], th: f64| -> bool {
            let (c, s) = (th.cos(), th.sin());
            let off = |p: &[f64; 2]| ((p[1] - o[1]) * c - (p[0] - o[0]) * s).abs();
            let ang = (b[1] - a[1]).atan2(b[0] - a[0]) - th;
            let ang = (ang + std::f64::consts::FRAC_PI_2).rem_euclid(std::f64::consts::PI) - std::f64::consts::FRAC_PI_2;
            off(a) <= STRAIGHT_TOL && off(b) <= STRAIGHT_TOL && ang.abs() <= STRAIGHT_ANGLE
        };
        let len = |(a, b): &([f64; 2], [f64; 2])| ((b[0] - a[0]).powi(2) + (b[1] - a[1]).powi(2)).sqrt();
        let mut best: Option<(f64, [f64; 2], f64)> = None;
        for sg in &segs {
            let th = (sg.1[1] - sg.0[1]).atan2(sg.1[0] - sg.0[0]);
            let total: f64 = segs.iter().filter(|q| on_line(q, sg.0, th)).map(len).sum();
            if best.map_or(true, |b| total > b.0) {
                best = Some((total, sg.0, th));
            }
        }
        let (_, o, th) = best?;
        let pts: Vec<[f64; 2]> = segs.iter().filter(|q| on_line(q, o, th)).flat_map(|q| [q.0, q.1]).collect();
        let m = pts.len() as f64;
        let (cx, cy) = (pts.iter().map(|p| p[0]).sum::<f64>() / m, pts.iter().map(|p| p[1]).sum::<f64>() / m);
        let (mut sxx, mut sxy, mut syy) = (0.0, 0.0, 0.0);
        for p in &pts {
            let (dx, dy) = (p[0] - cx, p[1] - cy);
            sxx += dx * dx;
            sxy += dx * dy;
            syy += dy * dy;
        }
        let dir = 0.5 * (2.0 * sxy).atan2(sxx - syy);
        let (c, s) = (dir.cos(), dir.sin());
        let (mut lo, mut hi, mut e2) = (f64::INFINITY, f64::NEG_INFINITY, 0.0);
        for p in &pts {
            let (dx, dy) = (p[0] - cx, p[1] - cy);
            let along = dx * c + dy * s;
            (lo, hi) = (lo.min(along), hi.max(along));
            e2 += (dy * c - dx * s).powi(2);
        }
        Some(StreetLine { p0: [cx + lo * c, cy + lo * s], dir, len: hi - lo, rms: (e2 / m).sqrt() })
    }

    /// Highest terrain node within `r` metres of `c`.
    pub fn hilltop_near(&self, c: [f64; 2], r: f64) -> [f64; 3] {
        let mut best = [c[0], c[1], f64::NEG_INFINITY];
        for j in 0..self.tny {
            for i in 0..self.tnx {
                let (x, y) = (self.x0 + i as f64 * TSP, self.y0 + j as f64 * TSP);
                let h = self.terr[j * self.tnx + i] as f64;
                if (x - c[0]).powi(2) + (y - c[1]).powi(2) <= r * r && h > best[2] {
                    best = [x, y, h];
                }
            }
        }
        best
    }

    /// Highest terrain point at least `border` metres inside the map.
    pub fn highest_point(&self, border: f64) -> [f64; 3] {
        let mut best = [0.0, 0.0, f64::NEG_INFINITY];
        for j in 0..self.tny {
            for i in 0..self.tnx {
                let (x, y) = (self.x0 + i as f64 * TSP, self.y0 + j as f64 * TSP);
                let h = self.terr[j * self.tnx + i] as f64;
                let inner = x >= self.x0 + border && x <= self.x1 - border && y >= self.y0 + border && y <= self.y1 - border;
                if inner && h > best[2] {
                    best = [x, y, h];
                }
            }
        }
        best
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
        for j in 0..self.tny {
            for i in 0..self.tnx {
                let x = self.x0 + i as f64 * TSP;
                let y = self.y0 + j as f64 * TSP;
                self.terr[j * self.tnx + i] = self.terrain_fn(x, y) as f32;
            }
        }
    }

    /// True terrain height: barycentric on the render triangulation.
    #[inline]
    pub fn terrain(&self, x: f64, y: f64) -> f64 {
        let fx = ((x - self.x0) / TSP).clamp(0.0, (self.tnx - 1) as f64 - 1e-9);
        let fy = ((y - self.y0) / TSP).clamp(0.0, (self.tny - 1) as f64 - 1e-9);
        let i = fx as usize;
        let j = fy as usize;
        let u = fx - i as f64;
        let v = fy - j as f64;
        let n = self.tnx;
        let h00 = self.terr[j * n + i] as f64;
        let h10 = self.terr[j * n + i + 1] as f64;
        let h01 = self.terr[(j + 1) * n + i] as f64;
        let h11 = self.terr[(j + 1) * n + i + 1] as f64;
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
        self.boxes.push(Building::aabb(x0, x1, y0, y1, zmin - 1.5, zc + h, tint, lot));
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
        // Terrain: cells evenly subdivide the 20 m quads, so the triangulation
        // diagonal only meets cell corners; the max over a cell is the max of
        // its four corners.
        let (nx, ny) = (self.raw.nx, self.raw.ny);
        let np = nx + 1;
        let mut corner = vec![0f32; np * (ny + 1)];
        for j in 0..=ny {
            for i in 0..np {
                corner[j * np + i] = self.terrain(self.x0 + i as f64 * CELL, self.y0 + j as f64 * CELL) as f32;
            }
        }
        for j in 0..ny {
            for i in 0..nx {
                let a = corner[j * np + i]
                    .max(corner[j * np + i + 1])
                    .max(corner[(j + 1) * np + i])
                    .max(corner[(j + 1) * np + i + 1]);
                self.raw.v[j * nx + i] = a;
            }
        }
        self.raw_terr = self.raw.clone();
        for b in &self.boxes {
            let (_, ja) = self.raw.cell(b.x0, b.y0);
            let (_, jb) = self.raw.cell(b.x1, b.y1);
            for j in ja..=jb {
                // Polygon: only the cells its slice of this row touches.
                let (xa, xb) = if b.pn == 0 {
                    (b.x0, b.x1)
                } else {
                    let poly = &self.pts[b.p0 as usize..(b.p0 + b.pn) as usize];
                    let ya = self.y0 + j as f64 * CELL;
                    match strip_x_range(poly, ya, ya + CELL) {
                        Some(r) => r,
                        None => continue,
                    }
                };
                let (ia, _) = self.raw.cell(xa, b.y0);
                let (ib, _) = self.raw.cell(xb, b.y0);
                for i in ia..=ib {
                    let c = &mut self.raw.v[j * nx + i];
                    *c = c.max(b.z1 as f32);
                }
            }
        }
    }

    fn build_buckets(&mut self) {
        let nb = self.nbx;
        for (n, b) in self.boxes.iter().enumerate() {
            let (i0, j0) = self.bucket(b.x0, b.y0);
            let (i1, j1) = self.bucket(b.x1, b.y1);
            for j in j0..=j1 {
                for i in i0..=i1 {
                    self.buckets[j * nb + i].push(n as u32);
                    self.bucket_top[j * nb + i] = self.bucket_top[j * nb + i].max(b.z1 as f32);
                }
            }
        }
    }

    /// The building bucket holding (x, y), clamped to the map.
    #[inline]
    fn bucket(&self, x: f64, y: f64) -> (usize, usize) {
        let i = (((x - self.x0) / BUCKET).floor().max(0.0) as usize).min(self.nbx - 1);
        let j = (((y - self.y0) / BUCKET).floor().max(0.0) as usize).min(self.nby - 1);
        (i, j)
    }

    /// Robust maps (lazily built): one per entry of `ROBUST_CELLS`;
    /// `[0]` for re-checks, `[1]` (one cell wider) for acceptance.
    pub fn robust_maps(&self, accept: bool) -> &Vec<CellMap> {
        let m = self.robust.get_or_init(|| {
            let mk = |extra: usize| ROBUST_CELLS.iter().map(|&r| dilate(&self.raw_terr, r + extra, VERT_MARGIN as f32)).collect();
            [mk(0), mk(1)]
        });
        &m[accept as usize]
    }

    /// Exact distance from the segment `a`-`b` to the nearest building,
    /// or infinity if none is within `q`.
    #[inline]
    pub fn seg_building_dist(&self, a: [f64; 3], b: [f64; 3], q: f64) -> f64 {
        let (x0, x1) = (a[0].min(b[0]) - q, a[0].max(b[0]) + q);
        let (y0, y1) = (a[1].min(b[1]) - q, a[1].max(b[1]) + q);
        let (z0, z1) = (a[2].min(b[2]) - q, a[2].max(b[2]) + q);
        let (ia, ja) = self.bucket(x0, y0);
        let (ib, jb) = self.bucket(x1, y1);
        let nb = self.nbx;
        let mut d2 = q * q;
        let mut hit = false;
        for j in ja..=jb {
            for i in ia..=ib {
                if (self.bucket_top[j * nb + i] as f64) < z0 {
                    continue;
                }
                for &n in &self.buckets[j * nb + i] {
                    let bx = &self.boxes[n as usize];
                    if bx.x1 < x0 || bx.x0 > x1 || bx.y1 < y0 || bx.y0 > y1 || bx.z1 < z0 || bx.z0 > z1 {
                        continue;
                    }
                    let e = self.seg_bld_dist2(bx, a, b, d2);
                    if e < d2 {
                        d2 = e;
                        hit = true;
                    }
                }
            }
        }
        if hit {
            d2.sqrt()
        } else {
            f64::INFINITY
        }
    }

    /// Distance from `p` to the nearest building surface, capped at `cap`.
    /// Visits buckets in rings outward from `p` and stops once a ring is
    /// farther than the best distance so far (a building's nearest point lies
    /// in a bucket it is registered in, so nothing skipped can be closer).
    pub fn building_dist(&self, p: [f64; 3], cap: f64) -> f64 {
        let ((ilo, jlo), (ihi, jhi)) = (self.bucket(p[0] - cap, p[1] - cap), self.bucket(p[0] + cap, p[1] + cap));
        let (ci, cj) = self.bucket(p[0], p[1]);
        let nb = self.nbx;
        let rmax = (ci - ilo).max(ihi - ci).max(cj - jlo).max(jhi - cj);
        let mut d = cap;
        for r in 0..=rmax {
            if r >= 1 && (r - 1) as f64 * BUCKET >= d {
                break;
            }
            for j in jlo.max(cj.saturating_sub(r))..=jhi.min(cj + r) {
                let edge_row = j + r == cj || j == cj + r;
                for i in ilo.max(ci.saturating_sub(r))..=ihi.min(ci + r) {
                    if !edge_row && i + r != ci && i != ci + r {
                        continue;
                    }
                    if p[2] - self.bucket_top[j * nb + i] as f64 >= d {
                        continue;
                    }
                    for &n in &self.buckets[j * nb + i] {
                        d = d.min(self.bld_dist2(&self.boxes[n as usize], p).sqrt());
                    }
                }
            }
        }
        d
    }

    /// True clearance of the aircraft body (negative = collision).
    pub fn true_clearance(&self, p: [f64; 3]) -> f64 {
        if !self.inside(p[0], p[1]) {
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

    /// Clearance of the `R_BODY` sphere and the wing capsule (`wing_tips`, `WING_R`); values above `cap` may read as `cap`.
    pub fn airframe_clearance(&self, s: &State, cap: f64) -> f64 {
        let p = [s[X], s[Y], s[Z]];
        if !self.inside(p[0], p[1]) {
            return -1.0;
        }
        let mut c = p[2] - R_BODY - self.terrain(p[0], p[1]);
        for k in 0..8 {
            let a = k as f64 * std::f64::consts::FRAC_PI_4;
            let t = self.terrain(p[0] + R_BODY * a.cos(), p[1] + R_BODY * a.sin());
            c = c.min(p[2] - t);
        }
        c = c.min(self.building_dist(p, cap + R_BODY) - R_BODY);
        let [a, b] = wing_tips(s);
        let q = c.max(0.0).min(cap) + WING_R;
        c = c.min(self.seg_building_dist(a, b, q) - WING_R);
        let m: [f64; 3] = std::array::from_fn(|i| 0.5 * (a[i] + b[i]));
        for tip in [a, b] {
            for k in 0..=6 {
                let t = (4.0 + 0.25 * k as f64) / WING_TIP;
                let w: [f64; 3] = std::array::from_fn(|i| m[i] + (tip[i] - m[i]) * t);
                c = c.min(w[2] - WING_R - self.terrain(w[0], w[1]));
            }
        }
        c
    }

    /// Ground or roof height directly below `(x, y)` (raw cell max).
    pub fn surface(&self, x: f64, y: f64) -> f64 {
        let (i, j) = self.raw.cell(x, y);
        self.raw.v[j * self.raw.nx + i] as f64
    }

    pub fn tallest_center(&self) -> [f64; 3] {
        let b = &self.boxes[self.tallest];
        [0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1), b.z1]
    }
}

/// Bilinear lookup in a clearance map; out of bounds is a wall.
#[inline]
pub fn hc_at(map: &CellMap, x: f64, y: f64) -> f64 {
    let fx = (x - map.x0) / CELL - 0.5;
    let fy = (y - map.y0) / CELL - 0.5;
    let ix = fx.floor();
    let iy = fy.floor();
    let tx = fx - ix;
    let ty = fy - iy;
    let (ix, iy) = (ix as i64, iy as i64);
    let a = map.get(ix, iy);
    let b = map.get(ix + 1, iy);
    let c = map.get(ix, iy + 1);
    let d = map.get(ix + 1, iy + 1);
    (a * (1.0 - tx) + b * tx) * (1.0 - ty) + (c * (1.0 - tx) + d * tx) * ty
}

/// Exact squared distance between the segment `a`-`b` and the axis-aligned
/// box [lo, hi]. Between the parameters where the segment crosses a slab
/// boundary, each axis is either inside its slab or clamped to one face, so
/// the squared distance is a quadratic in t; minimise it on each piece.
#[inline]
pub fn seg_aabb_dist2(a: [f64; 3], b: [f64; 3], lo: [f64; 3], hi: [f64; 3]) -> f64 {
    let d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
    let mut ts = [0.0f64; 8];
    ts[1] = 1.0;
    let mut n = 2;
    for ax in 0..3 {
        if d[ax].abs() > 1e-12 {
            for bound in [lo[ax], hi[ax]] {
                let t = (bound - a[ax]) / d[ax];
                if t > 0.0 && t < 1.0 {
                    ts[n] = t;
                    n += 1;
                }
            }
        }
    }
    let ts = &mut ts[..n];
    ts.sort_by(|p, q| p.partial_cmp(q).unwrap());
    let mut best = f64::INFINITY;
    for w in ts.windows(2) {
        let (t0, t1) = (w[0], w[1]);
        let tm = 0.5 * (t0 + t1);
        let (mut qa, mut qb, mut qc) = (0.0, 0.0, 0.0);
        for ax in 0..3 {
            let p = a[ax] + d[ax] * tm;
            let c = if p < lo[ax] {
                lo[ax]
            } else if p > hi[ax] {
                hi[ax]
            } else {
                continue;
            };
            let e = a[ax] - c;
            qa += d[ax] * d[ax];
            qb += 2.0 * e * d[ax];
            qc += e * e;
        }
        let t = if qa > 1e-15 { (-qb / (2.0 * qa)).clamp(t0, t1) } else { t0 };
        best = best.min(qa * t * t + qb * t + qc);
    }
    best.max(0.0)
}

/// Squared distance from `q` to a convex counter-clockwise polygon in the
/// plane (0 inside). Outside, the nearest point lies on an edge.
#[inline]
pub fn pt_poly_dist2(q: [f64; 2], poly: &[[f64; 2]]) -> f64 {
    let n = poly.len();
    let mut inside = true;
    let mut best = f64::INFINITY;
    for i in 0..n {
        let (v, w) = (poly[i], poly[(i + 1) % n]);
        let (ex, ey) = (w[0] - v[0], w[1] - v[1]);
        let (qx, qy) = (q[0] - v[0], q[1] - v[1]);
        if ex * qy - ey * qx < 0.0 {
            inside = false;
        }
        let s = ((qx * ex + qy * ey) / (ex * ex + ey * ey)).clamp(0.0, 1.0);
        let (dx, dy) = (qx - s * ex, qy - s * ey);
        best = best.min(dx * dx + dy * dy);
    }
    if inside {
        0.0
    } else {
        best
    }
}

/// Squared distance from `p` to the prism `poly x [z0, z1]`. The prism is a
/// product of a plane set and an interval, so the squared distance splits
/// into the two parts.
#[inline]
pub fn pt_prism_dist2(p: [f64; 3], poly: &[[f64; 2]], z0: f64, z1: f64) -> f64 {
    let dz = (z0 - p[2]).max(0.0).max(p[2] - z1);
    pt_poly_dist2([p[0], p[1]], poly) + dz * dz
}

/// Exact squared distance between the segment `a`-`b` and the vertical prism
/// `poly x [z0, z1]` (`poly` convex, counter-clockwise, at most `MAX_POLY`
/// vertices).
///
/// As in `pt_prism_dist2`, d^2(t) = d_poly(q(t))^2 + d_z(z(t))^2 along the
/// segment. Outside a convex polygon, the nearest boundary feature is the
/// edge whose perpendicular slab holds the point or the vertex between two
/// slabs, so the feature (or "inside") only changes where the ground track
/// q(t) crosses an edge's line or a line through an edge's endpoint
/// perpendicular to it; the z part only changes where z(t) crosses z0 or z1.
/// Between consecutive crossings both parts are fixed quadratics in t (the
/// squared distance to one line, one point, or zero), so minimise each piece.
pub fn seg_prism_dist2(a: [f64; 3], b: [f64; 3], poly: &[[f64; 2]], z0: f64, z1: f64) -> f64 {
    let n = poly.len();
    debug_assert!((3..=MAX_POLY).contains(&n));
    let d = [b[0] - a[0], b[1] - a[1], b[2] - a[2]];
    let mut ts = [0.0f64; 3 * MAX_POLY + 4];
    ts[1] = 1.0;
    let mut m = 2;
    let mut add = |t: f64, m: &mut usize| {
        if t > 0.0 && t < 1.0 {
            ts[*m] = t;
            *m += 1;
        }
    };
    for i in 0..n {
        let (v, w) = (poly[i], poly[(i + 1) % n]);
        let (ex, ey) = (w[0] - v[0], w[1] - v[1]);
        // Edge line: e x (q - v) = 0.
        let den = ex * d[1] - ey * d[0];
        if den.abs() > 1e-12 {
            add(-(ex * (a[1] - v[1]) - ey * (a[0] - v[0])) / den, &mut m);
        }
        // Perpendiculars at both ends: e . (q - v) = 0 and e . (q - w) = 0.
        let den = ex * d[0] + ey * d[1];
        if den.abs() > 1e-12 {
            add((ex * (v[0] - a[0]) + ey * (v[1] - a[1])) / den, &mut m);
            add((ex * (w[0] - a[0]) + ey * (w[1] - a[1])) / den, &mut m);
        }
    }
    if d[2].abs() > 1e-12 {
        add((z0 - a[2]) / d[2], &mut m);
        add((z1 - a[2]) / d[2], &mut m);
    }
    let ts = &mut ts[..m];
    ts.sort_by(|p, q| p.partial_cmp(q).unwrap());
    let mut best = f64::INFINITY;
    for k in 0..m - 1 {
        let (t0, t1) = (ts[k], ts[k + 1]);
        if t1 <= t0 && k > 0 {
            continue;
        }
        let tm = 0.5 * (t0 + t1);
        let q = [a[0] + d[0] * tm, a[1] + d[1] * tm];
        let (mut qa, mut qb, mut qc) = (0.0, 0.0, 0.0);
        // Nearest polygon feature at the midpoint: inside, an edge, a vertex.
        let mut inside = true;
        let mut near = (f64::INFINITY, 0usize, 0.0f64);
        for i in 0..n {
            let (v, w) = (poly[i], poly[(i + 1) % n]);
            let (ex, ey) = (w[0] - v[0], w[1] - v[1]);
            let (qx, qy) = (q[0] - v[0], q[1] - v[1]);
            if ex * qy - ey * qx < 0.0 {
                inside = false;
            }
            let s = ((qx * ex + qy * ey) / (ex * ex + ey * ey)).clamp(0.0, 1.0);
            let (dx, dy) = (qx - s * ex, qy - s * ey);
            let e2 = dx * dx + dy * dy;
            if e2 < near.0 {
                near = (e2, i, s);
            }
        }
        if !inside {
            let (_, i, s) = near;
            let (v, w) = (poly[i], poly[(i + 1) % n]);
            if s > 0.0 && s < 1.0 {
                // Distance to the edge's line: (e x (q - v)) / |e|, linear in t.
                let (ex, ey) = (w[0] - v[0], w[1] - v[1]);
                let l = (ex * ex + ey * ey).sqrt();
                let c0 = (ex * (a[1] - v[1]) - ey * (a[0] - v[0])) / l;
                let c1 = (ex * d[1] - ey * d[0]) / l;
                qa += c1 * c1;
                qb += 2.0 * c0 * c1;
                qc += c0 * c0;
            } else {
                let c = if s <= 0.0 { v } else { w };
                for ax in 0..2 {
                    let e = a[ax] - c[ax];
                    qa += d[ax] * d[ax];
                    qb += 2.0 * e * d[ax];
                    qc += e * e;
                }
            }
        }
        let zm = a[2] + d[2] * tm;
        let zc = if zm < z0 {
            Some(z0)
        } else if zm > z1 {
            Some(z1)
        } else {
            None
        };
        if let Some(zc) = zc {
            let e = a[2] - zc;
            qa += d[2] * d[2];
            qb += 2.0 * e * d[2];
            qc += e * e;
        }
        let t = if qa > 1e-15 { (-qb / (2.0 * qa)).clamp(t0, t1) } else { t0 };
        best = best.min(qa * t * t + qb * t + qc);
    }
    best.max(0.0)
}

/// x-range of a convex polygon inside the horizontal strip `ya <= y <= yb`,
/// or `None` if they do not meet: the strip cuts out a convex polygon whose
/// corners are the polygon's vertices inside the strip and the edges'
/// crossings of its two lines.
fn strip_x_range(poly: &[[f64; 2]], ya: f64, yb: f64) -> Option<(f64, f64)> {
    let n = poly.len();
    let (mut lo, mut hi) = (f64::INFINITY, f64::NEG_INFINITY);
    for i in 0..n {
        let (v, w) = (poly[i], poly[(i + 1) % n]);
        if v[1] >= ya && v[1] <= yb {
            (lo, hi) = (lo.min(v[0]), hi.max(v[0]));
        }
        for y in [ya, yb] {
            if (v[1] - y) * (w[1] - y) < 0.0 {
                let x = v[0] + (y - v[1]) / (w[1] - v[1]) * (w[0] - v[0]);
                (lo, hi) = (lo.min(x), hi.max(x));
            }
        }
    }
    (lo <= hi).then_some((lo, hi))
}

/// Minimum clearance `z - Hc` over every cell the 3D segment
/// (x0,y0,z0)-(x1,y1,z1) crosses, using the segment's lowest height inside
/// each cell.
#[inline]
pub fn swept_clear(map: &CellMap, x0: f64, y0: f64, z0: f64, x1: f64, y1: f64, z1: f64) -> f64 {
    let (fx0, fy0) = ((x0 - map.x0) / CELL, (y0 - map.y0) / CELL);
    let (fx1, fy1) = ((x1 - map.x0) / CELL, (y1 - map.y0) / CELL);
    let (mut i, mut j) = (fx0.floor() as i64, fy0.floor() as i64);
    let (i1, j1) = (fx1.floor() as i64, fy1.floor() as i64);
    let (dx, dy) = (fx1 - fx0, fy1 - fy0);
    let (si, sj) = (if dx > 0.0 { 1 } else { -1 }, if dy > 0.0 { 1 } else { -1 });
    let mut tmx = if dx != 0.0 { ((if si > 0 { i + 1 } else { i }) as f64 - fx0) / dx } else { f64::INFINITY };
    let mut tmy = if dy != 0.0 { ((if sj > 0 { j + 1 } else { j }) as f64 - fy0) / dy } else { f64::INFINITY };
    let tdx = if dx != 0.0 { 1.0 / dx.abs() } else { f64::INFINITY };
    let tdy = if dy != 0.0 { 1.0 / dy.abs() } else { f64::INFINITY };
    let zt = |t: f64| z0 + (z1 - z0) * t;
    let n = (i1 - i).abs() + (j1 - j).abs();
    let mut t0 = 0.0;
    let mut c = f64::INFINITY;
    for _ in 0..n {
        let step_x = tmx < tmy;
        let tn = if step_x { tmx } else { tmy }.min(1.0);
        c = c.min(zt(t0).min(zt(tn)) - map.get(i, j));
        t0 = tn;
        if step_x {
            i += si;
            tmx += tdx;
        } else {
            j += sj;
            tmy += tdy;
        }
    }
    c.min(zt(t0).min(z1) - map.get(i, j))
}

/// Square (Chebyshev) max filter of radius `r` cells, out-of-map = wall,
/// then add the vertical margin.
pub fn dilate(raw: &CellMap, r: usize, vm: f32) -> CellMap {
    let (nx, ny) = (raw.nx as i64, raw.ny as i64);
    let r = r as i64;
    let mut tmp = vec![0f32; raw.nx * raw.ny];
    for j in 0..ny {
        for i in 0..nx {
            let mut m = f32::MIN;
            for d in -r..=r {
                let ii = i + d;
                let v = if ii < 0 || ii >= nx { WALL } else { raw.v[(j * nx + ii) as usize] };
                m = m.max(v);
            }
            tmp[(j * nx + i) as usize] = m;
        }
    }
    let mut out = CellMap::new(raw.x0, raw.y0, raw.nx, raw.ny, 0.0);
    for j in 0..ny {
        for i in 0..nx {
            let mut m = f32::MIN;
            for d in -r..=r {
                let jj = j + d;
                let v = if jj < 0 || jj >= ny { WALL } else { tmp[(jj * nx + i) as usize] };
                m = m.max(v);
            }
            out.v[(j * nx + i) as usize] = m + vm;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rand_poly(r: &mut Rng) -> Vec<[f64; 2]> {
        let (cx, cy, s) = (r.range(-20.0, 20.0), r.range(-20.0, 20.0), r.range(2.0, 30.0));
        let k = 3 + (r.f() * 12.0) as usize;
        let pts: Vec<[f64; 2]> = (0..k).map(|_| [cx + s * r.range(-1.0, 1.0), cy + s * r.range(-1.0, 1.0)]).collect();
        convex_hull(&pts)
    }

    fn rand_pt(r: &mut Rng) -> [f64; 3] {
        [r.range(-60.0, 60.0), r.range(-60.0, 60.0), r.range(-20.0, 60.0)]
    }

    /// Reference: minimum over dense samples, and its guaranteed error. The
    /// distance is 1-Lipschitz in position, so the true minimum is within
    /// half a sample spacing of the best sample.
    fn sampled(a: [f64; 3], b: [f64; 3], poly: &[[f64; 2]], z0: f64, z1: f64) -> (f64, f64) {
        let k = 4000;
        let mut m = f64::INFINITY;
        for s in 0..=k {
            let t = s as f64 / k as f64;
            let p = [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];
            m = m.min(pt_prism_dist2(p, poly, z0, z1).sqrt());
        }
        let len = ((b[0] - a[0]).powi(2) + (b[1] - a[1]).powi(2) + (b[2] - a[2]).powi(2)).sqrt();
        (m, 0.5 * len / k as f64)
    }

    #[test]
    fn grid_aliases_match_the_grid_world() {
        let w = World::new(1337);
        assert_eq!((w.x0, w.x1, w.y0, w.y1), (-MAP_HALF, MAP_HALF, -MAP_HALF, MAP_HALF));
        assert_eq!((w.tnx, w.tny, w.raw.nx, w.raw.ny), (TN, TN, NC, NC));
    }

    #[test]
    fn hull_is_ccw_and_convex() {
        let mut r = Rng::new(7);
        for _ in 0..2000 {
            let p = rand_poly(&mut r);
            let n = p.len();
            for i in 0..n {
                let (a, b, c) = (p[i], p[(i + 1) % n], p[(i + 2) % n]);
                assert!((b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]) > 0.0);
            }
        }
    }

    #[test]
    fn point_poly_matches_boundary_sampling() {
        let mut r = Rng::new(11);
        for _ in 0..3000 {
            let poly = rand_poly(&mut r);
            let q = [r.range(-60.0, 60.0), r.range(-60.0, 60.0)];
            let d = pt_poly_dist2(q, &poly).sqrt();
            // Inside iff winding test says so; outside: min over finely sampled edges.
            let n = poly.len();
            let mut m = f64::INFINITY;
            let mut inside = true;
            for i in 0..n {
                let (v, w) = (poly[i], poly[(i + 1) % n]);
                if (w[0] - v[0]) * (q[1] - v[1]) - (w[1] - v[1]) * (q[0] - v[0]) < 0.0 {
                    inside = false;
                }
                for s in 0..=200 {
                    let t = s as f64 / 200.0;
                    let p = [v[0] + (w[0] - v[0]) * t, v[1] + (w[1] - v[1]) * t];
                    m = m.min(((p[0] - q[0]).powi(2) + (p[1] - q[1]).powi(2)).sqrt());
                }
            }
            if inside {
                assert_eq!(d, 0.0);
            } else {
                assert!(d <= m + 1e-9 && d >= m - 0.2, "d {d} sampled {m}");
            }
        }
    }

    #[test]
    fn seg_prism_matches_dense_sampling() {
        let mut r = Rng::new(3);
        for _ in 0..4000 {
            let poly = rand_poly(&mut r);
            let z0 = r.range(-10.0, 10.0);
            let z1 = z0 + r.range(1.0, 50.0);
            let a = rand_pt(&mut r);
            // Mix long segments with short ones, as the predictor uses.
            let b = if r.chance(0.5) {
                rand_pt(&mut r)
            } else {
                [a[0] + r.range(-6.0, 6.0), a[1] + r.range(-6.0, 6.0), a[2] + r.range(-2.0, 2.0)]
            };
            let d = seg_prism_dist2(a, b, &poly, z0, z1).sqrt();
            let (m, err) = sampled(a, b, &poly, z0, z1);
            assert!(d <= m + 1e-9, "exact {d} above a sample {m}");
            assert!(d >= m - err - 1e-9, "exact {d} below the sampling bound {m} - {err}");
        }
    }

    #[test]
    fn seg_prism_axis_aligned_equals_box() {
        let mut r = Rng::new(5);
        for _ in 0..4000 {
            let (x0, y0, z0) = (r.range(-30.0, 30.0), r.range(-30.0, 30.0), r.range(-5.0, 5.0));
            let (x1, y1, z1) = (x0 + r.range(1.0, 40.0), y0 + r.range(1.0, 40.0), z0 + r.range(1.0, 40.0));
            let poly = [[x0, y0], [x1, y0], [x1, y1], [x0, y1]];
            let (a, b) = (rand_pt(&mut r), rand_pt(&mut r));
            let p = seg_prism_dist2(a, b, &poly, z0, z1);
            let q = seg_aabb_dist2(a, b, [x0, y0, z0], [x1, y1, z1]);
            assert!((p - q).abs() <= 1e-7 * (1.0 + q), "prism {p} box {q}");
        }
    }

    #[test]
    fn degenerate_segments() {
        let poly = [[0.0, 0.0], [10.0, 0.0], [10.0, 10.0], [0.0, 10.0]];
        // A point, a vertical segment through the roof, one along an edge line.
        assert!((seg_prism_dist2([15.0, 5.0, 5.0], [15.0, 5.0, 5.0], &poly, 0.0, 20.0) - 25.0).abs() < 1e-12);
        assert_eq!(seg_prism_dist2([5.0, 5.0, 30.0], [5.0, 5.0, 10.0], &poly, 0.0, 20.0), 0.0);
        assert!((seg_prism_dist2([-5.0, 0.0, 5.0], [-5.0, 10.0, 5.0], &poly, 0.0, 20.0) - 25.0).abs() < 1e-12);
        assert!((seg_prism_dist2([12.0, -3.0, 25.0], [12.0, 13.0, 25.0], &poly, 0.0, 20.0) - 29.0).abs() < 1e-12);
    }

    #[test]
    fn strip_range_matches_sampling() {
        let mut r = Rng::new(13);
        for _ in 0..2000 {
            let poly = rand_poly(&mut r);
            let ya = r.range(-50.0, 50.0);
            let yb = ya + 2.5;
            let got = strip_x_range(&poly, ya, yb);
            // Reference: clip the polygon to the strip (Sutherland-Hodgman).
            let clip = |p: Vec<[f64; 2]>, keep: &dyn Fn(f64) -> f64| -> Vec<[f64; 2]> {
                let mut out = Vec::new();
                for i in 0..p.len() {
                    let (u, v) = (p[i], p[(i + 1) % p.len()]);
                    let (fu, fv) = (keep(u[1]), keep(v[1]));
                    if fu >= 0.0 {
                        out.push(u);
                    }
                    if (fu >= 0.0) != (fv >= 0.0) {
                        let t = fu / (fu - fv);
                        out.push([u[0] + t * (v[0] - u[0]), u[1] + t * (v[1] - u[1])]);
                    }
                }
                out
            };
            let c = clip(clip(poly.clone(), &|y| y - ya), &|y| yb - y);
            match got {
                None => assert!(c.is_empty()),
                Some((a, b)) => {
                    let lo = c.iter().map(|q| q[0]).fold(f64::INFINITY, f64::min);
                    let hi = c.iter().map(|q| q[0]).fold(f64::NEG_INFINITY, f64::max);
                    assert!((a - lo).abs() < 1e-9 && (b - hi).abs() < 1e-9, "{a} {b} vs {lo} {hi}");
                }
            }
            // And every inside sample falls in the range.
            for sx in 0..=600 {
                let x = -60.0 + 120.0 * sx as f64 / 600.0;
                for y in [ya, 0.5 * (ya + yb), yb] {
                    if pt_poly_dist2([x, y], &poly) == 0.0 {
                        let (a, b) = got.unwrap();
                        assert!(x >= a - 1e-9 && x <= b + 1e-9);
                    }
                }
            }
        }
    }

    #[test]
    fn building_dist_ring_search_is_exact() {
        // Ring pruning must agree with brute force over every building.
        let w = World::new(1337);
        let mut r = Rng::new(17);
        for _ in 0..3000 {
            let p = [r.range(-1500.0, 1500.0), r.range(-1500.0, 1500.0), r.range(0.0, 300.0)];
            let brute = w.boxes.iter().fold(200.0f64, |d, b| d.min(w.bld_dist2(b, p).sqrt()));
            assert_eq!(w.building_dist(p, 200.0), brute);
        }
    }

    #[test]
    fn golden_gate_open_under_the_deck() {
        use crate::golden_gate as gg;
        let w = World::san_francisco();
        let p = |s: f64, a: f64, z: f64| {
            let q = gg::at(s, a);
            [q[0], q[1], z]
        };
        let mid = 0.5 * gg::MAIN;
        // Under the deck mid-span: open water up to the truss (67 m clearance).
        let under = p(mid, 0.0, 30.0);
        assert!(w.true_clearance(under) > 20.0, "{}", w.true_clearance(under));
        // In the deck, in the suspender wall and on the main cable: solid.
        assert!(w.true_clearance(p(mid, 0.0, gg::deck(mid) - 3.0)) < 0.0);
        assert!(w.true_clearance(p(mid - 200.0, gg::CABLE, gg::deck(mid - 200.0) + 20.0)) < 0.0);
        for s in [-200.0, 100.0, mid, 1100.0, gg::MAIN + 200.0] {
            assert_eq!(w.building_dist(p(s, -gg::CABLE, gg::cable(s)), 50.0), 0.0, "cable at s = {s}");
        }
        // Beside the bridge, well clear of the cable plane.
        assert!(w.true_clearance(p(mid, 60.0, 100.0)) > 40.0);
    }

    #[test]
    fn san_francisco_loads() {
        let w = World::san_francisco();
        assert!(w.boxes.len() > 30_000);
        let tc = w.tallest_center();
        // Salesforce Tower: 326 m, about (691, -138) in the map frame.
        assert!((tc[0] - 691.0).abs() < 40.0 && (tc[1] + 138.0).abs() < 40.0, "{tc:?}");
        assert!(tc[2] > 320.0 && tc[2] < 335.0, "{tc:?}");
        for b in &w.boxes {
            assert!(b.z1 > b.z0 && b.pn >= 3);
            let poly = w.footprint(b);
            // Every footprint vertex is at most on the boundary of its prism.
            assert!(poly.iter().all(|q| pt_poly_dist2(*q, poly) == 0.0));
        }
        for name in ["Market Street", "Mission Street", "Folsom Street", "California Street", "Van Ness Avenue", "Geary Street"] {
            let l = w.street_line(name).expect(name);
            eprintln!("{name:<18} p0 ({:>6.0},{:>6.0}) dir {:>6.1} deg  len {:>5.0} m  rms {:.2} m", l.p0[0], l.p0[1], l.dir.to_degrees(), l.len, l.rms);
            assert!(l.len > 1500.0 && l.rms < 3.0, "{name}: {l:?}");
        }
        let nob = w.hilltop_near([-800.0, 200.0], 400.0);
        assert!(nob[2] > 100.0, "{nob:?}");
        // Street axes: the grid north of Market runs ~9.6 deg off the map's
        // x axis, the SoMa grid parallel to Market Street (~45 deg), so they
        // differ by ~35 deg modulo 90.
        let (n, so) = (w.street_axis(-900.0, 600.0).unwrap(), w.street_axis(300.0, -900.0).unwrap());
        let california = w.street_line("California Street").unwrap().dir;
        let mission = w.street_line("Mission Street").unwrap().dir;
        let m90 = |a: f64| (a + std::f64::consts::FRAC_PI_4).rem_euclid(std::f64::consts::FRAC_PI_2) - std::f64::consts::FRAC_PI_4;
        eprintln!("axis north of Market {:.1} deg, SoMa {:.1} deg", n.to_degrees(), so.to_degrees());
        assert!(m90(n - california).abs() < 0.03 && m90(so - mission).abs() < 0.03);
        assert!((m90(n - so).abs() - 35f64.to_radians()).abs() < 3f64.to_radians());
        // Ring search agrees with brute force in the dense SF data too.
        let mut r = Rng::new(19);
        for _ in 0..300 {
            let p = [r.range(-2500.0, 2500.0), r.range(-2500.0, 2500.0), r.range(0.0, 200.0)];
            let brute = w.boxes.iter().fold(200.0f64, |d, b| d.min(w.bld_dist2(b, p).sqrt()));
            assert_eq!(w.building_dist(p, 200.0), brute);
        }
    }
}
