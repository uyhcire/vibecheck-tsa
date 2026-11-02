//! Writes the procedural city the gatekeeper filter checks against as plain files, and checks them.
//!
//! `city-export map OUTDIR [SEED]`: `map.json` (conventions), `buildings.csv`, `terrain.csv` (default seed 1337).
//! `city-export check OUTDIR`: rebuilds the filter's geometry from the files alone and compares it with
//! `World::new(seed)` bit for bit: terrain heights, boxes, and the 2.5 m max-height raster.
//! `city-export map-sf OUTDIR` / `check-sf OUTDIR`: the same for San Francisco (`World::load(MapId::SanFrancisco)`),
//! whose buildings are convex prisms: `footprints.csv` holds them, `buildings.csv` the boxes covering them that the
//! Lean city gate checks against (`cityflight::covering`), and the check also confirms the boxes contain the prisms.

use cityflight::covering::{cover, covers, COVER_TOL, MAX_STRIPS};
use cityflight::world::{street_x, Building, MapId, World, CELL, MAP_HALF, NC, R_BODY, TN, TSP};
use std::fmt::Write as _;
use std::io::Write;
use std::path::Path;

const FORMAT: &str = "cityflight-map 1";

fn write_map(dir: &Path, seed: u64) {
    std::fs::create_dir_all(dir).expect("create output directory");
    let w = World::new(seed);
    let mut t = String::with_capacity(TN * TN * 10);
    for j in 0..TN {
        let row: Vec<String> = (0..TN).map(|i| format!("{}", w.terr[j * TN + i])).collect();
        writeln!(t, "{}", row.join(",")).unwrap();
    }
    std::fs::write(dir.join("terrain.csv"), t).expect("write terrain.csv");
    let mut b = String::from("id,lot,x_min,y_min,x_max,y_max,z_min,z_max\n");
    for (k, x) in w.boxes.iter().enumerate() {
        writeln!(b, "{k},{},{},{},{},{},{},{}", x.lot, x.x0, x.y0, x.x1, x.y1, x.z0, x.z1).unwrap();
    }
    std::fs::write(dir.join("buildings.csv"), b).expect("write buildings.csv");
    let streets: Vec<String> =
        w.street_w.iter().enumerate().map(|(k, sw)| format!("{{\"axis\": {}, \"width\": {sw}}}", street_x(k))).collect();
    let tc = w.tallest_center();
    let json = format!(
        r#"{{
  "format": "{FORMAT}",
  "seed": {seed},
  "units": "metres",
  "axes": "x east, y north, z up. Map (0, 0) is the point gate_config places at origin_lat_deg, origin_lon_deg; x and y are east and north on the tangent plane there (gate_map_to_geodetic converts). z is altitude above sea level minus origin_alt_m.",
  "extent": {{"x_min": {lo}, "x_max": {hi}, "y_min": {lo}, "y_max": {hi}, "outside": "no obstacles; an escape that leaves the extent counts as clear"}},
  "terrain": {{
    "file": "terrain.csv",
    "x0": {lo}, "y0": {lo}, "spacing": {TSP}, "nx": {TN}, "ny": {TN},
    "layout": "row j is y = y0 + j * spacing (south to north), column i is x = x0 + i * spacing (west to east); heights are float32 written in shortest round-trip form",
    "interpolation": "each grid square splits along its south-west to north-east diagonal: with u = (x - x_i) / spacing and v = (y - y_j) / spacing, h = h00 + u (h10 - h00) + v (h11 - h10) if u >= v, else h00 + v (h01 - h00) + u (h11 - h01), where h10 is one step east and h01 one step north; positions outside the grid clamp to its edge"
  }},
  "buildings": {{
    "file": "buildings.csv",
    "count": {nb},
    "shape": "axis-aligned boxes [x_min, x_max] x [y_min, y_max] x [z_min, z_max]; a tower is several stacked boxes with the same lot; z_min is below the terrain"
  }},
  "streets": {{"axes": [{streets}], "note": "street centre lines run north-south at x = axis and east-west at y = axis inside the city (|x|, |y| <= {city}); the street escape climbs along them"}},
  "tallest_building": {{"x": {tx}, "y": {ty}, "z_max": {tz}}},
  "map_top": {top},
  "raster": "the filter also checks a {CELL} m max-height raster derived from the above: over each {NC} x {NC} cell starting at (x0, y0), the maximum of the terrain at the cell's four corners and of z_max for every box overlapping the cell",
  "clearance": {{"margin": 4.0, "body_radius": {R_BODY}, "wing_capsule_radius": 0.8, "wingspan": 11.0, "note": "an escape is verified only if the body sphere and the wing capsule keep margin metres from terrain and boxes along it"}}
}}
"#,
        lo = -MAP_HALF,
        hi = MAP_HALF,
        nb = w.boxes.len(),
        streets = streets.join(", "),
        city = cityflight::world::CITY_HALF,
        tx = tc[0],
        ty = tc[1],
        tz = tc[2],
        top = w.raw_top,
    );
    std::fs::write(dir.join("map.json"), json).expect("write map.json");
    eprintln!("wrote {}: {} buildings, {TN} x {TN} terrain grid, seed {seed}", dir.display(), w.boxes.len());
}

fn json_number(json: &str, key: &str) -> f64 {
    let k = format!("\"{key}\":");
    let at = json.find(&k).unwrap_or_else(|| panic!("map.json: no {key}")) + k.len();
    let rest = json[at..].trim_start();
    let end = rest.find(|c: char| !(c.is_ascii_digit() || "-+.eE".contains(c))).unwrap_or(rest.len());
    rest[..end].parse().unwrap_or_else(|_| panic!("map.json: bad {key}"))
}

/// The terrain function of `map.json`, from `terrain.csv` alone.
fn terrain_at(h: &[f32], x: f64, y: f64) -> f64 {
    let fx = ((x + MAP_HALF) / TSP).clamp(0.0, (TN - 1) as f64 - 1e-9);
    let fy = ((y + MAP_HALF) / TSP).clamp(0.0, (TN - 1) as f64 - 1e-9);
    let (i, j) = (fx as usize, fy as usize);
    let (u, v) = (fx - i as f64, fy - j as f64);
    let at = |i: usize, j: usize| h[j * TN + i] as f64;
    let (h00, h10, h01, h11) = (at(i, j), at(i + 1, j), at(i, j + 1), at(i + 1, j + 1));
    if u >= v {
        h00 + u * (h10 - h00) + v * (h11 - h10)
    } else {
        h00 + v * (h01 - h00) + u * (h11 - h01)
    }
}

fn check(dir: &Path) -> bool {
    let json = std::fs::read_to_string(dir.join("map.json")).expect("read map.json");
    assert!(json.contains(FORMAT), "map.json: not {FORMAT}");
    let seed = json_number(&json, "seed") as u64;
    let terr: Vec<f32> = std::fs::read_to_string(dir.join("terrain.csv"))
        .expect("read terrain.csv")
        .lines()
        .flat_map(|l| l.split(',').map(|v| v.parse::<f32>().expect("terrain value")).collect::<Vec<_>>())
        .collect();
    let boxes: Vec<[f64; 6]> = std::fs::read_to_string(dir.join("buildings.csv"))
        .expect("read buildings.csv")
        .lines()
        .skip(1)
        .map(|l| {
            let f: Vec<f64> = l.split(',').skip(2).map(|v| v.parse().expect("box value")).collect();
            [f[0], f[1], f[2], f[3], f[4], f[5]]
        })
        .collect();
    let w = World::new(seed);
    let mut ok = true;
    let mut report = |name: &str, good: bool| {
        println!("{} {name}", if good { "ok  " } else { "FAIL" });
        ok &= good;
    };
    report("terrain grid", terr.len() == TN * TN && terr.iter().zip(&w.terr).all(|(a, b)| a.to_bits() == b.to_bits()));
    let same = |b: &Building, f: &[f64; 6]| [b.x0, b.y0, b.x1, b.y1, b.z0, b.z1].iter().zip(f).all(|(a, c)| a.to_bits() == c.to_bits());
    report("buildings", boxes.len() == w.boxes.len() && w.boxes.iter().zip(&boxes).all(|(b, f)| same(b, f)));
    let mut rng = cityflight::world::Rng::new(7);
    let pts = 200_000;
    let terrain_same = (0..pts).all(|_| {
        let (x, y) = ((rng.f() * 2.0 - 1.0) * MAP_HALF * 1.01, (rng.f() * 2.0 - 1.0) * MAP_HALF * 1.01);
        terrain_at(&terr, x, y).to_bits() == w.terrain(x, y).to_bits()
    });
    report(&format!("terrain function at {pts} random points"), terrain_same);
    // The raster as `World::rasterize` derives it, from the files.
    let np = NC + 1;
    let corner: Vec<f32> = (0..np * np)
        .map(|k| terrain_at(&terr, -MAP_HALF + (k % np) as f64 * CELL, -MAP_HALF + (k / np) as f64 * CELL) as f32)
        .collect();
    let mut raster: Vec<f32> = (0..NC * NC)
        .map(|k| {
            let (i, j) = (k % NC, k / NC);
            corner[j * np + i].max(corner[j * np + i + 1]).max(corner[(j + 1) * np + i]).max(corner[(j + 1) * np + i + 1])
        })
        .collect();
    let ci = |v: f64| (((v + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
    for b in &boxes {
        for j in ci(b[1])..=ci(b[3]) {
            for i in ci(b[0])..=ci(b[2]) {
                raster[j * NC + i] = raster[j * NC + i].max(b[5] as f32);
            }
        }
    }
    report("2.5 m max-height raster", raster.len() == w.raw.v.len() && raster.iter().zip(&w.raw.v).all(|(a, b)| a.to_bits() == b.to_bits()));
    report("map_top", json_number(&json, "map_top").to_bits() == w.raw_top.to_bits());
    ok
}


const FORMAT_SF: &str = "cityflight-map 2";

fn write_sf(dir: &Path) {
    std::fs::create_dir_all(dir).expect("create output directory");
    let w = World::load(MapId::SanFrancisco);
    let mut t = String::with_capacity(w.tnx * w.tny * 10);
    for j in 0..w.tny {
        let row: Vec<String> = (0..w.tnx).map(|i| format!("{}", w.terr[j * w.tnx + i])).collect();
        writeln!(t, "{}", row.join(",")).unwrap();
    }
    std::fs::write(dir.join("terrain.csv"), t).expect("write terrain.csv");
    let mut f = String::from("id,lot,z_min,z_max,n,x_1,y_1,x_2,y_2,...\n");
    for (k, b) in w.boxes.iter().enumerate() {
        let pts: Vec<String> = w.outline(b).iter().map(|q| format!("{},{}", q[0], q[1])).collect();
        writeln!(f, "{k},{},{},{},{},{}", b.lot, b.z0, b.z1, pts.len(), pts.join(",")).unwrap();
    }
    std::fs::write(dir.join("footprints.csv"), f).expect("write footprints.csv");
    let c = cover(&w);
    let mut bx = String::from("id,footprint,x_min,y_min,x_max,y_max,z_min,z_max\n");
    for (k, (b, of)) in c.boxes.iter().zip(&c.of).enumerate() {
        writeln!(bx, "{k},{of},{},{},{},{},{},{}", b[0], b[1], b[2], b[3], b[4], b[5]).unwrap();
    }
    std::fs::write(dir.join("buildings.csv"), bx).expect("write buildings.csv");
    let json = format!(
        r#"{{
  "format": "{FORMAT_SF}",
  "map": "San Francisco (flight/data/sf/sf_world.bin, World::load(MapId::SanFrancisco))",
  "units": "metres",
  "axes": "x east, y north, z up (NAVD88 m); map (0, 0) is Kearny & Market",
  "extent": {{"x_min": {x0}, "x_max": {x1}, "y_min": {y0}, "y_max": {y1}, "outside": "the terrain continues its edge; no buildings"}},
  "terrain": {{
    "file": "terrain.csv",
    "x0": {x0}, "y0": {y0}, "spacing": {TSP}, "nx": {tnx}, "ny": {tny},
    "layout": "row j is y = y0 + j * spacing (south to north), column i is x = x0 + i * spacing (west to east); heights are float32 written in shortest round-trip form, already raised to the water surface",
    "interpolation": "as cityflight-map 1: each grid square splits along its south-west to north-east diagonal; positions outside the grid clamp to its edge"
  }},
  "footprints": {{
    "file": "footprints.csv",
    "count": {nf},
    "shape": "vertical prisms: the convex footprint (n vertices x_k, y_k, counter-clockwise) times [z_min, z_max]; this is the geometry collisions are judged against"
  }},
  "buildings": {{
    "file": "buildings.csv",
    "count": {nb},
    "shape": "axis-aligned boxes containing the prisms (column footprint): each footprint is cut into strips across x or y, each strip covered by the box of its extent, until every box point is within {COVER_TOL} m of the footprint (or {MAX_STRIPS} strips); the Lean city gate checks clearance against these"
  }},
  "raster": "the filter's {CELL} m max-height raster ({rnx} x {rny} cells from (x0, y0)): per cell the maximum of the terrain at its corners and of z_max for every footprint whose part in the cell's row meets the cell",
  "map_top": {top}
}}
"#,
        x0 = w.x0,
        x1 = w.x1,
        y0 = w.y0,
        y1 = w.y1,
        tnx = w.tnx,
        tny = w.tny,
        nf = w.boxes.len(),
        nb = c.boxes.len(),
        rnx = w.raw.nx,
        rny = w.raw.ny,
        top = w.raw_top,
    );
    std::fs::write(dir.join("map.json"), json).expect("write map.json");
    eprintln!("wrote {}: {} footprints, {} covering boxes, {} x {} terrain grid", dir.display(), w.boxes.len(), c.boxes.len(), w.tnx, w.tny);
}

/// The terrain function of `map.json` on a `nx x ny` grid from `(x0, y0)`.
fn terrain_rect(h: &[f32], x0: f64, y0: f64, nx: usize, ny: usize, x: f64, y: f64) -> f64 {
    let fx = ((x - x0) / TSP).clamp(0.0, (nx - 1) as f64 - 1e-9);
    let fy = ((y - y0) / TSP).clamp(0.0, (ny - 1) as f64 - 1e-9);
    let (i, j) = (fx as usize, fy as usize);
    let (u, v) = (fx - i as f64, fy - j as f64);
    let at = |i: usize, j: usize| h[j * nx + i] as f64;
    let (h00, h10, h01, h11) = (at(i, j), at(i + 1, j), at(i, j + 1), at(i + 1, j + 1));
    if u >= v {
        h00 + u * (h10 - h00) + v * (h11 - h10)
    } else {
        h00 + v * (h01 - h00) + u * (h11 - h01)
    }
}

/// The x-range of a convex polygon's part with `y` in `[ya, yb]`.
fn strip_x(poly: &[[f64; 2]], ya: f64, yb: f64) -> Option<(f64, f64)> {
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

fn check_sf(dir: &Path) -> bool {
    let json = std::fs::read_to_string(dir.join("map.json")).expect("read map.json");
    assert!(json.contains(FORMAT_SF), "map.json: not {FORMAT_SF}");
    let (x0, y0) = (json_number(&json, "x_min"), json_number(&json, "y_min"));
    let (nx, ny) = (json_number(&json, "nx") as usize, json_number(&json, "ny") as usize);
    let terr: Vec<f32> = std::fs::read_to_string(dir.join("terrain.csv"))
        .expect("read terrain.csv")
        .lines()
        .flat_map(|l| l.split(',').map(|v| v.parse::<f32>().expect("terrain value")).collect::<Vec<_>>())
        .collect();
    let feet: Vec<(f64, f64, Vec<[f64; 2]>)> = std::fs::read_to_string(dir.join("footprints.csv"))
        .expect("read footprints.csv")
        .lines()
        .skip(1)
        .map(|l| {
            let f: Vec<f64> = l.split(',').skip(2).map(|v| v.parse().expect("footprint value")).collect();
            let n = f[2] as usize;
            assert_eq!(f.len(), 3 + 2 * n, "footprints.csv: vertex count");
            (f[0], f[1], (0..n).map(|k| [f[3 + 2 * k], f[4 + 2 * k]]).collect())
        })
        .collect();
    let boxes: Vec<(usize, [f64; 6])> = std::fs::read_to_string(dir.join("buildings.csv"))
        .expect("read buildings.csv")
        .lines()
        .skip(1)
        .map(|l| {
            let f: Vec<&str> = l.split(',').collect();
            let v: Vec<f64> = f[2..].iter().map(|v| v.parse().expect("box value")).collect();
            (f[1].parse().expect("footprint id"), [v[0], v[1], v[2], v[3], v[4], v[5]])
        })
        .collect();
    let w = World::load(MapId::SanFrancisco);
    let mut ok = true;
    let mut report = |name: &str, good: bool| {
        println!("{} {name}", if good { "ok  " } else { "FAIL" });
        ok &= good;
    };
    report(
        "extent and terrain grid",
        [x0, y0].iter().zip([w.x0, w.y0]).all(|(a, b)| a.to_bits() == b.to_bits())
            && (nx, ny) == (w.tnx, w.tny)
            && terr.len() == nx * ny
            && terr.iter().zip(&w.terr).all(|(a, b)| a.to_bits() == b.to_bits()),
    );
    let same = |a: f64, b: f64| a.to_bits() == b.to_bits();
    report(
        "footprints",
        feet.len() == w.boxes.len()
            && w.boxes.iter().zip(&feet).all(|(b, (z0, z1, p))| {
                let o = w.outline(b);
                same(b.z0, *z0) && same(b.z1, *z1) && o.len() == p.len() && o.iter().zip(p).all(|(q, r)| same(q[0], r[0]) && same(q[1], r[1]))
            }),
    );
    let c = cover(&w);
    report(
        "covering boxes as cityflight::covering builds them",
        c.boxes.len() == boxes.len() && c.boxes.iter().zip(&c.of).zip(&boxes).all(|((b, of), (f, v))| *of as usize == *f && b.iter().zip(v).all(|(a, b)| same(*a, *b))),
    );
    let mut by: Vec<Vec<[f64; 6]>> = vec![Vec::new(); feet.len()];
    for (f, v) in &boxes {
        by[*f].push(*v);
    }
    report("every footprint prism inside its covering boxes", feet.iter().zip(&by).all(|((z0, z1, p), bs)| covers(p, *z0, *z1, bs)));
    let mut rng = cityflight::world::Rng::new(7);
    let pts = 200_000;
    let (wx, wy) = (w.x1 - w.x0, w.y1 - w.y0);
    let terrain_same = (0..pts).all(|_| {
        let (x, y) = (w.x0 - 0.01 * wx + rng.f() * 1.02 * wx, w.y0 - 0.01 * wy + rng.f() * 1.02 * wy);
        terrain_rect(&terr, x0, y0, nx, ny, x, y).to_bits() == w.terrain(x, y).to_bits()
    });
    report(&format!("terrain function at {pts} random points"), terrain_same);
    // The raster as `World::rasterize` derives it, from the files.
    let (rnx, rny) = (w.raw.nx, w.raw.ny);
    let np = rnx + 1;
    let corner = |i: usize, j: usize| terrain_rect(&terr, x0, y0, nx, ny, x0 + i as f64 * CELL, y0 + j as f64 * CELL) as f32;
    let mut raster: Vec<f32> = vec![0.0; rnx * rny];
    let mut lo_row: Vec<f32> = (0..np).map(|i| corner(i, 0)).collect();
    for j in 0..rny {
        let hi_row: Vec<f32> = (0..np).map(|i| corner(i, j + 1)).collect();
        for i in 0..rnx {
            raster[j * rnx + i] = lo_row[i].max(lo_row[i + 1]).max(hi_row[i]).max(hi_row[i + 1]);
        }
        lo_row = hi_row;
    }
    let cx = |v: f64| (((v - x0) / CELL).floor().max(0.0) as usize).min(rnx - 1);
    let cy = |v: f64| (((v - y0) / CELL).floor().max(0.0) as usize).min(rny - 1);
    for (_, z1, p) in &feet {
        let (ylo, yhi) = p.iter().fold((f64::INFINITY, f64::NEG_INFINITY), |a, q| (a.0.min(q[1]), a.1.max(q[1])));
        for j in cy(ylo)..=cy(yhi) {
            let ya = y0 + j as f64 * CELL;
            let Some((xa, xb)) = strip_x(p, ya, ya + CELL) else { continue };
            for i in cx(xa)..=cx(xb) {
                raster[j * rnx + i] = raster[j * rnx + i].max(*z1 as f32);
            }
        }
    }
    report(
        "2.5 m max-height raster",
        raster.len() == w.raw.v.len() && raster.iter().zip(&w.raw.v).all(|(a, b)| a.to_bits() == b.to_bits()),
    );
    report("map_top", json_number(&json, "map_top").to_bits() == w.raw_top.to_bits());
    // Extra caution of the covering: area, and how far box points reach beyond their footprints.
    let area = |p: &[[f64; 2]]| (0..p.len()).map(|k| p[k][0] * p[(k + 1) % p.len()][1] - p[(k + 1) % p.len()][0] * p[k][1]).sum::<f64>().abs() / 2.0;
    let fa: f64 = feet.iter().map(|f| area(&f.2)).sum();
    let ba: f64 = boxes.iter().map(|(_, b)| (b[2] - b[0]) * (b[3] - b[1])).sum();
    let bb: f64 = feet.iter().map(|f| {
        let (a, b) = f.2.iter().fold(([f64::INFINITY; 2], [f64::NEG_INFINITY; 2]), |(l, h), q| ([l[0].min(q[0]), l[1].min(q[1])], [h[0].max(q[0]), h[1].max(q[1])]));
        (b[0] - a[0]) * (b[1] - a[1])
    }).sum();
    let mut ex: Vec<f64> = boxes
        .iter()
        .map(|(f, b)| {
            let p = &feet[*f].2;
            [[b[0], b[1]], [b[2], b[1]], [b[0], b[3]], [b[2], b[3]]].iter().map(|c| cityflight::world::pt_poly_dist2(*c, p)).fold(0.0, f64::max).sqrt()
        })
        .collect();
    ex.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let q = |f: f64| ex[((ex.len() - 1) as f64 * f) as usize];
    println!(
        "covering: {} boxes for {} footprints; footprint area {:.2} km^2, boxes {:.2} km^2 (+{:.1}%; one bounding box each would be +{:.1}%); box point beyond its footprint: median {:.2} m, p99 {:.2} m, max {:.2} m",
        boxes.len(),
        feet.len(),
        fa / 1e6,
        ba / 1e6,
        100.0 * (ba / fa - 1.0),
        100.0 * (bb / fa - 1.0),
        q(0.5),
        q(0.99),
        q(1.0)
    );
    ok
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let dir = Path::new(args.get(1).map(String::as_str).unwrap_or("city-map"));
    match args.first().map(String::as_str) {
        Some("map") => write_map(dir, args.get(2).map_or(1337, |s| s.parse().expect("seed"))),
        Some("check") => {
            if !check(dir) {
                std::process::exit(1);
            }
        }
        Some("map-sf") => write_sf(dir),
        Some("check-sf") => {
            if !check_sf(dir) {
                std::process::exit(1);
            }
        }
        _ => {
            let _ = writeln!(std::io::stderr(), "usage: city-export map OUTDIR [SEED] | check OUTDIR | map-sf OUTDIR | check-sf OUTDIR");
            std::process::exit(2);
        }
    }
}
