//! Writes the procedural city the gatekeeper filter checks against as plain files, and checks them.
//!
//! `city-export map OUTDIR [SEED]`: `map.json` (conventions), `buildings.csv`, `terrain.csv` (default seed 1337).
//! `city-export check OUTDIR`: rebuilds the filter's geometry from the files alone and compares it with
//! `World::new(seed)` bit for bit: terrain heights, boxes, and the 2.5 m max-height raster.

use cityflight::world::{street_x, Building, World, CELL, MAP_HALF, NC, R_BODY, TN, TSP};
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
    report("2.5 m max-height raster", raster.iter().zip(&w.raw).all(|(a, b)| a.to_bits() == b.to_bits()));
    report("map_top", json_number(&json, "map_top").to_bits() == w.raw_top.to_bits());
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
        _ => {
            let _ = writeln!(std::io::stderr(), "usage: city-export map OUTDIR [SEED] | city-export check OUTDIR");
            std::process::exit(2);
        }
    }
}
