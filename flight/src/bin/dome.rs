//! `dome OUT [--check N]`: the circle-safe dome, the terminal set of the city gate drawn as a surface over the city.
//!
//! For a circle radius `r` and a centre `c`, `D_r(c)` is the least altitude `z` at which `helix_check` (the gate's
//! terminal test for a steady climbing circle, `envfilter.rs`) passes: the highest raw raster cell under the annulus
//! `r ± (m + R_BODY)` plus `R_BODY + MARGIN`, capped at the ceiling `top + R_BODY + MARGIN` (which is also the
//! value wherever the annulus leaves the map). The annulus covers the same set of cell offsets for every centre on
//! a 10 m grid (10 m is four 2.5 m cells), so the maximum is exact, not an approximation; `--check N` compares it
//! with the real `helix_check` at N random centres. Writes the f32 grids, JSON headers, PNG heat-maps and stats.
use cityflight::envfilter::{helix_check, top, MARGIN};
use cityflight::world::*;
use std::fmt::Write as _;
use std::fs;

const CEIL: [u8; 3] = [225, 225, 225]; // cells at the ceiling
const STEP: f64 = 10.0; // centre-grid spacing (m)
const K: usize = 4; // cells per step
const N: usize = 601; // nodes per side: x = -3000 + 10 i, i = 0..=600
const RADII: [f64; 2] = [143.0, 250.0];
/// Primary drift allowance: `m = 5 + 3 (d_r + d_c)` with `d_r + d_c = 0.1 r` (see docs/dome.md).
const M_FRAC: f64 = 0.3;

fn drift(r: f64, frac: f64) -> f64 {
    5.0 + frac * r
}

struct Runs(Vec<(i64, i64, i64)>); // (row offset, first col offset, last col offset), in cells

fn annulus(r: f64, m: f64) -> Runs {
    let (r0, r1) = ((r - m - R_BODY).max(0.0), r + m + R_BODY);
    let pad = CELL * std::f64::consts::FRAC_1_SQRT_2;
    let (lo2, hi2) = ((r0 - pad).max(0.0).powi(2), (r1 + pad).powi(2));
    let lim = ((r1 + pad) / CELL).ceil() as i64 + 2;
    let mut runs = Vec::new();
    for oy in -lim..=lim {
        let dy = CELL * (oy as f64 + 0.5);
        let mut start: Option<i64> = None;
        for ox in -lim..=lim + 1 {
            let dx = CELL * (ox as f64 + 0.5);
            let inside = ox <= lim && {
                let d2 = dx * dx + dy * dy;
                d2 >= lo2 && d2 <= hi2
            };
            match (inside, start) {
                (true, None) => start = Some(ox),
                (false, Some(s)) => {
                    runs.push((oy, s, ox - 1));
                    start = None;
                }
                _ => {}
            }
        }
    }
    Runs(runs)
}

/// `D_r` on the 601 x 601 grid (row-major, y up), `ceil` where the annulus leaves the map.
fn dome(world: &World, r: f64, m: f64) -> Vec<f32> {
    let runs = annulus(r, m);
    let ceil = (top(world) + R_BODY + MARGIN) as f32;
    let r1 = r + m + R_BODY;
    let mut out = vec![ceil; N * N];
    let nthreads = 8;
    let rows_per = (N + nthreads - 1) / nthreads;
    std::thread::scope(|s| {
        for (t, chunk) in out.chunks_mut(rows_per * N).enumerate() {
            let runs = &runs;
            s.spawn(move || {
                for (jj, row) in chunk.chunks_mut(N).enumerate() {
                    let j = t * rows_per + jj;
                    let cy = -MAP_HALF + STEP * j as f64;
                    for (i, v) in row.iter_mut().enumerate() {
                        let cx = -MAP_HALF + STEP * i as f64;
                        if !(cx - r1 > -MAP_HALF && cx + r1 < MAP_HALF && cy - r1 > -MAP_HALF && cy + r1 < MAP_HALF) {
                            continue;
                        }
                        let (ci, cj) = ((K * i) as i64, (K * j) as i64);
                        let mut mx = f32::MIN;
                        for &(oy, a, b) in &runs.0 {
                            let y = cj + oy;
                            if y < 0 || y >= NC as i64 {
                                continue;
                            }
                            let (a, b) = ((ci + a).max(0), (ci + b).min(NC as i64 - 1));
                            if a > b {
                                continue;
                            }
                            for &h in &world.raw.v[y as usize * NC + a as usize..=y as usize * NC + b as usize] {
                                mx = mx.max(h);
                            }
                        }
                        *v = ((mx as f64 + R_BODY + MARGIN) as f32).min(ceil);
                    }
                }
            });
        }
    });
    out
}

// ---------------------------------------------------------------- PNG

const GLYPH: [[u8; 5]; 17] = [
    [7, 5, 5, 5, 7], [2, 6, 2, 2, 7], [7, 1, 7, 4, 7], [7, 1, 7, 1, 7], [5, 5, 7, 1, 1],
    [7, 4, 7, 1, 7], [7, 4, 7, 5, 7], [7, 1, 1, 1, 1], [7, 5, 7, 5, 7], [7, 5, 7, 1, 7], [0, 0, 5, 7, 5], // 0-9, m
    [0, 7, 4, 4, 7], [7, 5, 7, 4, 7], [2, 0, 2, 2, 2], [4, 4, 4, 4, 7], [0, 6, 5, 5, 5], [7, 5, 7, 1, 7], // c e i l n g
];

struct Img {
    w: usize,
    h: usize,
    px: Vec<u8>,
}

impl Img {
    fn new(w: usize, h: usize) -> Img {
        Img { w, h, px: vec![255; w * h * 3] }
    }
    fn set(&mut self, x: usize, y: usize, c: [u8; 3]) {
        if x < self.w && y < self.h {
            self.px[(y * self.w + x) * 3..][..3].copy_from_slice(&c);
        }
    }
    fn text(&mut self, x: usize, y: usize, s: &str, sc: usize) {
        for (k, ch) in s.chars().enumerate() {
            let g = match ch {
                '0'..='9' => GLYPH[ch as usize - '0' as usize],
                'm' => GLYPH[10],
                'c' => GLYPH[11],
                'e' => GLYPH[12],
                'i' => GLYPH[13],
                'l' => GLYPH[14],
                'n' => GLYPH[15],
                'g' => GLYPH[16],
                _ => continue,
            };
            for (row, bits) in g.iter().enumerate() {
                for col in 0..3 {
                    if bits >> (2 - col) & 1 == 1 {
                        for dy in 0..sc {
                            for dx in 0..sc {
                                self.set(x + k * 4 * sc + col * sc + dx, y + row * sc + dy, [0, 0, 0]);
                            }
                        }
                    }
                }
            }
        }
    }
    fn save(&self, path: &str) {
        let f = fs::File::create(path).unwrap();
        let mut enc = png::Encoder::new(std::io::BufWriter::new(f), self.w as u32, self.h as u32);
        enc.set_color(png::ColorType::Rgb);
        enc.set_depth(png::BitDepth::Eight);
        enc.set_compression(png::Compression::Best);
        enc.write_header().unwrap().write_image_data(&self.px).unwrap();
    }
}

fn colormap(t: f64) -> [u8; 3] {
    const S: [[f64; 3]; 5] = [[68.0, 1.0, 84.0], [59.0, 82.0, 139.0], [33.0, 145.0, 140.0], [94.0, 201.0, 98.0], [253.0, 200.0, 37.0]];
    let t = t.clamp(0.0, 1.0) * 4.0;
    let i = (t as usize).min(3);
    let u = t - i as f64;
    let c = |k: usize| (S[i][k] + u * (S[i + 1][k] - S[i][k])) as u8;
    [c(0), c(1), c(2)]
}

/// Bilinear sample of a node grid at world (x, y).
fn sample(g: &[f32], x: f64, y: f64) -> f64 {
    let fx = ((x + MAP_HALF) / STEP).clamp(0.0, (N - 1) as f64 - 1e-9);
    let fy = ((y + MAP_HALF) / STEP).clamp(0.0, (N - 1) as f64 - 1e-9);
    let (i, j, u, v) = (fx as usize, fy as usize, fx.fract(), fy.fract());
    let at = |a: usize, b: usize| g[b * N + a] as f64;
    (at(i, j) * (1.0 - u) + at(i + 1, j) * u) * (1.0 - v) + (at(i, j + 1) * (1.0 - u) + at(i + 1, j + 1) * u) * v
}

/// `value` per node (metres), drawn over `[-half, half]^2` at `mpp` metres per pixel with building outlines and a
/// colour bar labelled in metres; `vmax` is the top of the scale, `ceil` cells (value >= `cap`) are white.
fn render(world: &World, grid: &[f32], cap: f32, half: f64, mpp: f64, vmax: f64, label_m: bool, path: &str) {
    let n = (2.0 * half / mpp) as usize;
    let bar = 150;
    let mut img = Img::new(n + bar, n);
    let mut solid = vec![false; n * n];
    for b in &world.boxes {
        let px = |x: f64| (x + half) / mpp;
        let (i0, i1) = (px(b.x0).floor().max(0.0) as usize, (px(b.x1).ceil() as usize).min(n));
        let (j0, j1) = (px(b.y0).floor().max(0.0) as usize, (px(b.y1).ceil() as usize).min(n));
        for j in j0..j1 {
            for i in i0..i1 {
                solid[j * n + i] = true;
            }
        }
    }
    for py in 0..n {
        let y = half - (py as f64 + 0.5) * mpp; // north up
        let j = n - 1 - py;
        for px in 0..n {
            let x = -half + (px as f64 + 0.5) * mpp;
            let v = sample(grid, x, y);
            let c = if v >= cap as f64 - 1e-3 { CEIL } else { colormap(v / vmax) };
            img.set(px, py, c);
            let s = |i: i64, j: i64| i >= 0 && j >= 0 && (i as usize) < n && (j as usize) < n && solid[j as usize * n + i as usize];
            let (i, jj) = (px as i64, j as i64);
            if s(i, jj) && !(s(i - 1, jj) && s(i + 1, jj) && s(i, jj - 1) && s(i, jj + 1)) {
                img.set(px, py, [0, 0, 0]);
            }
        }
    }
    // colour bar with ticks in metres
    let (bx, bw, top_y, bh) = (n + 20, 24, 30usize, n.min(600) - 60);
    for k in 0..bh {
        let t = 1.0 - k as f64 / (bh - 1) as f64;
        for x in 0..bw {
            img.set(bx + x, top_y + k, colormap(t));
        }
    }
    let step = if vmax > 600.0 { 200.0 } else { 100.0 };
    let mut v = 0.0;
    while v <= vmax + 1e-9 {
        let y = top_y + ((1.0 - v / vmax) * (bh - 1) as f64) as usize;
        for x in 0..bw + 4 {
            img.set(bx + x, y, [0, 0, 0]);
        }
        img.text(bx + bw + 8, y.saturating_sub(5), &format!("{}m", v as i64), 2);
        v += step;
    }
    for y in top_y + bh + 10..top_y + bh + 40 {
        for x in 0..bw {
            img.set(bx + x, y, CEIL);
        }
    }
    for x in 0..bw {
        img.set(bx + x, top_y + bh + 10, [0, 0, 0]);
        img.set(bx + x, top_y + bh + 39, [0, 0, 0]);
    }
    for y in top_y + bh + 10..top_y + bh + 40 {
        img.set(bx, y, [0, 0, 0]);
        img.set(bx + bw - 1, y, [0, 0, 0]);
    }
    img.text(bx + bw + 8, top_y + bh + 12, "ceiling", 2);
    if label_m {
        img.text(bx + bw + 8, top_y + bh + 26, &format!("{}m", cap.round() as i64), 2);
    }
    img.save(path);
}

// ---------------------------------------------------------------- stats

fn quantile(v: &mut Vec<f64>, q: f64) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    if v.is_empty() { f64::NAN } else { v[((v.len() - 1) as f64 * q).round() as usize] }
}

fn region(world: &World, x: f64, y: f64) -> usize {
    if x.abs() > CITY_HALF || y.abs() > CITY_HALF {
        3 // outskirts: hills, ridge, rim
    } else if world.is_park(x, y) {
        2
    } else if ((x - 60.0).powi(2) + (y - 60.0).powi(2)).sqrt() <= 430.0 {
        0 // downtown core
    } else {
        1
    }
}

const REGIONS: [&str; 5] = ["downtown core (within 430 m of the tower)", "rest of the city blocks and streets", "parks", "outskirts (outside the city square)", "whole map"];

fn stats(world: &World, grid: &[f32], ceil: f32) -> String {
    let mut s = String::new();
    let mut agl: Vec<Vec<f64>> = vec![Vec::new(); 5];
    let mut at_ceil = vec![0usize; 5];
    for j in 0..N {
        for i in 0..N {
            let (x, y) = (-MAP_HALF + STEP * i as f64, -MAP_HALF + STEP * j as f64);
            let (d, g) = (grid[j * N + i], world.terrain(x, y));
            for k in [region(world, x, y), 4] {
                agl[k].push(d as f64 - g);
                at_ceil[k] += (d >= ceil - 1e-3) as usize;
            }
        }
    }
    writeln!(s, "| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |").unwrap();
    writeln!(s, "|---|---|---|---|---|---|---|").unwrap();
    for k in 0..5 {
        let a = &mut agl[k];
        let n = a.len() as f64;
        let f = |t: f64| 100.0 * a.iter().filter(|&&v| v < t).count() as f64 / n;
        let (f1, f2, f3) = (f(100.0), f(200.0), f(300.0));
        let med = quantile(a, 0.5);
        writeln!(s, "| {} | {:.1}% | {:.1}% | {:.1}% | {:.1}% | {:.1}% | {:.0} |", REGIONS[k], 100.0 * n / (N * N) as f64, f1, f2, f3, 100.0 * at_ceil[k] as f64 / n, med).unwrap();
    }
    s
}

fn line_stats(world: &World, grid: &[f32], pts: &[(f64, f64)]) -> String {
    let at = |x: f64, y: f64| {
        let (i, j) = (((x + MAP_HALF) / STEP).round() as usize, ((y + MAP_HALF) / STEP).round() as usize);
        grid[j * N + i] as f64 - world.terrain(x, y)
    };
    let mut v: Vec<f64> = pts.iter().map(|&(x, y)| at(x, y)).collect();
    let (lo, hi) = (v.iter().cloned().fold(f64::MAX, f64::min), v.iter().cloned().fold(f64::MIN, f64::max));
    format!("min {:.0} m, median {:.0} m, max {:.0} m", lo, quantile(&mut v, 0.5), hi)
}

fn write_grid(path: &str, g: &[f32], head: &str) {
    let mut b = Vec::with_capacity(g.len() * 4);
    for v in g {
        b.extend_from_slice(&v.to_le_bytes());
    }
    fs::write(format!("{path}.f32"), b).unwrap();
    fs::write(format!("{path}.json"), head).unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out = args.get(1).cloned().unwrap_or_else(|| "/tmp/dome".into());
    let nchk: usize = args.iter().position(|a| a == "--check").map(|p| args[p + 1].parse().unwrap()).unwrap_or(300);
    fs::create_dir_all(&out).unwrap();
    let world = World::new(1337);
    // The dome is computed on the default city, whose raster is the full NC x NC grid from -MAP_HALF.
    assert!(world.raw.nx == NC && world.raw.ny == NC && world.raw.x0 == -MAP_HALF && world.raw.y0 == -MAP_HALF);
    let ceil = (top(&world) + R_BODY + MARGIN) as f32;
    println!("zTop = {:.2} m (map top {:.2} + R_BODY {} + MARGIN {})", ceil, top(&world), R_BODY, MARGIN);
    let mut report = format!("zTop = {:.2} m (map top {:.2} m + R_BODY {} m + MARGIN {} m)\n", ceil, top(&world), R_BODY, MARGIN);

    for &r in &RADII {
        for (tag, frac) in [("m = 5 (perfect agreement)", 0.0), ("m = 5 + 0.3 r (primary)", M_FRAC), ("m = 5 + 0.6 r (loosest agreement the test accepts)", 0.6)] {
            let m = drift(r, frac);
            let g = dome(&world, r, m);
            writeln!(report, "\n### r = {r} m, {tag}: m = {m:.1} m\n").unwrap();
            report += &stats(&world, &g, ceil);
            if frac == M_FRAC {
                let name = format!("{out}/dome_r{}", r as i64);
                let head = format!(
                    "{{\"file\":\"dome_r{r}.f32\",\"dtype\":\"float32\",\"endian\":\"little\",\"order\":\"row-major, index j*nx+i, y up (north)\",\"origin\":[{o},{o}],\"spacing\":{STEP},\"nx\":{N},\"ny\":{N},\"x_of_i\":\"origin[0]+i*spacing\",\"y_of_j\":\"origin[1]+j*spacing\",\"r\":{r},\"m\":{m},\"r_body\":{R_BODY},\"margin\":{MARGIN},\"z_top\":{ceil},\"units\":\"metres, world frame (same z as the raw raster and the recorded frames)\",\"meaning\":\"least altitude at which the gate's circle test passes for a circle of radius r centred here\"}}\n",
                    o = -MAP_HALF
                );
                write_grid(&name, &g, &head);
                let agl: Vec<f32> = (0..N * N).map(|k| g[k] - world.terrain(-MAP_HALF + STEP * (k % N) as f64, -MAP_HALF + STEP * (k / N) as f64) as f32).collect();
                let amax = 500.0;
                // ceiling cells are white in both views
                let ceil_agl: Vec<f32> = (0..N * N).map(|k| if g[k] >= ceil - 1e-3 { 1.0e4 } else { agl[k] }).collect();
                render(&world, &g, ceil, MAP_HALF, STEP / 2.0, ((ceil as f64 / 200.0).ceil() * 200.0).max(ceil as f64), true, &format!("{name}_map.png"));
                render(&world, &g, ceil, 1300.0, 2.5, (ceil as f64 / 200.0).ceil() * 200.0, true, &format!("{name}_city.png"));
                render(&world, &ceil_agl, 9999.0, MAP_HALF, STEP / 2.0, amax, false, &format!("{name}_agl_map.png"));
                render(&world, &ceil_agl, 9999.0, 1300.0, 2.5, amax, false, &format!("{name}_agl_city.png"));
                let gap: Vec<(f64, f64)> = (-15..=10).map(|k| (-120.0, k as f64 * 10.0)).collect();
                let canyon: Vec<(f64, f64)> = (-47..=60).map(|k| (k as f64 * 10.0, 120.0)).collect();
                let at = |x: f64, y: f64| line_stats(&world, &g, &[(x, y)]);
                writeln!(report, "\nTower gap street x = -120, y from -150 to 100: {}; at (-120, -60) (the showcase start): {}", line_stats(&world, &g, &gap), at(-120.0, -60.0)).unwrap();
                writeln!(report, "Canyon slice y = 120, x from -470 to 600: {}; at (-470, 120): {}", line_stats(&world, &g, &canyon), at(-470.0, 120.0)).unwrap();
                // check against the real helix_check
                let mut rng = Rng::new(7 + r as u64);
                let (mut bad, mut tight) = (0, 0);
                for _ in 0..nchk {
                    let (i, j) = ((rng.f() * (N - 1) as f64) as usize, (rng.f() * (N - 1) as f64) as usize);
                    let c = [-MAP_HALF + STEP * i as f64, -MAP_HALF + STEP * j as f64];
                    let d = g[j * N + i] as f64;
                    let pass = |z: f64| helix_check(&world, c, r, m, z, top(&world), MARGIN).is_ok();
                    if !pass(d + 1e-3) {
                        bad += 1;
                    }
                    if d < ceil as f64 - 1e-3 && pass(d - 1e-2) {
                        bad += 1;
                    }
                    tight += (d < ceil as f64 - 1e-3) as usize;
                }
                writeln!(report, "check: {nchk} random centres against helix_check, {tight} below the ceiling, {bad} disagreements").unwrap();
                assert_eq!(bad, 0, "dome disagrees with helix_check");
            }
        }
    }
    fs::write(format!("{out}/dome_stats.md"), &report).unwrap();
    println!("{report}");
}
