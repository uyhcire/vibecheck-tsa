//! Albedo: sRGB + occlusion in A. Mask: asphalt, grass, rock weights (concrete = rest).

use cityflight::world::*;

pub const TEX: usize = 4096;

fn hash01(x: i64, y: i64) -> f64 {
    let mut r = Rng::new((x as u64).wrapping_mul(0x9E37_79B1) ^ (y as u64).wrapping_mul(0x85EB_CA77));
    r.f()
}

fn smooth_noise(x: f64, y: f64) -> f64 {
    let (ix, iy) = (x.floor(), y.floor());
    let (fx, fy) = (x - ix, y - iy);
    let (ux, uy) = (fx * fx * (3.0 - 2.0 * fx), fy * fy * (3.0 - 2.0 * fy));
    let h = |a: f64, b: f64| hash01(a as i64, b as i64);
    let a = h(ix, iy) + (h(ix + 1.0, iy) - h(ix, iy)) * ux;
    let b = h(ix, iy + 1.0) + (h(ix + 1.0, iy + 1.0) - h(ix, iy + 1.0)) * ux;
    a + (b - a) * uy
}

fn mix3(a: [f64; 3], b: [f64; 3], t: f64) -> [f64; 3] {
    [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]
}

struct Texel {
    col: [f64; 3],
    asphalt: f64,
    grass: f64,
    rock: f64,
}

fn ground(w: &World, x: f64, y: f64) -> Texel {
    let h = w.terrain(x, y);
    let gx = w.terrain(x + 5.0, y) - w.terrain(x - 5.0, y);
    let gy = w.terrain(x, y + 5.0) - w.terrain(x, y - 5.0);
    let slope = (gx * gx + gy * gy).sqrt() / 10.0;
    let speck = smooth_noise(x / 6.0, y / 6.0) * 0.6 + smooth_noise(x / 1.7 + 31.0, y / 1.7) * 0.4;
    let big = 0.5 + 0.5 * ((x * 0.0021 + (y * 0.0017).sin() * 2.0).sin() * (y * 0.0013 + (x * 0.0019).cos()).cos());
    let grass_c = mix3([0.31, 0.45, 0.22], [0.44, 0.50, 0.27], 0.6 * big + 0.4 * speck);
    let dry = smoothstep(140.0, 340.0, h);
    let mut c = mix3(grass_c, [0.55, 0.52, 0.37], dry);
    let rock = smoothstep(0.45, 0.85, slope).max(smoothstep(540.0, 660.0, h));
    c = mix3(c, mix3([0.46, 0.44, 0.42], [0.56, 0.54, 0.51], speck), rock);
    let snow = smoothstep(770.0, 840.0, h) * (1.0 - smoothstep(0.9, 1.4, slope));
    c = mix3(c, [0.93, 0.94, 0.97], snow);
    let mut t = Texel { col: c, asphalt: 0.0, grass: (1.0 - rock) * (1.0 - snow), rock: rock.max(snow) };
    let lim = CITY_HALF + 22.0;
    if x.abs() < lim && y.abs() < lim {
        let street = |v: f64| -> (f64, f64, f64) {
            let k = ((v + CITY_HALF) / STREET_PITCH).round().clamp(0.0, 20.0) as usize;
            let d = (v - street_x(k)).abs();
            (d, w.street_w[k], if k % 5 == 0 { 1.0 } else { 0.0 })
        };
        let (dx, wx, ax) = street(x);
        let (dy, wy, ay) = street(y);
        let in_x = dx <= wx / 2.0 && y.abs() <= CITY_HALF + wy / 2.0;
        let in_y = dy <= wy / 2.0 && x.abs() <= CITY_HALF + wx / 2.0;
        if in_x || in_y {
            t = Texel { col: mix3([0.21, 0.21, 0.23], [0.26, 0.26, 0.28], speck * 0.5), asphalt: 1.0, grass: 0.0, rock: 0.0 };
            let (d, ww, art, along) = if in_x && !in_y { (dx, wx, ax, y) } else if in_y && !in_x { (dy, wy, ay, x) } else { (99.0, 0.0, 0.0, 0.0) };
            if d < 99.0 {
                if d > ww / 2.0 - 3.0 {
                    t = Texel { col: [0.62, 0.61, 0.58], asphalt: 0.0, grass: 0.0, rock: 0.0 };
                } else if d < 0.35 && (along / 9.0).rem_euclid(1.0) < 0.55 {
                    t.col = if art > 0.5 { [0.86, 0.74, 0.28] } else { [0.85, 0.85, 0.82] };
                }
            }
        } else if x.abs() <= CITY_HALF && y.abs() <= CITY_HALF {
            if w.is_park(x, y) {
                t = Texel { col: mix3([0.29, 0.47, 0.23], [0.35, 0.52, 0.27], speck), asphalt: 0.0, grass: 1.0, rock: 0.0 };
                let (ix, iy) = ((x / 11.0).floor() as i64, (y / 11.0).floor() as i64);
                let cx = (ix as f64 + 0.2 + 0.6 * hash01(ix, iy * 7 + 3)) * 11.0;
                let cy = (iy as f64 + 0.2 + 0.6 * hash01(ix * 5 + 1, iy)) * 11.0;
                if ((x - cx).powi(2) + (y - cy).powi(2)).sqrt() < 3.6 && hash01(ix * 3, iy * 3) < 0.7 {
                    t.col = [0.16, 0.32, 0.15];
                }
            } else {
                t = Texel { col: mix3([0.46, 0.45, 0.42], [0.56, 0.55, 0.52], speck), asphalt: 0.0, grass: 0.0, rock: 0.0 };
            }
        }
    }
    t
}

fn occlusion(w: &World, x: f64, y: f64, h: f64) -> f64 {
    if x.abs() >= CITY_HALF + 30.0 || y.abs() >= CITY_HALF + 30.0 {
        return 1.0;
    }
    let mut occ = 0.0;
    for k in 0..8 {
        let a = k as f64 * std::f64::consts::FRAC_PI_4;
        let (dx, dy) = (a.cos(), a.sin());
        let mut best: f64 = 0.0;
        for d in [1.5, 3.5, 7.0, 14.0, 28.0] {
            let hz = w.surface(x + dx * d, y + dy * d) - h;
            if hz > 0.0 {
                best = best.max(hz / (hz * hz + d * d).sqrt());
            }
        }
        occ += best;
    }
    1.0 - 0.85 * occ / 8.0
}

pub fn bake(w: &World) -> (Vec<u8>, Vec<u8>) {
    let mut alb = vec![0u8; TEX * TEX * 4];
    let mut mask = vec![0u8; TEX * TEX * 4];
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let rows_per = TEX.div_ceil(threads);
    let to8 = |v: f64| (v.clamp(0.0, 1.0) * 255.0 + 0.5) as u8;
    std::thread::scope(|sc| {
        for (ci, (ca, cm)) in alb.chunks_mut(rows_per * TEX * 4).zip(mask.chunks_mut(rows_per * TEX * 4)).enumerate() {
            sc.spawn(move || {
                for (ri, (ra, rm)) in ca.chunks_mut(TEX * 4).zip(cm.chunks_mut(TEX * 4)).enumerate() {
                    let py = ci * rows_per + ri;
                    let y = -GRID_HALF + (py as f64 + 0.5) * 2.0 * GRID_HALF / TEX as f64;
                    for i in 0..TEX {
                        let x = -GRID_HALF + (i as f64 + 0.5) * 2.0 * GRID_HALF / TEX as f64;
                        let t = ground(w, x, y);
                        let h = w.terrain(x, y);
                        ra[i * 4] = to8(t.col[0]);
                        ra[i * 4 + 1] = to8(t.col[1]);
                        ra[i * 4 + 2] = to8(t.col[2]);
                        ra[i * 4 + 3] = to8(occlusion(w, x, y, h));
                        rm[i * 4] = to8(t.asphalt);
                        rm[i * 4 + 1] = to8(t.grass);
                        rm[i * 4 + 2] = to8(t.rock);
                        rm[i * 4 + 3] = 255;
                    }
                }
            });
        }
    });
    (alb, mask)
}
