//! Backup-CBF City Flight: the interactive demo.
//!
//! Static geometry (terrain, buildings: ~2k boxes in the grid city, ~41k
//! prisms in San Francisco) lives in immutable GPU buffers drawn through raw
//! miniquad with one shader: a per-pixel sky, linear lighting with a filmic
//! tone map, glass and water that reflect the sky, and aerial perspective.
//! Dynamic things (aircraft, escape paths, trail, HUD) go through macroquad.
//! The simulation and the safety filter come from the library, the same code
//! the headless harness runs. Tab switches maps; each loads once.

use cityflight::escape::*;
use cityflight::filter::*;
use cityflight::harness::*;
use cityflight::model::*;
use cityflight::pilot::*;
use cityflight::sim::*;
use cityflight::world::*;
use macroquad::camera::Camera as _;
use macroquad::miniquad as mq;
use macroquad::prelude::*;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

const SUN: [f32; 3] = [-0.45, -0.55, 0.70];
const SF_SUN: [f32; 3] = [0.40, -0.50, 0.77];
const FOG: [f32; 3] = [0.70, 0.79, 0.90];
const TEX: usize = 4096;

fn window_conf() -> Conf {
    Conf {
        window_title: "Backup-CBF City Flight".to_owned(),
        window_width: 1440,
        window_height: 900,
        high_dpi: true,
        sample_count: 4,
        window_resizable: true,
        ..Default::default()
    }
}

fn sun_n() -> Vec3 {
    vec3(SUN[0], SUN[1], SUN[2]).normalize()
}

/// Sun direction per map. San Francisco's matches the aerial photo's shadows
/// (late morning), so baked photo shadows and our lighting agree.
fn sun_for(map: MapId) -> Vec3 {
    match map {
        MapId::Grid => sun_n(),
        MapId::SanFrancisco => vec3(SF_SUN[0], SF_SUN[1], SF_SUN[2]).normalize(),
    }
}

// ------------------------------------------------------------------ static scene

#[repr(C)]
#[derive(Clone, Copy)]
struct SV {
    pos: [f32; 3],
    nrm: [f32; 3],
    col: [f32; 3],
    uv: [f32; 2],
    win: f32,
}

#[repr(C)]
struct SU {
    mvp: [f32; 16],
    cam: [f32; 3],
    sun: [f32; 3],
    fog: [f32; 3],
    dens: f32,
    water_z: f32,
    time: f32,
}

#[repr(C)]
struct SkyU {
    ivp: [f32; 16],
    cam: [f32; 3],
    sun: [f32; 3],
    fog: [f32; 3],
}

/// Material ids, passed per vertex (`SV::win`).
const MAT_GROUND: f32 = 0.0;
const MAT_WALL: f32 = 1.0;
const MAT_ROOF_PHOTO: f32 = 2.0;
const MAT_ROOF: f32 = 3.0;
const MAT_PLAIN: f32 = 4.0;
const MAT_GLASS: f32 = 5.0;
/// See-through safety envelope (drawn last, blended).
const MAT_ENV: f32 = 6.0;

struct StaticScene {
    pipe: mq::Pipeline,
    sky_pipe: mq::Pipeline,
    sky: mq::Bindings,
    terr: mq::Bindings,
    terr_n: i32,
    bld: mq::Bindings,
    bld_n: i32,
    env_pipe: mq::Pipeline,
    env: mq::Bindings,
    env_n: i32,
    sun: Vec3,
    water_z: f32,
}

/// Shared shader code: sky radiance (linear), filmic tone map.
const SKY_GLSL: &str = r#"
vec3 lin(vec3 c) { return c * c; }
vec3 sky(vec3 d, vec3 sun, vec3 fog) {
    vec3 hor = lin(fog) * 0.92;
    vec3 zen = vec3(0.035, 0.13, 0.46);
    vec3 c = mix(hor, zen, pow(clamp(d.z, 0.0, 1.0), 0.5));
    if (d.z < 0.0) c = hor * (1.0 - 0.2 * min(-d.z * 4.0, 1.0));
    float s = max(dot(d, sun), 0.0);
    c += vec3(1.0, 0.80, 0.55) * (0.16 * pow(s, 6.0) + 0.35 * pow(s, 64.0));
    return c;
}
vec3 tonemap(vec3 x) {
    x *= 1.1;
    return clamp((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14), 0.0, 1.0);
}
"#;

const VS: &str = r#"#version 100
attribute vec3 in_pos;
attribute vec3 in_nrm;
attribute vec3 in_col;
attribute vec2 in_uv;
attribute float in_win;
uniform mat4 mvp;
varying highp vec3 v_pos;
varying mediump vec3 v_nrm;
varying mediump vec3 v_col;
varying highp vec2 v_uv;
varying mediump float v_win;
void main() {
    gl_Position = mvp * vec4(in_pos, 1.0);
    v_pos = in_pos; v_nrm = in_nrm; v_col = in_col; v_uv = in_uv; v_win = in_win;
}"#;

/// Scene shader. Materials (`v_win`): 0 ground (texture), 1 wall with
/// punched windows, 2 roof from the aerial photo, 3 plain roof, 4 plain wall,
/// 5 glass curtain wall. Walls carry (distance along the footprint, height
/// above the base) in `v_uv`. Lighting is linear with a filmic tone map;
/// glass and water reflect the sky; distance fades into the sky colour in
/// that direction (aerial perspective, thinner with height).
const FS_MAIN: &str = r#"
uniform sampler2D tex;
uniform mat4 mvp;
uniform vec3 cam;
uniform vec3 sun;
uniform vec3 fog;
uniform float dens;
uniform float water_z;
uniform float time;
varying highp vec3 v_pos;
varying mediump vec3 v_nrm;
varying mediump vec3 v_col;
varying highp vec2 v_uv;
varying mediump float v_win;
float hash(vec2 p) { return fract(sin(dot(p, vec2(127.1, 311.7))) * 43758.5453); }
// 1 on [a, b] of a period (x in 0..1), edges blurred over `fw` periods.
float pulse(float x, float a, float b, float fw) {
    fw = max(fw, 1e-3);
    return smoothstep(a - fw, a + fw, x) - smoothstep(b - fw, b + fw, x);
}
void main() {
    vec3 n = normalize(v_nrm);
    vec3 vd = v_pos - cam;
    float d = length(vd);
    vec3 v = -vd / d;
    float mat = v_win;
    vec3 alb;
    if (mat < 0.5) alb = lin(texture2D(tex, v_uv).rgb) * lin(v_col);
    else if (mat < 2.5 && mat > 1.5) alb = lin(texture2D(tex, v_uv).rgb) * 1.05;
    else alb = lin(v_col);
    bool wall = (mat > 0.5 && mat < 1.5) || mat > 4.5;
    float ao = 1.0;
    if (wall || (mat > 3.5 && mat < 4.5)) ao = 0.5 + 0.5 * smoothstep(0.0, 14.0, v_uv.y);
    float gloss = 0.0;
    float tint = 1.0;
    // Facades: window stripes filtered over the pixel's footprint on the
    // wall (it grows with distance), fading to their average far away.
    if (wall && abs(n.z) < 0.5) {
        float s = v_uv.x;
        float hb = v_uv.y;
        float px = d * 0.0007;
        float fl = fract(hb / 3.6);
        float ff = px / 3.6;
        float w;
        float mean;
        if (mat > 4.5) {
            float cl = fract(s / 1.55);
            float fc = px / 1.55;
            w = pulse(cl, 0.05, 0.95, fc) * pulse(fl, 0.24, 1.0, ff);
            mean = 0.68;
            w = mix(w, mean, smoothstep(0.12, 0.45, max(fc, ff)));
            alb *= 0.55;
        } else {
            float cl = fract(s / 3.1);
            float fc = px / 3.1;
            if (hb < 4.2) {
                w = pulse(hb / 4.2, 0.12, 0.86, px / 4.2) * pulse(cl, 0.06, 0.94, fc);
                mean = 0.65;
            } else {
                w = pulse(fl, 0.30, 0.86, ff) * pulse(cl, 0.18, 0.82, fc);
                mean = 0.36;
            }
            w = mix(w, mean, smoothstep(0.12, 0.45, max(fc, ff)));
        }
        gloss = w;
        tint = 0.85 + 0.3 * hash(vec2(floor(hb / 3.6), floor(s / 3.1)));
    }
    float diff = max(dot(n, sun), 0.0);
    vec3 sunc = vec3(1.0, 0.93, 0.82) * 2.0;
    vec3 amb = mix(vec3(0.09, 0.085, 0.08), vec3(0.17, 0.23, 0.36), 0.5 + 0.5 * n.z);
    vec3 col = alb * (amb * ao + sunc * diff * (0.55 + 0.45 * ao));
    if (gloss > 0.0) {
        vec3 r = reflect(-v, n);
        float fres = 0.05 + 0.95 * pow(1.0 - max(dot(n, v), 0.0), 5.0);
        vec3 rc = r.z > 0.0 ? sky(r, sun, fog) : lin(vec3(0.30, 0.30, 0.31)) * (amb + sunc * 0.3);
        vec3 glass = lin(vec3(0.06, 0.09, 0.12)) * (amb + sunc * diff * 0.3) + rc * fres * tint;
        glass += sunc * pow(max(dot(r, sun), 0.0), 300.0) * 1.5;
        col = mix(col, glass, gloss * 0.9);
    }
    if (mat < 0.5 && v_pos.z <= water_z + 0.05) {
        // Sum of a few travelling waves in different directions, calming
        // with distance (no visible repetition far out).
        vec2 p = v_pos.xy;
        vec2 g = vec2(0.0);
        vec2 k1 = vec2(0.093, 0.041); g += 0.45 * k1 * cos(dot(p, k1) + time * 1.3);
        vec2 k2 = vec2(-0.061, 0.137); g += 0.35 * k2 * cos(dot(p, k2) - time * 1.7);
        vec2 k3 = vec2(0.211, -0.173); g += 0.16 * k3 * cos(dot(p, k3) + time * 2.3);
        vec2 k4 = vec2(0.317, 0.289); g += 0.10 * k4 * cos(dot(p, k4) - time * 2.9);
        vec2 k5 = vec2(-0.53, 0.47); g += 0.05 * k5 * cos(dot(p, k5) + time * 3.7);
        vec3 wn = normalize(vec3(-0.6 * g * (1.0 - smoothstep(200.0, 2500.0, d)), 1.0));
        vec3 r = reflect(-v, wn);
        float fres = 0.02 + 0.98 * pow(1.0 - max(dot(wn, v), 0.0), 5.0);
        vec3 deep = alb * (amb + sunc * 0.35);
        col = mix(deep, sky(r, sun, fog), fres) + sunc * pow(max(dot(r, sun), 0.0), 500.0) * 2.5;
    }
    float hz = max(0.5 * (cam.z + v_pos.z), 0.0);
    float f = 1.0 - exp(-d * dens * exp(-hz / 900.0));
    col = mix(col, sky(-v, sun, fog), clamp(f, 0.0, 1.0));
    float alpha = mat > 5.5 ? 0.07 + 0.25 * pow(1.0 - abs(dot(n, v)), 2.0) : 1.0;
    gl_FragColor = vec4(sqrt(tonemap(col)), alpha);
}"#;

const SKY_VS: &str = r#"#version 100
attribute vec2 in_pos;
varying highp vec2 v_ndc;
void main() {
    gl_Position = vec4(in_pos, 0.0, 1.0);
    v_ndc = in_pos;
}"#;

const FS_SKY: &str = r#"
uniform mat4 ivp;
uniform vec3 cam;
uniform vec3 sun;
uniform vec3 fog;
varying highp vec2 v_ndc;
void main() {
    vec4 p = ivp * vec4(v_ndc, 1.0, 1.0);
    vec3 d = normalize(p.xyz / p.w - cam);
    vec3 c = sky(d, sun, fog);
    c += vec3(1.0, 0.92, 0.75) * 40.0 * smoothstep(0.99990, 0.99996, dot(d, sun));
    gl_FragColor = vec4(sqrt(tonemap(c)), 1.0);
}"#;

fn frag(body: &str) -> String {
    format!("#version 100\nprecision highp float;\n{SKY_GLSL}\n{body}")
}

fn hash01(x: i64, y: i64) -> f64 {
    let mut r = Rng::new((x as u64).wrapping_mul(0x9E37_79B1) ^ (y as u64).wrapping_mul(0x85EB_CA77));
    r.f()
}

fn mix3(a: [f64; 3], b: [f64; 3], t: f64) -> [f64; 3] {
    [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]
}

/// Albedo of the ground at (x, y), with static sun shadows from buildings.
fn ground_color(w: &World, x: f64, y: f64) -> [f64; 3] {
    let h = w.terrain(x, y);
    let gx = w.terrain(x + 5.0, y) - w.terrain(x - 5.0, y);
    let gy = w.terrain(x, y + 5.0) - w.terrain(x, y - 5.0);
    let slope = (gx * gx + gy * gy).sqrt() / 10.0;
    let speck = hash01((x / 6.0).floor() as i64, (y / 6.0).floor() as i64);
    let big = 0.5 + 0.5 * ((x * 0.0021 + (y * 0.0017).sin() * 2.0).sin() * (y * 0.0013 + (x * 0.0019).cos()).cos());
    let grass = mix3([0.31, 0.45, 0.22], [0.44, 0.50, 0.27], 0.6 * big + 0.4 * speck);
    let mut c = mix3(grass, [0.55, 0.52, 0.37], smoothstep(140.0, 340.0, h));
    let rock = smoothstep(0.45, 0.85, slope).max(smoothstep(540.0, 660.0, h));
    c = mix3(c, mix3([0.46, 0.44, 0.42], [0.56, 0.54, 0.51], speck), rock);
    let snow = smoothstep(770.0, 840.0, h) * (1.0 - smoothstep(0.9, 1.4, slope));
    c = mix3(c, [0.93, 0.94, 0.97], snow);
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
            c = mix3([0.21, 0.21, 0.23], [0.26, 0.26, 0.28], speck * 0.5);
            let (d, ww, art, along) = if in_x && !in_y { (dx, wx, ax, y) } else if in_y && !in_x { (dy, wy, ay, x) } else { (99.0, 0.0, 0.0, 0.0) };
            if d < 99.0 {
                if d > ww / 2.0 - 3.0 {
                    c = [0.62, 0.61, 0.58];
                } else if d < 0.35 && (along / 9.0).rem_euclid(1.0) < 0.55 {
                    c = if art > 0.5 { [0.86, 0.74, 0.28] } else { [0.85, 0.85, 0.82] };
                }
            }
        } else if x.abs() <= CITY_HALF && y.abs() <= CITY_HALF {
            if w.is_park(x, y) {
                c = mix3([0.29, 0.47, 0.23], [0.35, 0.52, 0.27], speck);
                let (ix, iy) = ((x / 11.0).floor() as i64, (y / 11.0).floor() as i64);
                let cx = (ix as f64 + 0.2 + 0.6 * hash01(ix, iy * 7 + 3)) * 11.0;
                let cy = (iy as f64 + 0.2 + 0.6 * hash01(ix * 5 + 1, iy)) * 11.0;
                if ((x - cx).powi(2) + (y - cy).powi(2)).sqrt() < 3.6 && hash01(ix * 3, iy * 3) < 0.7 {
                    c = [0.16, 0.32, 0.15];
                }
            } else {
                c = mix3([0.58, 0.56, 0.52], [0.66, 0.64, 0.60], speck);
            }
        }
    }
    // Sun shadows cast by buildings onto the ground.
    if x.abs() < 1450.0 && y.abs() < 1450.0 {
        let s = sun_n();
        let hl = ((s.x * s.x + s.y * s.y) as f64).sqrt();
        let (sx, sy, te) = (s.x as f64 / hl, s.y as f64 / hl, s.z as f64 / hl);
        let mut t = 3.0;
        while t < 600.0 {
            let hz = h + t * te;
            if hz > 470.0 {
                break;
            }
            if w.surface(x + sx * t, y + sy * t) > hz + 0.3 {
                c = [c[0] * 0.52, c[1] * 0.55, c[2] * 0.62];
                break;
            }
            t += 3.0;
        }
    }
    c
}

/// San Francisco streets rasterised at texture resolution: 0 none,
/// 1 sidewalk edge, 2 asphalt, 3 centre line (busier streets).
fn street_mask(w: &World) -> Vec<u8> {
    let mut m = vec![0u8; TEX * TEX];
    let px = 2.0 * MAP_HALF / TEX as f64;
    for st in w.streets.iter().filter(|s| !s.bridge) {
        let hw = [11.0, 10.0, 9.0, 8.0, 7.0, 5.5, 5.5, 4.0, 4.0, 4.0, 4.0][st.class as usize];
        let walk = st.class >= 2 && st.class <= 6;
        let line = st.class <= 3;
        for seg in st.pts.windows(2) {
            let (a, b) = (seg[0], seg[1]);
            let (dx, dy) = (b[0] - a[0], b[1] - a[1]);
            let l2 = (dx * dx + dy * dy).max(1e-9);
            let ti = |v: f64| (((v + MAP_HALF) / px).floor().max(0.0) as usize).min(TEX - 1);
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
                    // Where streets overlap, asphalt beats a centre line beats
                    // a sidewalk (no lines painted through intersections).
                    let rank = |c: u8| [0, 1, 3, 2][c as usize];
                    let c = &mut m[j * TEX + i];
                    if rank(code) > rank(*c) {
                        *c = code;
                    }
                }
            }
        }
    }
    m
}

/// San Francisco ground: bay water, paved lots, OSM streets, sun shadows
/// from the buildings.
fn ground_color_sf(w: &World, street: u8, x: f64, y: f64) -> [f64; 3] {
    let h = w.terrain(x, y);
    let speck = hash01((x / 6.0).floor() as i64, (y / 6.0).floor() as i64);
    if h <= SF_WATER + 0.05 {
        let ripple = 0.5 + 0.5 * ((x * 0.013 + y * 0.007).sin() * (y * 0.011 - x * 0.005).cos());
        return mix3([0.12, 0.26, 0.35], [0.16, 0.32, 0.41], 0.6 * ripple + 0.4 * speck);
    }
    let mut c = match street {
        1 => [0.62, 0.61, 0.58],
        2 => mix3([0.21, 0.21, 0.23], [0.26, 0.26, 0.28], speck * 0.5),
        3 => [0.85, 0.85, 0.82],
        _ => mix3([0.54, 0.53, 0.49], [0.62, 0.61, 0.57], speck),
    };
    let s = sun_for(MapId::SanFrancisco);
    let hl = ((s.x * s.x + s.y * s.y) as f64).sqrt();
    let (sx, sy, te) = (s.x as f64 / hl, s.y as f64 / hl, s.z as f64 / hl);
    let mut t = 3.0;
    while t < 600.0 {
        let hz = h + t * te;
        if hz > 340.0 {
            break;
        }
        if w.surface(x + sx * t, y + sy * t) > hz + 0.3 {
            c = [c[0] * 0.52, c[1] * 0.55, c[2] * 0.62];
            break;
        }
        t += 3.0;
    }
    c
}

fn terrain_texture(w: &World) -> Vec<u8> {
    let mask = if w.map == MapId::SanFrancisco { street_mask(w) } else { Vec::new() };
    let mask = &mask;
    let mut px = vec![0u8; TEX * TEX * 4];
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let rows_per = TEX.div_ceil(threads);
    std::thread::scope(|sc| {
        for (ci, chunk) in px.chunks_mut(rows_per * TEX * 4).enumerate() {
            sc.spawn(move || {
                for (ri, row) in chunk.chunks_mut(TEX * 4).enumerate() {
                    let py = ci * rows_per + ri;
                    let y = -MAP_HALF + (py as f64 + 0.5) * 2.0 * MAP_HALF / TEX as f64;
                    for i in 0..TEX {
                        let x = -MAP_HALF + (i as f64 + 0.5) * 2.0 * MAP_HALF / TEX as f64;
                        let c = if w.map == MapId::SanFrancisco { ground_color_sf(w, mask[py * TEX + i], x, y) } else { ground_color(w, x, y) };
                        row[i * 4] = (c[0].clamp(0.0, 1.0) * 255.0) as u8;
                        row[i * 4 + 1] = (c[1].clamp(0.0, 1.0) * 255.0) as u8;
                        row[i * 4 + 2] = (c[2].clamp(0.0, 1.0) * 255.0) as u8;
                        row[i * 4 + 3] = 255;
                    }
                }
            });
        }
    });
    px
}

fn building_color(b: &Building) -> [f32; 3] {
    match b.kind {
        Kind::Bridge => return [0.62, 0.78, 0.95],
        Kind::BridgeTower => return [0.62, 0.65, 0.68],
        Kind::Viaduct => return [0.63, 0.62, 0.59],
        Kind::Building => {}
    }
    let t = b.tint;
    let tall = b.z1 - b.z0 > 70.0;
    let pal_tall = [[0.50, 0.58, 0.67], [0.40, 0.46, 0.53], [0.66, 0.70, 0.74], [0.56, 0.62, 0.58]];
    let pal_low = [[0.76, 0.73, 0.68], [0.64, 0.46, 0.38], [0.84, 0.81, 0.74], [0.70, 0.66, 0.58], [0.58, 0.60, 0.62]];
    if tall {
        pal_tall[((t * 3.999) as usize).min(3)]
    } else {
        pal_low[((t * 4.999) as usize).min(4)]
    }
}

/// Push a vertical quad from `p` to `q` (ground track), `z0..z1`.
fn push_quad(v: &mut Vec<SV>, i: &mut Vec<u32>, p: [f64; 2], q: [f64; 2], z: [f32; 4], col: [f32; 3], mat: f32) {
    let (ex, ey) = ((q[0] - p[0]) as f32, (q[1] - p[1]) as f32);
    let l = (ex * ex + ey * ey).sqrt().max(1e-4);
    let nrm = [ey / l, -ex / l, 0.0];
    let (px, py, qx, qy) = (p[0] as f32, p[1] as f32, q[0] as f32, q[1] as f32);
    let k = v.len() as u32;
    for (pos, h) in [([px, py, z[0]], 0.0), ([qx, qy, z[1]], 0.0), ([qx, qy, z[3]], 1.0), ([px, py, z[2]], 1.0)] {
        v.push(SV { pos, nrm, col, uv: [0.0, h * 50.0], win: mat });
    }
    i.extend_from_slice(&[k, k + 1, k + 2, k, k + 2, k + 3]);
}

/// The Bay Bridge as it looks: a deck, two main cables and suspenders
/// (pushed into the opaque mesh), plus its collision curtain as a faint
/// see-through envelope (returned). The curtain pieces are ordered along
/// the bridge; the cable runs through each piece's top.
fn bridge_meshes(w: &World, bv: &mut Vec<SV>, bi: &mut Vec<u32>) -> (Vec<SV>, Vec<u32>) {
    let (mut ev, mut ei) = (Vec::new(), Vec::new());
    let pieces: Vec<&Building> = w.boxes.iter().filter(|b| b.kind == Kind::Bridge).collect();
    if pieces.len() < 2 {
        return (ev, ei);
    }
    let cen: Vec<[f64; 2]> = pieces
        .iter()
        .map(|b| {
            let o = w.outline(b);
            let n = o.len() as f64;
            [o.iter().map(|q| q[0]).sum::<f64>() / n, o.iter().map(|q| q[1]).sum::<f64>() / n]
        })
        .collect();
    let m = cen.len() as f64;
    let (cx, cy) = (cen.iter().map(|c| c[0]).sum::<f64>() / m, cen.iter().map(|c| c[1]).sum::<f64>() / m);
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
    let steel = [0.55, 0.58, 0.62];
    let deck_col = [0.42, 0.43, 0.45];
    // Per piece: centre, half-width across the bridge, cable and deck height.
    let info: Vec<([f64; 2], f64, f32, f32)> = order
        .iter()
        .map(|&k| {
            let b = pieces[k];
            let c = cen[k];
            let hw = w.outline(b).iter().map(|q| ((q[0] - c[0]) * nx + (q[1] - c[1]) * ny).abs()).fold(0.0, f64::max);
            let cable = (b.z1 - 1.0) as f32;
            let deck = ((b.z1 - 8.0).min(66.0)).max(w.terrain(c[0], c[1]) + 6.0) as f32;
            (c, hw, cable, deck)
        })
        .collect();
    for (k, &idx) in order.iter().enumerate() {
        let b = pieces[idx];
        let (c, hw, cable, deck) = info[k];
        // Deck slab: the piece's footprint, 7 m deep.
        let o = w.outline(b);
        let n = o.len();
        for e in 0..n {
            push_quad(bv, bi, o[e], o[(e + 1) % n], [deck - 7.0, deck - 7.0, deck, deck], deck_col, MAT_PLAIN);
        }
        let i0 = bv.len() as u32;
        for q in &o {
            bv.push(SV { pos: [q[0] as f32, q[1] as f32, deck], nrm: [0.0, 0.0, 1.0], col: deck_col, uv: [0.5, 0.5], win: MAT_ROOF });
        }
        for t in 1..n.saturating_sub(1) as u32 {
            bi.extend_from_slice(&[i0, i0 + t, i0 + t + 1]);
        }
        // Envelope: the curtain piece itself, see-through. Walls across the
        // bridge are internal seams between pieces; only the two ends keep
        // theirs.
        let col = building_color(b);
        let (z0, z1) = (b.z0 as f32, b.z1 as f32);
        let end = k == 0 || k + 1 == order.len();
        for e in 0..n {
            let (a, q) = (o[e], o[(e + 1) % n]);
            let (dx, dy) = (q[0] - a[0], q[1] - a[1]);
            let across = ((dx * ux + dy * uy) / (dx * dx + dy * dy).sqrt().max(1e-9)).abs() < 0.5;
            if across && !end {
                continue;
            }
            push_quad(&mut ev, &mut ei, a, q, [z0, z0, z1, z1], col, MAT_ENV);
        }
        let i0 = ev.len() as u32;
        for q in &o {
            ev.push(SV { pos: [q[0] as f32, q[1] as f32, z1], nrm: [0.0, 0.0, 1.0], col, uv: [0.5, 0.5], win: MAT_ENV });
        }
        for t in 1..n.saturating_sub(1) as u32 {
            ei.extend_from_slice(&[i0, i0 + t, i0 + t + 1]);
        }
        for side in [-1.0, 1.0] {
            let off = side * (hw - 1.5).max(1.0);
            let p = [c[0] + nx * off, c[1] + ny * off];
            // Suspender from the deck up to the cable.
            if cable - deck > 4.0 {
                let p2 = [p[0] + ux * 0.4, p[1] + uy * 0.4];
                push_quad(bv, bi, p, p2, [deck, deck, cable, cable], steel, MAT_PLAIN);
            }
            // Main cable to the next piece.
            if let Some(&(c2, hw2, cable2, _)) = info.get(k + 1) {
                let off2 = side * (hw2 - 1.5).max(1.0);
                let q = [c2[0] + nx * off2, c2[1] + ny * off2];
                push_quad(bv, bi, p, q, [cable - 1.2, cable2 - 1.2, cable, cable2], steel, MAT_PLAIN);
            }
        }
    }
    (ev, ei)
}

/// San Francisco aerial photo (USDA NAIP via USGS, public domain), RGBA with
/// row 0 at the map's south edge; `None` if the file is missing.
fn sf_photo() -> Option<(Vec<u8>, usize)> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/data/sf/sf_naip.jpg");
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

impl StaticScene {
    fn new(w: &World) -> StaticScene {
        let InternalGlContext { quad_context: ctx, .. } = unsafe { get_internal_gl() };
        let uv_of = |x: f64, y: f64| [((x + MAP_HALF) / (2.0 * MAP_HALF)) as f32, ((y + MAP_HALF) / (2.0 * MAP_HALF)) as f32];
        // Terrain: same vertices and triangle split as the collision truth.
        let mut tv = Vec::with_capacity(TN * TN);
        for j in 0..TN {
            for i in 0..TN {
                let x = -MAP_HALF + i as f64 * TSP;
                let y = -MAP_HALF + j as f64 * TSP;
                let hh = |a: usize, b: usize| w.terr[b.min(TN - 1) * TN + a.min(TN - 1)];
                let dx = hh(i + 1, j) - hh(i.saturating_sub(1), j);
                let dy = hh(i, j + 1) - hh(i, j.saturating_sub(1));
                let n = vec3(-dx, -dy, 2.0 * TSP as f32).normalize();
                tv.push(SV { pos: [x as f32, y as f32, w.terr[j * TN + i]], nrm: [n.x, n.y, n.z], col: [1.0, 1.0, 1.0], uv: uv_of(x, y), win: MAT_GROUND });
            }
        }
        let mut ti: Vec<u32> = Vec::with_capacity((TN - 1) * (TN - 1) * 6);
        for j in 0..TN - 1 {
            for i in 0..TN - 1 {
                let a = (j * TN + i) as u32;
                let b = a + 1;
                let c = a + TN as u32 + 1;
                let d = a + TN as u32;
                ti.extend_from_slice(&[a, b, c, a, c, d]);
            }
        }
        // Ground texture: the aerial photo in San Francisco (if present),
        // else the painted one.
        let photo = if w.map == MapId::SanFrancisco { sf_photo() } else { None };
        let has_photo = photo.is_some();
        let (px, size) = photo.unwrap_or_else(|| (terrain_texture(w), TEX));
        let tex = ctx.new_texture(
            mq::TextureAccess::Static,
            mq::TextureSource::Bytes(&px),
            mq::TextureParams {
                format: mq::TextureFormat::RGBA8,
                wrap: mq::TextureWrap::Clamp,
                min_filter: mq::FilterMode::Linear,
                mag_filter: mq::FilterMode::Linear,
                mipmap_filter: mq::MipmapFilterMode::Linear,
                width: size as u32,
                height: size as u32,
                allocate_mipmaps: true,
                ..Default::default()
            },
        );
        ctx.texture_generate_mipmaps(tex);
        drop(px);

        // Buildings: a wall per footprint edge plus the roof (boxes are four
        // walls). Walls carry (distance along the outline, height above the
        // base) for the window grid; low roofs in San Francisco show the
        // aerial photo, which is the real roof.
        let mut bv: Vec<SV> = Vec::with_capacity(w.boxes.len() * 26);
        let mut bi: Vec<u32> = Vec::with_capacity(w.boxes.len() * 42);
        for b in &w.boxes {
            let col = building_color(b);
            let roof = [col[0] * 0.62 + 0.08, col[1] * 0.62 + 0.08, col[2] * 0.62 + 0.09];
            let base = b.z0 + 1.5;
            let height = b.z1 - base;
            if b.kind == Kind::Bridge {
                continue;
            }
            let (wall_mat, roof_mat) = match b.kind {
                Kind::Building if has_photo && height < 25.0 => (MAT_WALL, MAT_ROOF_PHOTO),
                Kind::Building if height > 60.0 => (MAT_GLASS, MAT_ROOF),
                Kind::Building => (MAT_WALL, MAT_ROOF),
                _ => (MAT_PLAIN, MAT_ROOF),
            };
            let poly = w.outline(b);
            let n = poly.len();
            let (z0, z1) = (b.z0 as f32, b.z1 as f32);
            let (h0, h1) = ((b.z0 - base) as f32, height as f32);
            let mut along = 0.0f32;
            for k in 0..n {
                let (p, q) = (poly[k], poly[(k + 1) % n]);
                let (ex, ey) = ((q[0] - p[0]) as f32, (q[1] - p[1]) as f32);
                let l = (ex * ex + ey * ey).sqrt();
                if l < 1e-4 {
                    continue;
                }
                let nrm = [ey / l, -ex / l, 0.0];
                let (px, py, qx, qy) = (p[0] as f32, p[1] as f32, q[0] as f32, q[1] as f32);
                let i0 = bv.len() as u32;
                for (pos, uv) in [
                    ([px, py, z0], [along, h0]),
                    ([qx, qy, z0], [along + l, h0]),
                    ([qx, qy, z1], [along + l, h1]),
                    ([px, py, z1], [along, h1]),
                ] {
                    bv.push(SV { pos, nrm, col, uv, win: wall_mat });
                }
                bi.extend_from_slice(&[i0, i0 + 1, i0 + 2, i0, i0 + 2, i0 + 3]);
                along += l;
            }
            let i0 = bv.len() as u32;
            let rc = if roof_mat == MAT_ROOF_PHOTO { [1.0, 1.0, 1.0] } else { roof };
            for p in &poly {
                bv.push(SV { pos: [p[0] as f32, p[1] as f32, z1], nrm: [0.0, 0.0, 1.0], col: rc, uv: uv_of(p[0], p[1]), win: roof_mat });
            }
            for k in 1..n.saturating_sub(1) as u32 {
                bi.extend_from_slice(&[i0, i0 + k, i0 + k + 1]);
            }
        }
        let (ev, ei) = bridge_meshes(w, &mut bv, &mut bi);
        let mk = |ctx: &mut dyn mq::RenderingBackend, v: &[SV], i: &[u32], img: mq::TextureId| mq::Bindings {
            vertex_buffers: vec![ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(v))],
            index_buffer: ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(i)),
            images: vec![img],
        };
        let terr = mk(ctx, &tv, &ti, tex);
        let bld = mk(ctx, &bv, &bi, tex);
        let env = mk(ctx, &ev, &ei, tex);
        let fs = frag(FS_MAIN);
        let shader = ctx
            .new_shader(
                mq::ShaderSource::Glsl { vertex: VS, fragment: &fs },
                mq::ShaderMeta {
                    images: vec!["tex".to_string()],
                    uniforms: mq::UniformBlockLayout {
                        uniforms: vec![
                            mq::UniformDesc::new("mvp", mq::UniformType::Mat4),
                            mq::UniformDesc::new("cam", mq::UniformType::Float3),
                            mq::UniformDesc::new("sun", mq::UniformType::Float3),
                            mq::UniformDesc::new("fog", mq::UniformType::Float3),
                            mq::UniformDesc::new("dens", mq::UniformType::Float1),
                            mq::UniformDesc::new("water_z", mq::UniformType::Float1),
                            mq::UniformDesc::new("time", mq::UniformType::Float1),
                        ],
                    },
                },
            )
            .expect("shader");
        let pipe = ctx.new_pipeline(
            &[mq::BufferLayout::default()],
            &[
                mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_nrm", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_col", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_uv", mq::VertexFormat::Float2),
                mq::VertexAttribute::new("in_win", mq::VertexFormat::Float1),
            ],
            shader,
            mq::PipelineParams { depth_test: mq::Comparison::LessOrEqual, depth_write: true, ..Default::default() },
        );
        let env_pipe = ctx.new_pipeline(
            &[mq::BufferLayout::default()],
            &[
                mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_nrm", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_col", mq::VertexFormat::Float3),
                mq::VertexAttribute::new("in_uv", mq::VertexFormat::Float2),
                mq::VertexAttribute::new("in_win", mq::VertexFormat::Float1),
            ],
            shader,
            mq::PipelineParams {
                depth_test: mq::Comparison::LessOrEqual,
                depth_write: false,
                color_blend: Some(mq::BlendState::new(
                    mq::Equation::Add,
                    mq::BlendFactor::Value(mq::BlendValue::SourceAlpha),
                    mq::BlendFactor::OneMinusValue(mq::BlendValue::SourceAlpha),
                )),
                ..Default::default()
            },
        );
        // Sky: one screen-covering triangle; each pixel looks up its view ray.
        let sky_fs = frag(FS_SKY);
        let sky_shader = ctx
            .new_shader(
                mq::ShaderSource::Glsl { vertex: SKY_VS, fragment: &sky_fs },
                mq::ShaderMeta {
                    images: vec![],
                    uniforms: mq::UniformBlockLayout {
                        uniforms: vec![
                            mq::UniformDesc::new("ivp", mq::UniformType::Mat4),
                            mq::UniformDesc::new("cam", mq::UniformType::Float3),
                            mq::UniformDesc::new("sun", mq::UniformType::Float3),
                            mq::UniformDesc::new("fog", mq::UniformType::Float3),
                        ],
                    },
                },
            )
            .expect("sky shader");
        let sky_pipe = ctx.new_pipeline(
            &[mq::BufferLayout::default()],
            &[mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float2)],
            sky_shader,
            mq::PipelineParams { depth_test: mq::Comparison::Always, depth_write: false, ..Default::default() },
        );
        let tri: [[f32; 2]; 3] = [[-1.0, -1.0], [3.0, -1.0], [-1.0, 3.0]];
        let sky = mq::Bindings {
            vertex_buffers: vec![ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(&tri))],
            index_buffer: ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(&[0u16, 1, 2])),
            images: vec![],
        };
        let water_z = if w.map == MapId::SanFrancisco { SF_WATER as f32 } else { -1.0e4 };
        StaticScene {
            pipe,
            sky_pipe,
            sky,
            terr,
            terr_n: ti.len() as i32,
            bld,
            bld_n: bi.len() as i32,
            env_pipe,
            env,
            env_n: ei.len() as i32,
            sun: sun_for(w.map),
            water_z,
        }
    }

    fn draw(&self, cam: &Camera3D) {
        let mut gl = unsafe { get_internal_gl() };
        gl.flush();
        let ctx = gl.quad_context;
        let vp = cam.matrix();
        let sky = SkyU { ivp: vp.inverse().to_cols_array(), cam: cam.position.to_array(), sun: self.sun.to_array(), fog: FOG };
        let u = SU {
            mvp: vp.to_cols_array(),
            cam: cam.position.to_array(),
            sun: self.sun.to_array(),
            fog: FOG,
            dens: 1.0 / 9000.0,
            water_z: self.water_z,
            time: get_time() as f32,
        };
        ctx.begin_default_pass(mq::PassAction::Nothing);
        ctx.apply_pipeline(&self.sky_pipe);
        ctx.apply_bindings(&self.sky);
        ctx.apply_uniforms(mq::UniformsSource::table(&sky));
        ctx.draw(0, 3, 1);
        ctx.apply_pipeline(&self.pipe);
        ctx.apply_bindings(&self.terr);
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, self.terr_n, 1);
        ctx.apply_bindings(&self.bld);
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, self.bld_n, 1);
        if self.env_n > 0 {
            ctx.apply_pipeline(&self.env_pipe);
            ctx.apply_bindings(&self.env);
            ctx.apply_uniforms(mq::UniformsSource::table(&u));
            ctx.draw(0, self.env_n, 1);
        }
        ctx.end_render_pass();
    }
}

// ------------------------------------------------------------------ dynamic geometry

fn v3(p: [f32; 3]) -> Vec3 {
    vec3(p[0], p[1], p[2])
}

fn sv3(s: &State) -> Vec3 {
    vec3(s[X] as f32, s[Y] as f32, s[Z] as f32)
}

/// Camera-facing ribbons through `pts`, split into u16-indexed meshes.
fn ribbon(pts: &[Vec3], cols: &[Color], width: f32, cam: Vec3) {
    if pts.len() < 2 {
        return;
    }
    let mut verts: Vec<Vertex> = Vec::new();
    let mut idx: Vec<u16> = Vec::new();
    let flush = |verts: &mut Vec<Vertex>, idx: &mut Vec<u16>| {
        if !idx.is_empty() {
            draw_mesh(&Mesh { vertices: std::mem::take(verts), indices: std::mem::take(idx), texture: None });
        }
    };
    for i in 0..pts.len() {
        let a = pts[i.saturating_sub(1)];
        let b = pts[(i + 1).min(pts.len() - 1)];
        let dir = (b - a).normalize_or_zero();
        let view = (cam - pts[i]).normalize_or_zero();
        let side = dir.cross(view).normalize_or_zero() * (width * 0.5);
        let c = cols[i.min(cols.len() - 1)];
        let p0 = pts[i] - side;
        let p1 = pts[i] + side;
        if verts.len() + 2 > 60000 {
            flush(&mut verts, &mut idx);
        }
        let base = verts.len() as u16;
        verts.push(Vertex::new(p0.x, p0.y, p0.z, 0.0, 0.0, c));
        verts.push(Vertex::new(p1.x, p1.y, p1.z, 0.0, 0.0, c));
        if i > 0 && base >= 2 {
            idx.extend_from_slice(&[base - 2, base - 1, base + 1, base - 2, base + 1, base]);
        }
    }
    flush(&mut verts, &mut idx);
}

/// Body axes: forward, left wing, up (bank + = left wing down).
fn body_axes(s: &State) -> (Vec3, Vec3, Vec3) {
    let (sg, cg) = (s[GAM] as f32).sin_cos();
    let (sp, cp) = (s[PSI] as f32).sin_cos();
    let (sb, cb) = (s[PHI] as f32).sin_cos();
    let f = vec3(cg * cp, cg * sp, sg);
    let l0 = vec3(-sp, cp, 0.0);
    let u0 = f.cross(l0);
    (f, l0 * cb - u0 * sb, u0 * cb + l0 * sb)
}

fn draw_aircraft(s: &State) {
    let p = sv3(s);
    let (f, l, u) = body_axes(s);
    let white = [0.95, 0.95, 0.96];
    let red = [0.86, 0.18, 0.12];
    let glass = [0.14, 0.22, 0.32];
    let parts: [([f32; 3], [f32; 3], [f32; 3]); 9] = [
        ([0.0, 0.0, 0.0], [3.2, 0.55, 0.6], white),
        ([3.6, 0.0, -0.05], [0.5, 0.45, 0.45], red),
        ([1.0, 0.0, 0.62], [1.1, 0.45, 0.3], glass),
        ([0.6, 0.0, 0.35], [0.8, 4.5, 0.09], white),
        ([0.6, 4.25, 0.37], [0.82, 0.3, 0.1], red),
        ([0.6, -4.25, 0.37], [0.82, 0.3, 0.1], red),
        ([-3.1, 0.0, 0.2], [0.45, 1.6, 0.06], white),
        ([-3.0, 0.0, 0.95], [0.5, 0.06, 0.8], red),
        ([4.15, 0.0, -0.05], [0.04, 0.12, 0.12], [0.2, 0.2, 0.2]),
    ];
    let sun = sun_n();
    let mut verts = Vec::new();
    let mut idx: Vec<u16> = Vec::new();
    let to_w = |q: Vec3| p + f * q.x + l * q.y + u * q.z;
    for (c, h, col) in parts {
        let c = v3(c);
        let h = v3(h);
        let faces: [(Vec3, [Vec3; 4]); 6] = [
            (Vec3::X, [vec3(1., -1., -1.), vec3(1., 1., -1.), vec3(1., 1., 1.), vec3(1., -1., 1.)]),
            (-Vec3::X, [vec3(-1., 1., -1.), vec3(-1., -1., -1.), vec3(-1., -1., 1.), vec3(-1., 1., 1.)]),
            (Vec3::Y, [vec3(1., 1., -1.), vec3(-1., 1., -1.), vec3(-1., 1., 1.), vec3(1., 1., 1.)]),
            (-Vec3::Y, [vec3(-1., -1., -1.), vec3(1., -1., -1.), vec3(1., -1., 1.), vec3(-1., -1., 1.)]),
            (Vec3::Z, [vec3(-1., -1., 1.), vec3(1., -1., 1.), vec3(1., 1., 1.), vec3(-1., 1., 1.)]),
            (-Vec3::Z, [vec3(-1., 1., -1.), vec3(1., 1., -1.), vec3(1., -1., -1.), vec3(-1., -1., -1.)]),
        ];
        for (n, q) in faces {
            let nw = f * n.x + l * n.y + u * n.z;
            let k = 0.5 + 0.55 * nw.dot(sun).max(0.0);
            let color = Color::new((col[0] * k).min(1.0), (col[1] * k).min(1.0), (col[2] * k).min(1.0), 1.0);
            let base = verts.len() as u16;
            for corner in q {
                let wp = to_w(c + corner * h);
                verts.push(Vertex::new(wp.x, wp.y, wp.z, 0.0, 0.0, color));
            }
            idx.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
        }
    }
    draw_mesh(&Mesh { vertices: verts, indices: idx, texture: None });
}

fn draw_disc(c: Vec3, r: f32, color: Color) {
    let mut verts = vec![Vertex::new(c.x, c.y, c.z, 0.0, 0.0, color)];
    let mut idx = Vec::new();
    let n = 24;
    for k in 0..=n {
        let a = k as f32 / n as f32 * std::f32::consts::TAU;
        verts.push(Vertex::new(c.x + r * a.cos(), c.y + r * a.sin(), c.z, 0.0, 0.0, Color { a: 0.0, ..color }));
        if k > 0 {
            idx.extend_from_slice(&[0, k as u16, k as u16 + 1]);
        }
    }
    draw_mesh(&Mesh { vertices: verts, indices: idx, texture: None });
}

// ------------------------------------------------------------------ text

struct Ui {
    mono: Option<Font>,
    sans: Option<Font>,
}

impl Ui {
    fn text(&self, s: &str, x: f32, y: f32, size: f32, color: Color, mono: bool) {
        let dpi = screen_dpi_scale();
        let font = if mono { self.mono.as_ref() } else { self.sans.as_ref() };
        draw_text_ex(s, x, y, TextParams { font, font_size: (size * dpi) as u16, font_scale: 1.0 / dpi, color, ..Default::default() });
    }
    fn width(&self, s: &str, size: f32, mono: bool) -> f32 {
        let dpi = screen_dpi_scale();
        let font = if mono { self.mono.as_ref() } else { self.sans.as_ref() };
        measure_text(s, font, (size * dpi) as u16, 1.0 / dpi).width
    }
    fn pill(&self, s: &str, x: f32, y: f32, bg: Color, fg: Color) -> f32 {
        let w = self.width(s, 15.0, false) + 22.0;
        draw_rectangle(x, y, w, 28.0, bg);
        self.text(s, x + 11.0, y + 19.5, 15.0, fg, false);
        w
    }
}

fn load_font(paths: &[&str]) -> Option<Font> {
    for p in paths {
        if let Ok(bytes) = std::fs::read(p) {
            if let Ok(f) = load_ttf_font_from_bytes(&bytes) {
                return Some(f);
            }
        }
    }
    None
}

// ------------------------------------------------------------------ app

struct HarnessJob {
    progress: Arc<Mutex<(String, usize, usize)>>,
    result: Arc<Mutex<Option<String>>>,
    visible: bool,
}

struct App {
    world: &'static World,
    sim: Sim<'static>,
    fbw: Fbw,
    scenario: usize,
    phase: Phase,
    robust: bool,
    wind: bool,
    model_error: bool,
    kamikaze: Option<Kamikaze>,
    show_paths: bool,
    show_help: bool,
    cam_mode: usize,
    invert: bool,
    stick: (f64, f64),
    acc: f64,
    trail: VecDeque<(Vec3, Color)>,
    trail_t: f64,
    paths: Vec<(Vec<Vec3>, bool)>,
    plan_path: Vec<Vec3>,
    path_t: f64,
    cam_pos: Vec3,
    orbit: f32,
    act: f32,
    harness: Option<HarnessJob>,
    seed: u64,
    /// Tab pressed: switch to the other map before the next frame.
    switch_map: bool,
}

const CAM_NAMES: [&str; 4] = ["chase", "cockpit", "orbit", "overhead"];

/// Clickable filter toggle, just under the instrument panel.
fn filter_button() -> Rect {
    Rect::new(16.0, 277.0, 300.0, 42.0)
}

impl App {
    fn cfg(&self, filter_on: bool) -> SimCfg {
        SimCfg { filter_on, filter: FilterCfg { phase: self.phase, robust: self.robust }, wind: self.wind, model_error: self.model_error, seed: self.seed }
    }

    fn reset(&mut self, scenario: usize) {
        self.scenario = scenario;
        self.seed += 1;
        let s0 = scenario_start(self.world, scenario);
        let on = self.sim.cfg.filter_on;
        self.sim = Sim::new(self.world, s0, self.cfg(on));
        self.fbw = Fbw::from_state(&s0);
        self.trail.clear();
        self.paths.clear();
        self.plan_path.clear();
        self.acc = 0.0;
        self.stick = (0.0, 0.0);
        if self.kamikaze.is_some() {
            self.kamikaze = Some(Kamikaze::new(self.seed));
        }
        let (f, _, _) = body_axes(&s0);
        self.cam_pos = sv3(&s0) - f * 30.0 + vec3(0.0, 0.0, 8.0);
    }

    /// Rebuild the sim with new settings, keeping the aircraft where it is.
    fn rebuild(&mut self) {
        let s = self.sim.s;
        let on = self.sim.cfg.filter_on;
        let crashed = self.sim.crashed;
        self.sim = Sim::new(self.world, s, self.cfg(on));
        self.sim.crashed = crashed;
    }

    fn input(&mut self, dt: f64) {
        let down = |a: KeyCode, b: KeyCode| is_key_down(a) || is_key_down(b);
        let mut pitch = 0.0;
        if down(KeyCode::W, KeyCode::Up) {
            pitch -= 1.0;
        }
        if down(KeyCode::S, KeyCode::Down) {
            pitch += 1.0;
        }
        if self.invert {
            pitch = -pitch;
        }
        let mut roll = 0.0;
        if down(KeyCode::A, KeyCode::Left) {
            roll -= 1.0;
        }
        if down(KeyCode::D, KeyCode::Right) {
            roll += 1.0;
        }
        let k = (dt * 8.0).min(1.0);
        self.stick.0 += (pitch - self.stick.0) * k;
        self.stick.1 += (roll - self.stick.1) * k;
        if is_key_down(KeyCode::E) {
            self.fbw.thr = (self.fbw.thr + 0.5 * dt).min(1.0);
        }
        if is_key_down(KeyCode::Q) {
            self.fbw.thr = (self.fbw.thr - 0.5 * dt).max(0.0);
        }
        let clicked = is_mouse_button_pressed(MouseButton::Left) && filter_button().contains(mouse_position().into());
        if is_key_pressed(KeyCode::Space) || clicked {
            let on = !self.sim.cfg.filter_on;
            self.sim.set_filter(on);
        }
        if is_key_pressed(KeyCode::Tab) {
            self.switch_map = true;
        }
        if is_key_pressed(KeyCode::B) {
            self.show_paths = !self.show_paths;
        }
        if is_key_pressed(KeyCode::N) {
            self.wind = !self.wind;
            self.rebuild();
        }
        if is_key_pressed(KeyCode::M) {
            self.model_error = !self.model_error;
            self.rebuild();
        }
        if is_key_pressed(KeyCode::F) {
            self.phase = match self.phase {
                Phase::P1 => Phase::P2,
                Phase::P2 => Phase::Permissive,
                Phase::Permissive => Phase::P1,
            };
            self.rebuild();
        }
        if is_key_pressed(KeyCode::G) {
            self.robust = !self.robust;
            self.rebuild();
        }
        if is_key_pressed(KeyCode::C) {
            self.cam_mode = (self.cam_mode + 1) % 4;
        }
        if is_key_pressed(KeyCode::I) {
            self.invert = !self.invert;
        }
        if is_key_pressed(KeyCode::H) {
            self.show_help = !self.show_help;
        }
        if is_key_pressed(KeyCode::Escape) {
            self.show_help = false;
            if let Some(h) = &mut self.harness {
                h.visible = false;
            }
        }
        if is_key_pressed(KeyCode::K) {
            self.kamikaze = if self.kamikaze.is_some() { None } else { Some(Kamikaze::new(self.seed)) };
            if self.kamikaze.is_none() {
                self.fbw = Fbw { thr: self.fbw.thr, ..Fbw::from_state(&self.sim.s) };
            }
        }
        if is_key_pressed(KeyCode::R) {
            self.reset(self.scenario);
        }
        for (key, id) in [(KeyCode::Key1, 0), (KeyCode::Key2, 1), (KeyCode::Key3, 2), (KeyCode::Key4, 3)] {
            if is_key_pressed(key) {
                self.reset(id);
            }
        }
        if is_key_pressed(KeyCode::T) {
            self.toggle_harness();
        }
    }

    fn toggle_harness(&mut self) {
        if let Some(h) = &mut self.harness {
            let running = h.result.lock().unwrap().is_none();
            if running || h.visible {
                h.visible = !h.visible;
                return;
            }
        }
        let progress = Arc::new(Mutex::new(("starting".to_string(), 0, 1)));
        let result = Arc::new(Mutex::new(None));
        let (p2, r2) = (progress.clone(), result.clone());
        let world = self.world;
        std::thread::spawn(move || {
            let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).saturating_sub(2).max(1);
            let opts = HarnessOpts { only: None, episodes: 200, threads, kamikaze_secs: 300.0, extended: false };
            let t0 = std::time::Instant::now();
            let rep = run_harness(world, &opts, &|n, d, t| *p2.lock().unwrap() = (n.to_string(), d, t));
            let text = format!("{}\n{} threads, {:.0} s", format_report(&rep), threads, t0.elapsed().as_secs_f64());
            *r2.lock().unwrap() = Some(text);
        });
        self.harness = Some(HarnessJob { progress, result, visible: true });
    }

    fn step(&mut self, dt: f64) {
        if self.sim.crashed {
            return;
        }
        self.acc += dt;
        let mut n = 0;
        while self.acc >= DT_F && n < 10 {
            self.acc -= DT_F;
            n += 1;
            if let Some(k) = &mut self.kamikaze {
                k.update(self.world, &self.sim.s, &mut self.fbw, DT_F);
            } else {
                self.fbw.sticks(self.stick.0, self.stick.1, DT_F);
            }
            let u = self.fbw.cmd(&self.sim.prm_ctrl, &self.sim.s);
            self.sim.tick(u);
            self.fbw.resync(&self.sim.s, self.sim.fs.lam, DT_F);
            self.trail_t += DT_F;
            if self.trail_t >= 0.1 {
                self.trail_t = 0.0;
                let c = match (self.sim.cfg.filter_on, self.sim.fs.mode) {
                    (false, _) => Color::new(0.92, 0.92, 0.95, 0.75),
                    (_, Mode::Commit) => Color::new(1.0, 0.25, 0.12, 0.9),
                    (_, Mode::Blend) => {
                        let l = self.sim.fs.lam as f32;
                        Color::new(0.25 + 0.75 * l, 0.75 - 0.25 * l, 1.0 - 0.9 * l, 0.85)
                    }
                    _ => Color::new(0.25, 0.75, 1.0, 0.75),
                };
                self.trail.push_back((sv3(&self.sim.s), c));
                if self.trail.len() > 900 {
                    self.trail.pop_front();
                }
            }
            if self.sim.crashed {
                break;
            }
        }
        if self.acc > DT_F {
            self.acc = 0.0;
        }
        self.path_t -= dt;
        if self.path_t <= 0.0 {
            self.path_t = 0.1;
            self.update_paths();
        }
    }

    fn update_paths(&mut self) {
        let pred = Pred { accept: false, ..self.sim.pred() };
        let s = self.sim.s;
        self.paths.clear();
        for i in 0..N_ESC {
            let mut p = Vec::new();
            let r = pred.rollout(&s, None, i, 0.0, None, f64::NEG_INFINITY, Some(&mut p));
            self.paths.push((p.iter().map(|q| v3(*q)).collect(), r.valid));
        }
        self.plan_path.clear();
        if self.sim.cfg.filter_on {
            if let Some(pl) = self.sim.fs.plan {
                let mut p = Vec::new();
                let (hold, te) = pl.tail(self.sim.k);
                pred.rollout(&s, hold, pl.esc, te, pl.eref, f64::NEG_INFINITY, Some(&mut p));
                self.plan_path = p.iter().map(|q| v3(*q)).collect();
            }
        }
    }

    fn camera(&mut self, dt: f32) -> Camera3D {
        let s = &self.sim.s;
        let p = sv3(s);
        let (f, _, u) = body_axes(s);
        let fh = vec3(f.x, f.y, 0.0).normalize_or_zero();
        let (pos, target, up) = match self.cam_mode {
            1 => (p + f * 1.2 + u * 1.05, p + f * 300.0 + u * 1.05, u),
            2 => {
                self.orbit += dt * 0.25;
                (p + vec3(self.orbit.cos() * 70.0, self.orbit.sin() * 70.0, 22.0), p, Vec3::Z)
            }
            3 => (p + vec3(0.0, 0.0, 650.0) - fh * 250.0, p + fh * 60.0, Vec3::Z),
            _ => {
                let desired = p - f * 24.0 - fh * 6.0 + vec3(0.0, 0.0, 7.0);
                let k = 1.0 - (-dt * 5.0).exp();
                if !self.sim.crashed {
                    self.cam_pos = self.cam_pos.lerp(desired, k);
                }
                // Don't let the camera sit inside a building in a canyon:
                // walk back from the aircraft and stop before any wall.
                let mut cam = self.cam_pos;
                let n = 24;
                for i in 1..=n {
                    let q = p.lerp(self.cam_pos, i as f32 / n as f32);
                    let d = self.world.building_dist([q.x as f64, q.y as f64, q.z as f64], 3.0);
                    if d < 1.5 {
                        cam = p.lerp(self.cam_pos, (i - 1) as f32 / n as f32);
                        break;
                    }
                }
                (cam, p + f * 25.0, Vec3::Z)
            }
        };
        Camera3D { position: pos, target, up, fovy: 1.0, z_near: 0.5, z_far: 16000.0, ..Default::default() }
    }


    fn draw_world_dynamic(&self, cam: &Camera3D) {
        set_camera(cam);
        let s = &self.sim.s;
        let p = sv3(s);
        // Ground shadow under the aircraft.
        let gz = self.world.surface(s[X], s[Y]) as f32 + 0.4;
        let alt = (p.z - gz).max(0.0);
        draw_disc(vec3(p.x, p.y, gz), 6.0 + alt * 0.02, Color::new(0.0, 0.0, 0.0, (0.45 - alt * 0.0015).max(0.08)));
        // Trail.
        let pts: Vec<Vec3> = self.trail.iter().map(|t| t.0).chain(std::iter::once(p)).collect();
        let cols: Vec<Color> = self.trail.iter().map(|t| t.1).collect();
        ribbon(&pts, &cols, 1.6, cam.position);
        // Escape paths and the committed plan.
        if self.show_paths {
            for (path, ok) in &self.paths {
                let c = if *ok { Color::new(0.2, 0.95, 0.35, 0.8) } else { Color::new(1.0, 0.2, 0.2, 0.8) };
                ribbon(path, &[c], 1.3, cam.position);
            }
            if !self.plan_path.is_empty() {
                ribbon(&self.plan_path, &[Color::new(1.0, 0.85, 0.2, 0.95)], 2.2, cam.position);
            }
        }
        if let Some(k) = &self.kamikaze {
            let t = vec3(k.target[0] as f32, k.target[1] as f32, k.target[2] as f32);
            let pulse = 0.5 + 0.5 * (get_time() as f32 * 6.0).sin();
            draw_sphere(t, 6.0 + 4.0 * pulse, None, Color::new(1.0, 0.1, 0.1, 0.6));
            draw_line_3d(t, t + vec3(0.0, 0.0, 120.0), Color::new(1.0, 0.2, 0.2, 0.8));
        }
        if self.cam_mode != 1 {
            draw_aircraft(s);
        }
    }

    fn draw_tint(&self) {
        let a = self.act;
        if a < 0.01 {
            return;
        }
        let (w, h) = (screen_width(), screen_height());
        let d = w.min(h) * 0.2;
        let c0 = Color::new(1.0, 0.5, 0.08, 0.6 * a);
        let c1 = Color::new(1.0, 0.5, 0.08, 0.0);
        let quad = |v: [(f32, f32, Color); 4]| {
            let verts = v.iter().map(|&(x, y, c)| Vertex::new(x, y, 0.0, 0.0, 0.0, c)).collect();
            draw_mesh(&Mesh { vertices: verts, indices: vec![0, 1, 2, 0, 2, 3], texture: None });
        };
        quad([(0.0, 0.0, c0), (w, 0.0, c0), (w - d, d, c1), (d, d, c1)]);
        quad([(0.0, h, c0), (d, h - d, c1), (w - d, h - d, c1), (w, h, c0)]);
        quad([(0.0, 0.0, c0), (d, d, c1), (d, h - d, c1), (0.0, h, c0)]);
        quad([(w, 0.0, c0), (w, h, c0), (w - d, h - d, c1), (w - d, d, c1)]);
    }

    fn draw_hud(&self, ui: &Ui) {
        let s = &self.sim.s;
        let fs = &self.sim.fs;
        let on = self.sim.cfg.filter_on;
        let (w, h) = (screen_width(), screen_height());
        let panel = Color::new(0.04, 0.06, 0.09, 0.62);
        let dim = Color::new(0.70, 0.76, 0.84, 1.0);
        let bright = Color::new(0.97, 0.98, 1.0, 1.0);
        // Left panel.
        let agl = s[Z] - self.world.terrain(s[X], s[Y]);
        let hv = if on { fs.h } else { Pred { accept: false, ..self.sim.pred() }.best(s, None, &ESC_ORDER, f64::INFINITY).0 };
        let h_txt = if hv == f64::NEG_INFINITY { "none valid".to_string() } else { format!("{:.1} m", hv) };
        let esc = match (on, fs.mode) {
            (true, Mode::Blend) | (true, Mode::Commit) => fs.act_esc.map(|i| ESC_NAMES[i]).unwrap_or("-"),
            _ => "-",
        };
        let rows: Vec<(&str, String)> = vec![
            ("AIRSPEED", format!("{:.1} m/s  {:.0} kt", s[V], s[V] * 1.94384)),
            ("HEIGHT AGL", format!("{:.0} m", agl)),
            ("THROTTLE", format!("{:.0} %", s[THR] * 100.0)),
            ("PATH / BANK", format!("{:+.1}°  {:+.0}°", s[GAM].to_degrees(), -s[PHI].to_degrees())),
            ("h  BARRIER", h_txt),
            ("BLEND λ", if on { format!("{:.2}", if fs.mode == Mode::Commit { 1.0 } else { fs.lam }) } else { "-".into() }),
            ("ESCAPE", esc.to_string()),
            ("FILTER TIME", if on { format!("{:.2} ms/tick", fs.ms) } else { "-".into() }),
            ("TRUE CLEARANCE", format!("{:.1} m", self.sim.true_clear)),
        ];
        let px = 16.0;
        let py = 16.0;
        let ph = 18.0 + rows.len() as f32 * 23.0 + 26.0;
        draw_rectangle(px, py, 300.0, ph, panel);
        for (i, (k, v)) in rows.iter().enumerate() {
            let y = py + 28.0 + i as f32 * 23.0;
            ui.text(k, px + 14.0, y, 13.0, dim, false);
            ui.text(v, px + 138.0, y, 15.0, bright, true);
        }
        // λ bar
        let by = py + 28.0 + rows.len() as f32 * 23.0 - 6.0;
        draw_rectangle(px + 14.0, by, 272.0, 6.0, Color::new(1.0, 1.0, 1.0, 0.12));
        draw_rectangle(px + 14.0, by, 272.0 * self.act, 6.0, Color::new(1.0, 0.55, 0.1, 0.95));

        // Filter toggle button.
        let r = filter_button();
        let hover = r.contains(mouse_position().into());
        let (bg, label) = if on {
            (Color::new(0.10, 0.55, 0.28, if hover { 1.0 } else { 0.88 }), "SAFETY FILTER: ON")
        } else {
            (Color::new(0.75, 0.12, 0.10, if hover { 1.0 } else { 0.88 }), "SAFETY FILTER: OFF")
        };
        draw_rectangle(r.x, r.y, r.w, r.h, bg);
        ui.text(label, r.x + 14.0, r.y + 27.0, 17.0, WHITE, false);
        let hint = "click / Space";
        ui.text(hint, r.x + r.w - ui.width(hint, 13.0, false) - 12.0, r.y + 26.0, 13.0, Color::new(1.0, 1.0, 1.0, 0.75), false);

        // Status pills, top centre.
        let mut pills: Vec<(String, Color, Color)> = Vec::new();
        if on {
            let mode = match fs.mode {
                Mode::Commit => format!("COMMITTED ESCAPE · {}", fs.act_esc.map(|i| ESC_NAMES[i]).unwrap_or("-")),
                Mode::Blend => format!("blending {:.0} %", fs.lam * 100.0),
                _ => "pilot in control".to_string(),
            };
            let phase = format!("{}{}", self.phase.name(), if self.robust { " + P3 robust" } else { "" });
            pills.push((format!("SAFETY FILTER ON · {phase}"), Color::new(0.10, 0.55, 0.28, 0.92), WHITE));
            let mc = if fs.mode == Mode::Commit {
                Color::new(0.85, 0.2, 0.1, 0.92)
            } else if fs.mode == Mode::Blend {
                Color::new(0.95, 0.5, 0.08, 0.92)
            } else {
                Color::new(0.1, 0.12, 0.16, 0.7)
            };
            pills.push((mode, mc, WHITE));
        } else {
            pills.push(("SAFETY FILTER OFF".into(), Color::new(0.75, 0.12, 0.1, 0.92), WHITE));
        }
        if self.wind {
            let txt = format!("WIND {:.0} m/s · gusts ≤ {:.1} m/s", WIND_SPEED, GUST_XY);
            pills.push((txt, Color::new(0.15, 0.4, 0.7, 0.92), WHITE));
        }
        if self.model_error {
            pills.push(("MODEL ERROR: weaker aircraft".into(), Color::new(0.55, 0.25, 0.7, 0.92), WHITE));
        }
        if self.kamikaze.is_some() {
            pills.push(("KAMIKAZE AUTOPILOT".into(), Color::new(0.6, 0.05, 0.05, 0.92), WHITE));
        }
        let widths: Vec<f32> = pills.iter().map(|p| ui.width(&p.0, 15.0, false) + 22.0).collect();
        let total: f32 = widths.iter().sum::<f32>() + 8.0 * (pills.len() as f32 - 1.0);
        let mut x = (w - total) * 0.5;
        for (p, wd) in pills.iter().zip(&widths) {
            ui.pill(&p.0, x, 16.0, p.1, p.2);
            x += wd + 8.0;
        }
        if on && !fs.inv_ok && !self.sim.crashed {
            let t = "OUTSIDE VERIFIED SAFE SET";
            let tw = ui.width(t, 20.0, false);
            draw_rectangle((w - tw) * 0.5 - 14.0, 56.0, tw + 28.0, 36.0, Color::new(0.8, 0.1, 0.1, 0.9));
            ui.text(t, (w - tw) * 0.5, 81.0, 20.0, WHITE, false);
        }
        // Bottom bar.
        let hint = format!(
            "{} · {} · H help · Tab map · Space filter · B escapes · C camera ({}) · 1-4 scenarios · K kamikaze · T harness · R reset{}",
            self.world.map.name(),
            scenario_names(self.world.map)[self.scenario],
            CAM_NAMES[self.cam_mode],
            if self.world.map == MapId::SanFrancisco { " · map data: DataSF, © OpenStreetMap contributors, USGS" } else { "" }
        );
        draw_rectangle(0.0, h - 30.0, w, 30.0, Color::new(0.04, 0.06, 0.09, 0.55));
        ui.text(&hint, 14.0, h - 10.0, 13.0, dim, false);
        let fps = format!("{} fps  t={:.1}s", get_fps(), self.sim.time());
        ui.text(&fps, w - ui.width(&fps, 13.0, true) - 14.0, h - 10.0, 13.0, dim, true);

        if self.sim.crashed {
            draw_rectangle(0.0, 0.0, w, h, Color::new(0.3, 0.0, 0.0, 0.35));
            let t = "CRASH";
            ui.text(t, (w - ui.width(t, 64.0, false)) * 0.5, h * 0.42, 64.0, WHITE, false);
            let sub = format!(
                "true clearance {:.1} m at t = {:.1} s · filter was {} · R retry · Space toggles the filter",
                self.sim.crash_clear,
                self.sim.time(),
                if on { "ON" } else { "OFF" }
            );
            ui.text(&sub, (w - ui.width(&sub, 17.0, false)) * 0.5, h * 0.42 + 40.0, 17.0, WHITE, false);
        }
        if self.show_help {
            self.draw_help(ui);
        }
        if let Some(job) = &self.harness {
            if job.visible {
                self.draw_harness(ui, job);
            }
        }
    }

    fn draw_help(&self, ui: &Ui) {
        let (w, h) = (screen_width(), screen_height());
        let pw = 700.0f32.min(w - 40.0);
        let scen = scenario_names(self.world.map).join(" · ").to_lowercase();
        let lines: [(&str, &str); 16] = [
            ("W/S  ↑/↓", "pitch (stick forward = nose down; I inverts)"),
            ("A/D  ←/→", "roll · release the keys to hold flight path and bank"),
            ("Q / E", "throttle down / up"),
            ("Space", "safety filter on / off"),
            ("F", "filter: P1 blend+commit · P2 closed-form · permissive"),
            ("G", "Phase 3 robust margins on / off"),
            ("B", "show escape paths (green valid, red not, yellow committed)"),
            ("N", "wind: 7 m/s steady + bounded gusts (filter knows the envelope)"),
            ("M", "model error: a weaker, slower aircraft than the filter assumes"),
            ("C", "camera: chase · cockpit · orbit · overhead"),
            ("1 2 3 4", scen.as_str()),
            ("K", "kamikaze autopilot (flies at buildings and terrain)"),
            ("T", "run the 200-episode headless harness"),
            ("R", "reset the scenario"),
            ("H / Esc", "toggle / close this help"),
            ("Tab", "map: grid city · San Francisco"),
        ];
        let ph = 150.0 + lines.len() as f32 * 24.0;
        let (x, y) = ((w - pw) * 0.5, (h - ph) * 0.5);
        draw_rectangle(x, y, pw, ph, Color::new(0.03, 0.05, 0.08, 0.9));
        ui.text(&format!("Backup-CBF City Flight · {}", self.world.map.name()), x + 24.0, y + 40.0, 26.0, WHITE, false);
        ui.text(
            "Fly anywhere. Near buildings and terrain, a backup control barrier function filter",
            x + 24.0,
            y + 66.0,
            14.0,
            Color::new(0.8, 0.85, 0.9, 1.0),
            false,
        );
        ui.text(
            "blends your commands toward a verified escape maneuver, then hands control back.",
            x + 24.0,
            y + 84.0,
            14.0,
            Color::new(0.8, 0.85, 0.9, 1.0),
            false,
        );
        for (i, (k, v)) in lines.iter().enumerate() {
            let yy = y + 120.0 + i as f32 * 24.0;
            ui.text(k, x + 24.0, yy, 15.0, Color::new(1.0, 0.8, 0.35, 1.0), true);
            ui.text(v, x + 150.0, yy, 15.0, WHITE, false);
        }
        let warn1 = "The guarantee holds for the nominal aircraft with full state knowledge.";
        let warn2 = "Wind is covered up to its gust envelope; model error (M) is not: use G for margins.";
        ui.text(warn1, x + 24.0, y + ph - 44.0, 14.0, Color::new(1.0, 0.65, 0.4, 1.0), false);
        ui.text(warn2, x + 24.0, y + ph - 24.0, 14.0, Color::new(1.0, 0.65, 0.4, 1.0), false);
    }

    fn draw_harness(&self, ui: &Ui, job: &HarnessJob) {
        let (w, h) = (screen_width(), screen_height());
        let result = job.result.lock().unwrap().clone();
        let pw = 1010.0f32.min(w - 40.0);
        let (x, y) = ((w - pw) * 0.5, 70.0);
        match result {
            None => {
                let (name, d, n) = job.progress.lock().unwrap().clone();
                draw_rectangle(x, y, pw, 110.0, Color::new(0.03, 0.05, 0.08, 0.9));
                ui.text("Harness running (headless, multi-threaded)…", x + 24.0, y + 36.0, 18.0, WHITE, false);
                ui.text(&format!("{name}: {d} / {n}"), x + 24.0, y + 62.0, 15.0, Color::new(0.8, 0.85, 0.9, 1.0), true);
                draw_rectangle(x + 24.0, y + 78.0, pw - 48.0, 10.0, Color::new(1.0, 1.0, 1.0, 0.15));
                draw_rectangle(x + 24.0, y + 78.0, (pw - 48.0) * d as f32 / n.max(1) as f32, 10.0, Color::new(0.3, 0.8, 1.0, 1.0));
            }
            Some(text) => {
                let lines: Vec<&str> = text.lines().collect();
                let ph = (40.0 + lines.len() as f32 * 19.0).min(h - 100.0);
                draw_rectangle(x, y, pw, ph, Color::new(0.03, 0.05, 0.08, 0.94));
                for (i, l) in lines.iter().enumerate() {
                    let c = if l.contains("[x]") {
                        Color::new(0.4, 1.0, 0.5, 1.0)
                    } else if l.contains("[ ]") {
                        Color::new(1.0, 0.4, 0.35, 1.0)
                    } else {
                        WHITE
                    };
                    ui.text(l, x + 18.0, y + 30.0 + i as f32 * 19.0, 13.0, c, true);
                }
            }
        }
    }
}

#[macroquad::main(window_conf)]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)).cloned();
    let shot = arg("--shot");
    let shot_frames: u32 = arg("--frames").and_then(|s| s.parse().ok()).unwrap_or(90);

    clear_background(Color::new(FOG[0], FOG[1], FOG[2], 1.0));
    next_frame().await;
    let map = match arg("--map") {
        None => MapId::Grid,
        Some(m) => MapId::parse(&m).unwrap_or_else(|| {
            eprintln!("--map takes grid or sf");
            std::process::exit(2)
        }),
    };
    // Each map is loaded (and its GPU scene built) once, on first use.
    let mut worlds: [Option<&'static World>; 2] = [None, None];
    let mut scenes: [Option<StaticScene>; 2] = [None, None];
    let world: &'static World = Box::leak(Box::new(World::load(map)));
    worlds[map as usize] = Some(world);
    scenes[map as usize] = Some(StaticScene::new(world));
    let ui = Ui {
        mono: load_font(&["/System/Library/Fonts/SFNSMono.ttf", "/System/Library/Fonts/Menlo.ttc"]),
        sans: load_font(&["/System/Library/Fonts/SFNS.ttf", "/System/Library/Fonts/Helvetica.ttc"]),
    };
    let scenario: usize = arg("--scenario").and_then(|s| s.parse::<usize>().ok()).map(|s| s.clamp(1, 4) - 1).unwrap_or(0);
    let s0 = scenario_start(world, scenario);
    let mut app = App {
        world,
        sim: Sim::new(world, s0, SimCfg::default()),
        fbw: Fbw::from_state(&s0),
        scenario,
        phase: Phase::P1,
        robust: false,
        wind: false,
        model_error: false,
        kamikaze: None,
        show_paths: args.iter().any(|a| a == "--paths"),
        show_help: shot.is_none(),
        cam_mode: arg("--cam").and_then(|s| s.parse().ok()).unwrap_or(0),
        invert: false,
        stick: (0.0, 0.0),
        acc: 0.0,
        trail: VecDeque::new(),
        trail_t: 0.0,
        paths: Vec::new(),
        plan_path: Vec::new(),
        path_t: 0.0,
        cam_pos: Vec3::ZERO,
        orbit: 0.0,
        act: 0.0,
        harness: None,
        seed: 1,
        switch_map: false,
    };
    app.reset(scenario);
    if args.iter().any(|a| a == "--kamikaze") {
        app.kamikaze = Some(Kamikaze::new(app.seed));
    }
    // --at x,y,agl,heading_deg: start anywhere (map metres), level at 50 m/s.
    if let Some(at) = arg("--at") {
        let v: Vec<f64> = at.split(',').filter_map(|t| t.trim().parse().ok()).collect();
        if v.len() == 4 {
            let s0 = trimmed(v[0], v[1], app.world.terrain(v[0], v[1]) + v[2], 50.0, 0.0, v[3].to_radians(), 0.64);
            app.sim = Sim::new(app.world, s0, app.cfg(true));
            app.fbw = Fbw::from_state(&s0);
            let (f, _, _) = body_axes(&s0);
            app.cam_pos = sv3(&s0) - f * 30.0 + vec3(0.0, 0.0, 8.0);
        }
    }
    if args.iter().any(|a| a == "--off") {
        app.sim.set_filter(false);
    }
    let mut frame = 0u32;
    loop {
        if std::mem::take(&mut app.switch_map) {
            let m = app.world.map.next();
            if scenes[m as usize].is_none() {
                clear_background(Color::new(0.03, 0.05, 0.08, 1.0));
                let t = format!("Loading {}...", m.name());
                ui.text(&t, (screen_width() - ui.width(&t, 28.0, false)) * 0.5, screen_height() * 0.5, 28.0, WHITE, false);
                next_frame().await;
                let w: &'static World = *worlds[m as usize].get_or_insert_with(|| Box::leak(Box::new(World::load(m))));
                scenes[m as usize] = Some(StaticScene::new(w));
            }
            app.world = worlds[m as usize].unwrap();
            app.reset(app.scenario);
        }
        let scene = scenes[app.world.map as usize].as_ref().unwrap();
        let dt = get_frame_time().min(0.1) as f64;
        if shot.is_none() {
            app.input(dt);
        }
        app.step(if shot.is_some() { 1.0 / 60.0 } else { dt });
        let target = if !app.sim.cfg.filter_on {
            0.0
        } else if app.sim.fs.mode == Mode::Commit {
            1.0
        } else {
            app.sim.fs.lam as f32
        };
        app.act += (target - app.act) * (1.0 - (-dt as f32 * 10.0).exp());

        let cam = app.camera(dt as f32);
        clear_background(Color::new(FOG[0], FOG[1], FOG[2], 1.0));
        scene.draw(&cam);
        app.draw_world_dynamic(&cam);
        set_default_camera();
        app.draw_tint();
        app.draw_hud(&ui);

        frame += 1;
        if let Some(path) = &shot {
            if frame >= shot_frames {
                get_screen_data().export_png(path);
                break;
            }
        }
        next_frame().await;
    }
}
