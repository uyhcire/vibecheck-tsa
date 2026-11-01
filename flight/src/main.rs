//! Backup-CBF City Flight: the interactive demo.
//!
//! Static geometry (terrain, ~2k buildings) lives in immutable GPU buffers
//! drawn through raw miniquad; dynamic things (aircraft, escape paths, trail,
//! HUD) go through macroquad. The simulation and the safety filter come from
//! the library, the same code the headless harness runs.

mod assets;
mod atmos;
mod c172;
mod ground;
mod photo;
mod rt;
mod shaders;

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
const FOG: [f32; 3] = [0.74, 0.81, 0.89];
const SKY_TOP: Color = Color::new(0.30, 0.50, 0.82, 1.0);
const TEX: usize = 4096;

/// OpenGL instead of Metal (`--gl`): only the classic renderer, whose GLSL shaders run there.
fn use_gl() -> bool {
    !cfg!(target_vendor = "apple") || std::env::args().any(|a| a == "--gl")
}

fn window_conf() -> Conf {
    if std::env::args().any(|a| a == "--shot") {
        // Lets the Metal backend copy the drawable for screenshots.
        std::env::set_var("MINIQUAD_METAL_CAPTURE", "1");
    }
    Conf {
        window_title: "Backup-CBF City Flight".to_owned(),
        window_width: 1440,
        window_height: 900,
        high_dpi: true,
        // The photoreal renderer antialiases its own target; a 4x window costs it ~1.8 ms per frame.
        sample_count: if use_gl() || std::env::args().any(|a| a == "--classic") { 4 } else { 1 },
        window_resizable: true,
        platform: mq::conf::Platform {
            apple_gfx_api: if use_gl() { mq::conf::AppleGfxApi::OpenGl } else { mq::conf::AppleGfxApi::Metal },
            ..Default::default()
        },
        ..Default::default()
    }
}

fn sun_n() -> Vec3 {
    vec3(SUN[0], SUN[1], SUN[2]).normalize()
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
}

struct StaticScene {
    pipe: mq::Pipeline,
    terr: mq::Bindings,
    terr_n: i32,
    bld: mq::Bindings,
    bld_n: i32,
}

const VS: &str = r#"#version 100
attribute vec3 in_pos;
attribute vec3 in_nrm;
attribute vec3 in_col;
attribute vec2 in_uv;
attribute float in_win;
uniform mat4 mvp;
uniform vec3 cam;
uniform vec3 sun;
uniform vec3 fog;
uniform float dens;
varying highp vec3 v_pos;
varying mediump vec3 v_nrm;
varying mediump vec3 v_col;
varying highp vec2 v_uv;
varying mediump float v_win;
void main() {
    gl_Position = mvp * vec4(in_pos, 1.0);
    v_pos = in_pos; v_nrm = in_nrm; v_col = in_col; v_uv = in_uv; v_win = in_win;
}"#;

const FS: &str = r#"#version 100
precision highp float;
uniform sampler2D tex;
uniform mat4 mvp;
uniform vec3 cam;
uniform vec3 sun;
uniform vec3 fog;
uniform float dens;
varying highp vec3 v_pos;
varying mediump vec3 v_nrm;
varying mediump vec3 v_col;
varying highp vec2 v_uv;
varying mediump float v_win;
void main() {
    vec3 n = normalize(v_nrm);
    vec3 alb = v_col * texture2D(tex, v_uv).rgb;
    float d = length(v_pos - cam);
    if (v_win > 0.5 && abs(n.z) < 0.5) {
        float s = abs(n.x) > 0.5 ? v_pos.y : v_pos.x;
        float fl = fract(v_pos.z / 3.6);
        float cl = fract(s / 3.1);
        float w = step(0.30, fl) * step(fl, 0.86) * step(0.16, cl) * step(cl, 0.84);
        float far = smoothstep(500.0, 1800.0, d);
        w = mix(w, 0.42, far);
        vec3 glass = mix(vec3(0.13, 0.17, 0.23), vec3(0.50, 0.62, 0.76), 0.35 + 0.35 * max(dot(n, -sun), 0.0));
        alb = mix(alb, glass, w * 0.8);
    }
    float diff = max(dot(n, sun), 0.0);
    float sky = 0.5 + 0.5 * n.z;
    vec3 lit = alb * (vec3(0.36, 0.40, 0.48) * (0.55 + 0.45 * sky) + vec3(1.0, 0.95, 0.86) * diff * 0.82);
    float f = 1.0 - exp(-pow(d * dens, 1.5));
    gl_FragColor = vec4(mix(lit, fog, clamp(f, 0.0, 1.0)), 1.0);
}"#;

/// The classic shader for the Metal backend: same shading as `VS`/`FS`.
/// Uniforms arrive as the raw `SU` struct, so `packed_float3` matches its layout.
const CLASSIC_MSL: &str = r#"
#include <metal_stdlib>
using namespace metal;
struct SU { float4x4 mvp; packed_float3 cam; packed_float3 sun; packed_float3 fog; float dens; };
struct VIn { float3 pos [[attribute(0)]]; float3 nrm [[attribute(1)]]; float3 col [[attribute(2)]]; float2 uv [[attribute(3)]]; float win [[attribute(4)]]; };
struct VOut { float4 p [[position]]; float3 pos; float3 nrm; float3 col; float2 uv; float win; };
vertex VOut vertexShader(VIn v [[stage_in]], constant SU& u [[buffer(0)]]) {
    VOut o; o.p = u.mvp * float4(v.pos, 1.0);
    o.pos = v.pos; o.nrm = v.nrm; o.col = v.col; o.uv = v.uv; o.win = v.win; return o;
}
fragment float4 fragmentShader(VOut i [[stage_in]], constant SU& u [[buffer(0)]], texture2d<float> tex [[texture(0)]], sampler smp [[sampler(0)]]) {
    float3 n = normalize(i.nrm);
    float3 sun = float3(u.sun); float3 cam = float3(u.cam); float3 fog = float3(u.fog);
    float3 alb = i.col * tex.sample(smp, i.uv).rgb;
    float d = length(i.pos - cam);
    if (i.win > 0.5 && abs(n.z) < 0.5) {
        float s = abs(n.x) > 0.5 ? i.pos.y : i.pos.x;
        float fl = fract(i.pos.z / 3.6);
        float cl = fract(s / 3.1);
        float w = step(0.30, fl) * step(fl, 0.86) * step(0.16, cl) * step(cl, 0.84);
        float far = smoothstep(500.0, 1800.0, d);
        w = mix(w, 0.42, far);
        float3 glass = mix(float3(0.13, 0.17, 0.23), float3(0.50, 0.62, 0.76), 0.35 + 0.35 * max(dot(n, -sun), 0.0));
        alb = mix(alb, glass, w * 0.8);
    }
    float diff = max(dot(n, sun), 0.0);
    float sky = 0.5 + 0.5 * n.z;
    float3 lit = alb * (float3(0.36, 0.40, 0.48) * (0.55 + 0.45 * sky) + float3(1.0, 0.95, 0.86) * diff * 0.82);
    float f = 1.0 - exp(-pow(d * u.dens, 1.5));
    return float4(mix(lit, fog, clamp(f, 0.0, 1.0)), 1.0);
}
"#;

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

fn terrain_texture(w: &World) -> Vec<u8> {
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
                        let c = ground_color(w, x, y);
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

impl StaticScene {
    fn new(w: &World, px: &[u8]) -> StaticScene {
        let InternalGlContext { quad_context: ctx, .. } = unsafe { get_internal_gl() };
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
                tv.push(SV {
                    pos: [x as f32, y as f32, w.terr[j * TN + i]],
                    nrm: [n.x, n.y, n.z],
                    col: [1.0, 1.0, 1.0],
                    uv: [((x + MAP_HALF) / (2.0 * MAP_HALF)) as f32, ((y + MAP_HALF) / (2.0 * MAP_HALF)) as f32],
                    win: 0.0,
                });
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
        let tex = ctx.new_texture(
            mq::TextureAccess::Static,
            mq::TextureSource::Bytes(px),
            mq::TextureParams {
                format: mq::TextureFormat::RGBA8,
                wrap: mq::TextureWrap::Clamp,
                min_filter: mq::FilterMode::Linear,
                mag_filter: mq::FilterMode::Linear,
                mipmap_filter: mq::MipmapFilterMode::Linear,
                width: TEX as u32,
                height: TEX as u32,
                allocate_mipmaps: true,
                ..Default::default()
            },
        );
        ctx.texture_generate_mipmaps(tex);
        let white = ctx.new_texture_from_rgba8(1, 1, &[255, 255, 255, 255]);

        // Buildings: five faces per box.
        let mut bv: Vec<SV> = Vec::with_capacity(w.boxes.len() * 20);
        let mut bi: Vec<u32> = Vec::with_capacity(w.boxes.len() * 30);
        for b in &w.boxes {
            let col = building_color(b);
            let roof = [col[0] * 0.62 + 0.08, col[1] * 0.62 + 0.08, col[2] * 0.62 + 0.09];
            let (x0, x1, y0, y1, z0, z1) = (b.x0 as f32, b.x1 as f32, b.y0 as f32, b.y1 as f32, b.z0 as f32, b.z1 as f32);
            let faces: [([f32; 3], [[f32; 3]; 4], [f32; 3], f32); 5] = [
                ([1.0, 0.0, 0.0], [[x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [x1, y0, z1]], col, 1.0),
                ([-1.0, 0.0, 0.0], [[x0, y1, z0], [x0, y0, z0], [x0, y0, z1], [x0, y1, z1]], col, 1.0),
                ([0.0, 1.0, 0.0], [[x1, y1, z0], [x0, y1, z0], [x0, y1, z1], [x1, y1, z1]], col, 1.0),
                ([0.0, -1.0, 0.0], [[x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1]], col, 1.0),
                ([0.0, 0.0, 1.0], [[x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1]], roof, 0.0),
            ];
            for (n, q, c, wflag) in faces {
                let base = bv.len() as u32;
                for p in q {
                    bv.push(SV { pos: p, nrm: n, col: c, uv: [0.5, 0.5], win: wflag });
                }
                bi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
            }
        }
        let mk = |ctx: &mut dyn mq::RenderingBackend, v: &[SV], i: &[u32], img: mq::TextureId| mq::Bindings {
            vertex_buffers: vec![ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(v))],
            index_buffer: ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(i)),
            images: vec![img],
        };
        let terr = mk(ctx, &tv, &ti, tex);
        let bld = mk(ctx, &bv, &bi, white);
        let shader = ctx
            .new_shader(
                match ctx.info().backend {
                    mq::Backend::Metal => mq::ShaderSource::Msl { program: CLASSIC_MSL },
                    mq::Backend::OpenGl => mq::ShaderSource::Glsl { vertex: VS, fragment: FS },
                },
                mq::ShaderMeta {
                    images: vec!["tex".to_string()],
                    uniforms: mq::UniformBlockLayout {
                        uniforms: vec![
                            mq::UniformDesc::new("mvp", mq::UniformType::Mat4),
                            mq::UniformDesc::new("cam", mq::UniformType::Float3),
                            mq::UniformDesc::new("sun", mq::UniformType::Float3),
                            mq::UniformDesc::new("fog", mq::UniformType::Float3),
                            mq::UniformDesc::new("dens", mq::UniformType::Float1),
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
        StaticScene { pipe, terr, terr_n: ti.len() as i32, bld, bld_n: bi.len() as i32 }
    }

    fn draw(&self, cam: &Camera3D) {
        let mut gl = unsafe { get_internal_gl() };
        gl.flush();
        let ctx = gl.quad_context;
        let u = SU {
            mvp: cam.matrix().to_cols_array(),
            cam: cam.position.to_array(),
            sun: sun_n().to_array(),
            fog: FOG,
            dens: 1.0 / 3600.0,
        };
        ctx.begin_default_pass(mq::PassAction::Nothing);
        ctx.apply_pipeline(&self.pipe);
        ctx.apply_bindings(&self.terr);
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, self.terr_n, 1);
        ctx.apply_bindings(&self.bld);
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, self.bld_n, 1);
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

fn draw_aircraft(p: Vec3, (f, l, u): (Vec3, Vec3, Vec3), ctl: &c172::Controls) {
    let m = c172::build(ctl, false);
    let sun = sun_n();
    let verts: Vec<Vertex> = m
        .v
        .iter()
        .map(|a| {
            let wp = p + f * a.pos.x + l * a.pos.y + u * a.pos.z;
            let nw = f * a.nrm.x + l * a.nrm.y + u * a.nrm.z;
            let base = match a.part as i32 {
                6 => [0.08, 0.08, 0.08],
                4 => [0.6, 0.6, 0.62],
                _ => [0.93, 0.93, 0.92],
            };
            let k = 0.5 + 0.55 * nw.dot(sun).max(0.0);
            Vertex::new(wp.x, wp.y, wp.z, 0.0, 0.0, Color::new((base[0] * k).min(1.0), (base[1] * k).min(1.0), (base[2] * k).min(1.0), 1.0))
        })
        .collect();
    for chunk in m.i.chunks(60_000 / 3 * 3) {
        let lo = *chunk.iter().min().unwrap();
        let hi = *chunk.iter().max().unwrap();
        draw_mesh(&Mesh {
            vertices: verts[lo as usize..=hi as usize].to_vec(),
            indices: chunk.iter().map(|&x| (x - lo) as u16).collect(),
            texture: None,
        });
    }
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
    mismatch: bool,
    kamikaze: Option<Kamikaze>,
    /// Replays a harness hostile-pilot episode (`--episode N`).
    hostile: Option<Hostile>,
    /// Scripted Tower gap pilot (`Y`, `--showcase`).
    showcase: Option<Showcase>,
    /// Fly-by camera position, re-placed ahead of the aircraft once it has passed.
    flyby: Option<Vec3>,
    crash_logged: bool,
    show_paths: bool,
    show_help: bool,
    cam_mode: usize,
    invert: bool,
    stick: (f64, f64),
    acc: f64,
    /// The aircraft and its control surfaces as drawn between ticks, and the `sim.k` they were last pushed at.
    drawn: Drawn,
    drawn_ctl: [(c172::Controls, f32); 2],
    drawn_k: Option<u64>,
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
    /// 0 = classic, 1 = photoreal.
    renderer: usize,
    /// Photoreal sun elevation and azimuth, degrees.
    sun_el: f32,
    sun_az: f32,
    prop_angle: f32,
    /// Footage-realism post stack (L).
    footage: bool,
    /// Lens preset (O), focal length and f-stop (N/J, Z/X).
    lens: usize,
    focal_mm: f32,
    fstop: f32,
    /// Caption pill for demos (`--label`).
    label: Option<String>,
}

/// (name, focal length mm, f-stop, hexagonal aperture, cat's-eye strength, tilt-shift).
const LENSES: [(&str, f32, f32, bool, f32, bool); 5] = [
    ("24mm f/2.8", 24.0, 2.8, false, 0.0, false),
    ("200mm f/2 hex bokeh", 200.0, 2.0, true, 0.35, false),
    ("50mm f/0.95", 50.0, 0.95, false, 0.5, false),
    ("tilt-shift miniature", 24.0, 8.0, false, 0.0, true),
    ("cinematic 50mm f/4", 50.0, 4.0, false, 0.2, false),
];
const LENS_CINEMATIC: usize = 4;

const CAM_NAMES: [&str; 5] = ["chase", "cockpit", "orbit", "overhead", "fly-by"];
const RENDERER_NAMES: [&str; 3] = ["classic", "photoreal", "ray traced"];

/// Clickable filter toggle, just under the instrument panel.
fn filter_button() -> Rect {
    Rect::new(16.0, 277.0, 300.0, 42.0)
}

impl App {
    fn cfg(&self, filter_on: bool) -> SimCfg {
        SimCfg { filter_on, filter: FilterCfg { phase: self.phase, robust: self.robust }, mismatch: self.mismatch, seed: self.seed }
    }

    fn reset(&mut self, scenario: usize) {
        self.scenario = scenario;
        self.seed += 1;
        self.hostile = None;
        self.flyby = None;
        self.showcase = if scenario == 4 && self.showcase.is_some() { Some(Showcase::new(street_x(GAP_STREET))) } else { None };
        self.crash_logged = false;
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
        if is_key_pressed(KeyCode::B) {
            self.show_paths = !self.show_paths;
        }
        if is_key_pressed(KeyCode::M) {
            self.mismatch = !self.mismatch;
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
            self.cam_mode = (self.cam_mode + 1) % CAM_NAMES.len();
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
            self.showcase = None;
            if self.kamikaze.is_none() {
                self.fbw = Fbw { thr: self.fbw.thr, ..Fbw::from_state(&self.sim.s) };
            }
        }
        if is_key_pressed(KeyCode::R) {
            self.reset(self.scenario);
        }
        for (key, id) in [(KeyCode::Key1, 0), (KeyCode::Key2, 1), (KeyCode::Key3, 2), (KeyCode::Key4, 3), (KeyCode::Key5, 4)] {
            if is_key_pressed(key) {
                self.reset(id);
            }
        }
        if is_key_pressed(KeyCode::Y) {
            self.start_showcase(self.showcase.is_none());
        }
        if is_key_pressed(KeyCode::T) {
            self.toggle_harness();
        }
        if is_key_down(KeyCode::Comma) {
            self.sun_el = (self.sun_el - 12.0 * dt as f32).max(-4.0);
        }
        if is_key_down(KeyCode::Period) {
            self.sun_el = (self.sun_el + 12.0 * dt as f32).min(89.0);
        }
        if is_key_down(KeyCode::Semicolon) {
            self.sun_az -= 30.0 * dt as f32;
        }
        if is_key_down(KeyCode::Apostrophe) {
            self.sun_az += 30.0 * dt as f32;
        }
        if is_key_pressed(KeyCode::V) && !use_gl() {
            self.renderer = (self.renderer + 1) % 3;
        }
    }

    /// After each tick: record what is drawn between ticks (`Drawn`); start over if the sim was replaced.
    fn push_drawn(&mut self) {
        let ctl = self.tick_surfaces();
        if self.drawn_k.is_some_and(|k| k + STEPS_PER_TICK == self.sim.k) {
            self.drawn.push(&self.sim);
            self.drawn_ctl = [self.drawn_ctl[1], ctl];
        } else {
            self.drawn = Drawn::new(&self.sim);
            self.drawn_ctl = [ctl, ctl];
        }
        self.drawn_k = Some(self.sim.k);
    }

    /// The aircraft state to draw this frame: between the last two ticks at the accumulated fraction of a tick,
    /// or the sim's own state if no tick has run since the sim was (re)built.
    fn drawn_state(&self) -> State {
        if self.drawn_k == Some(self.sim.k) {
            self.drawn.at(self.acc / DT_F)
        } else {
            Drawn::of(&self.sim)
        }
    }

    /// Body axes with the nose raised by the angle of attack the load factor needs: the same frame the
    /// gate's wing clearance (`World::airframe_clearance`) checks.
    fn aircraft_axes(&self) -> (Vec3, Vec3, Vec3) {
        let s = &self.drawn_state();
        let a = airframe_axes(s, drawn_alpha(&self.sim.prm_true, s));
        let v = |x: [f64; 3]| vec3(x[0] as f32, x[1] as f32, x[2] as f32);
        (v(a[0]), v(a[1]), v(a[2]))
    }

    /// Control-surface deflections and engine rpm as drawn: between the last two ticks, like `drawn_state`.
    fn surfaces(&self) -> (c172::Controls, f32) {
        if self.drawn_k != Some(self.sim.k) {
            return self.tick_surfaces();
        }
        let t = (self.acc / DT_F).clamp(0.0, 1.0) as f32;
        let ([(a, ra), (b, rb)], l) = (self.drawn_ctl, |x: f32, y: f32| x + (y - x) * t);
        (c172::Controls { elevator: l(a.elevator, b.elevator), aileron: l(a.aileron, b.aileron), rudder: l(a.rudder, b.rudder) }, l(ra, rb))
    }

    /// Control-surface deflections (trailing edge down, rad) and engine rpm after the latest tick.
    fn tick_surfaces(&self) -> (c172::Controls, f32) {
        #[cfg(feature = "jsb")]
        if let Some(j) = &self.sim.jsb {
            let sf = j.surf;
            let c = c172::Controls { elevator: (sf[0] * 0.40) as f32, aileron: (sf[1] * 0.35) as f32, rudder: (sf[2] * 0.28) as f32 };
            return (c, j.obs.rpm as f32);
        }
        let s = &self.sim.s;
        let u = self.sim.applied;
        let pm = &self.sim.prm_true;
        let elev = -(0.12 * (u[0] - 1.0) + 0.5 * (u[0] - s[N])).clamp(-1.0, 1.0) * 0.40;
        let ail = -(u[1] / pm.p_max).clamp(-1.0, 1.0) * 0.35;
        let c = c172::Controls { elevator: elev as f32, aileron: ail as f32, rudder: (ail * 0.25) as f32 };
        (c, (800.0 + 1600.0 * s[THR]) as f32)
    }

    /// Nav, strobe and landing lights: glow sprites, plus the landing spot and nav point lights for the shaders.
    fn aircraft_lights(&self, ov: &mut Vec<photo::DV>, oi: &mut Vec<u32>, cam: Vec3, right: Vec3, up: Vec3) -> ([f32; 4], [f32; 4], [[f32; 4]; 3]) {
        let p = sv3(&self.drawn_state());
        let (f, l, u) = self.aircraft_axes();
        let to_w = |q: Vec3| p + f * q.x + l * q.y + u * q.z;
        let t = get_time() as f32;
        let strobe = if (t * 1.1).fract() < 0.05 { 1.0 } else { 0.0 };
        let navs = [(vec3(0.1, 5.47, 1.07), [3.0, 0.15, 0.08]), (vec3(0.1, -5.47, 1.07), [0.15, 3.0, 0.6]), (vec3(-5.78, 0.0, 0.36), [2.5, 2.5, 2.5])];
        let mut nav = [[0.0f32; 4]; 3];
        for (k, (q, c)) in navs.iter().enumerate() {
            let w = to_w(*q);
            let r = (0.12 + (w - cam).length() * 0.0015).min(1.5);
            if self.cam_mode != 1 {
                photo::glow(ov, oi, w, r, [c[0], c[1], c[2], 1.0], right, up);
                if k < 2 && strobe > 0.0 {
                    photo::glow(ov, oi, w, r * 2.5, [60.0, 60.0, 60.0, 1.0], right, up);
                }
            }
            nav[k] = [w.x, w.y, w.z, 3.0];
        }
        let lp = to_w(vec3(0.55, 1.9, 0.86));
        let ld = (f * 0.99 - u * 0.09).normalize();
        if self.cam_mode != 1 && (cam - lp).normalize().dot(ld) > 0.85 {
            photo::glow(ov, oi, lp, 0.4 + (lp - cam).length() * 0.002, [30.0, 28.0, 25.0, 1.0], right, up);
        }
        (lp.extend(1500.0).to_array(), ld.extend(13f32.to_radians().cos()).to_array(), nav)
    }

    fn sun_dir(&self) -> Vec3 {
        let (el, az) = (self.sun_el.to_radians(), self.sun_az.to_radians());
        vec3(el.cos() * az.cos(), el.cos() * az.sin(), el.sin())
    }

    /// Tower gap with the scripted showcase pilot and the escape paths on (or back to manual flying).
    fn start_showcase(&mut self, on: bool) {
        self.kamikaze = None;
        self.showcase = on.then(|| Showcase::new(street_x(GAP_STREET)));
        if on {
            self.show_paths = true;
            self.reset(4);
        } else {
            self.fbw = Fbw { thr: self.fbw.thr, ..Fbw::from_state(&self.sim.s) };
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
            let opts = HarnessOpts { episodes: 200, threads, kamikaze_secs: 300.0, extended: false };
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
        let omega = self.surfaces().1 / 60.0 * std::f32::consts::TAU;
        self.prop_angle = (self.prop_angle + omega * dt as f32) % std::f32::consts::TAU;
        let mut n = 0;
        while self.acc >= DT_F && n < 10 {
            self.acc -= DT_F;
            n += 1;
            if let Some(sc) = &mut self.showcase {
                sc.update(&self.sim.s, &mut self.fbw, DT_F);
            } else if let Some(k) = &mut self.kamikaze {
                k.update(self.world, &self.sim.s, &mut self.fbw, DT_F);
            } else if let Some(h) = &mut self.hostile {
                h.update(&mut self.fbw, DT_F);
            } else {
                self.fbw.sticks(self.stick.0, self.stick.1, DT_F);
            }
            let u = self.fbw.cmd(&self.sim.prm_ctrl, &self.sim.s);
            self.sim.tick(u);
            self.push_drawn();
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
                if !self.crash_logged {
                    self.crash_logged = true;
                    eprintln!("crashed at t={:.1} s", self.sim.time());
                }
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
        #[cfg(feature = "jsb")]
        if cityflight::envfilter::kind().is_some() {
            let v3f = |q: &[f64; 3]| vec3(q[0] as f32, q[1] as f32, q[2] as f32);
            self.paths.clear();
            self.plan_path.clear();
            if let Some(g) = &self.sim.env_gate {
                // Green/red: the latest rollout and its verdict; yellow: the committed escape's verified path.
                if self.show_paths {
                    self.paths.push((g.shown.iter().map(v3f).collect(), g.shown_ok));
                }
                if g.law.is_some() {
                    self.plan_path = g.committed_path.iter().map(v3f).collect();
                }
                return;
            }
            self.plan_path = self.sim.env_pred.iter().map(v3f).collect();
            if self.show_paths {
                if let Some(p) = &self.sim.jsb {
                    let r = cityflight::envfilter::rollout(self.world, p, self.sim.env_dir, usize::MAX);
                    self.paths.push((r.path.iter().chain(r.tail.iter()).map(v3f).collect(), r.ok()));
                }
            }
            return;
        }
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
                pred.rollout(&s, hold, pl.esc, te, pl.psi0, f64::NEG_INFINITY, Some(&mut p));
                self.plan_path = p.iter().map(|q| v3(*q)).collect();
            }
        }
    }

    fn camera(&mut self, dt: f32) -> Camera3D {
        let s = &self.drawn_state();
        let p = sv3(s);
        let (f, _, _) = body_axes(s);
        let fh = vec3(f.x, f.y, 0.0).normalize_or_zero();
        let (pos, target, up) = match self.cam_mode {
            1 => {
                let (f, l, u) = self.aircraft_axes();
                let e = p + f * c172::EYE.x + l * c172::EYE.y + u * c172::EYE.z;
                (e, e + f * 300.0 - u * 50.0, u)
            }
            2 => {
                self.orbit += dt * 0.25;
                (p + vec3(self.orbit.cos() * 70.0, self.orbit.sin() * 70.0, 22.0), p, Vec3::Z)
            }
            3 => (p + vec3(0.0, 0.0, 650.0) - fh * 250.0, p + fh * 60.0, Vec3::Z),
            4 => {
                // Fly-by: a fixed spot ahead, a little to the side and below, re-placed once passed.
                let passed = self.flyby.map_or(true, |c| (p - c).dot(fh) > 70.0 || (p - c).length() > 450.0);
                if passed && !self.sim.crashed {
                    let side = vec3(-fh.y, fh.x, 0.0);
                    let ahead = p + fh * 200.0;
                    let mut best = ahead;
                    for off in [10.0f32, -10.0, 6.0, -6.0, 3.0, -3.0, 0.0] {
                        let q = ahead + side * off - vec3(0.0, 0.0, 9.0);
                        let ground = self.world.terrain(q.x as f64, q.y as f64) as f32 + 2.0;
                        let q = vec3(q.x, q.y, q.z.max(ground));
                        if self.world.building_dist([q.x as f64, q.y as f64, q.z as f64], 3.0) >= 3.0 {
                            best = q;
                            break;
                        }
                    }
                    self.flyby = Some(best);
                }
                (self.flyby.unwrap_or(p - fh * 30.0), p + f * 4.0, Vec3::Z)
            }
            _ => {
                let zoom = (self.focal_mm / 24.0).sqrt().clamp(1.0, 4.0);
                let desired = p - (f * 24.0 + fh * 6.0 - vec3(0.0, 0.0, 7.0)) * zoom;
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
        let mut target = target;
        if self.footage && self.renderer >= 1 {
            let t = get_time() as f32;
            let fwd = (target - pos).normalize_or_zero();
            let right = fwd.cross(up).normalize_or_zero();
            let upv = right.cross(fwd);
            let n = |a: f32, b: f32| (t * a).sin() * 0.6 + (t * b + 1.3).sin() * 0.4;
            let amp = if self.cam_mode == 1 { 0.006 } else { 0.0035 };
            let buzz = if self.cam_mode == 1 { (t * 71.0).sin() * 0.0008 } else { 0.0 };
            let d = (target - pos).length();
            target += (right * n(3.1, 7.7) + upv * (n(2.3, 5.9) + buzz)) * amp * d;
        }
        let fovy = if self.renderer >= 1 { 2.0 * (12.0 / self.focal_mm).atan() } else { 1.0 };
        Camera3D { position: pos, target, up, fovy, z_near: 0.5, z_far: 16000.0, ..Default::default() }
    }

    fn draw_sky(&self, cam: &Camera3D) {
        set_default_camera();
        let (w, h) = (screen_width(), screen_height());
        let fwd = (cam.target - cam.position).normalize_or_zero();
        let fh = vec3(fwd.x, fwd.y, 0.0).normalize_or_zero();
        let far = cam.position + fh * 8000.0;
        let clip = cam.matrix() * far.extend(1.0);
        let hy = if clip.w > 0.0 { (1.0 - (clip.y / clip.w)) * 0.5 * h } else { h * 0.5 };
        let hy = hy.clamp(-h, 2.0 * h);
        let fog = Color::new(FOG[0], FOG[1], FOG[2], 1.0);
        let verts = vec![
            Vertex::new(0.0, hy - h * 0.9, 0.0, 0.0, 0.0, SKY_TOP),
            Vertex::new(w, hy - h * 0.9, 0.0, 0.0, 0.0, SKY_TOP),
            Vertex::new(w, hy, 0.0, 0.0, 0.0, fog),
            Vertex::new(0.0, hy, 0.0, 0.0, 0.0, fog),
        ];
        draw_rectangle(0.0, 0.0, w, (hy - h * 0.9).max(0.0), SKY_TOP);
        draw_mesh(&Mesh { vertices: verts, indices: vec![0, 1, 2, 0, 2, 3], texture: None });
        draw_rectangle(0.0, hy, w, (h - hy).max(0.0), fog);
    }

    fn draw_world_dynamic(&self, cam: &Camera3D) {
        set_camera(cam);
        let s = &self.drawn_state();
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
            draw_aircraft(p, self.aircraft_axes(), &self.surfaces().0);
        }
    }

    /// Aircraft (lit) and overlays (unlit, colours preserved through the tonemap) for the photoreal renderer.
    fn photo_dynamic(&self, cam: Vec3, exposure: f32) -> (Vec<photo::DV>, Vec<u32>, Vec<photo::DV>, Vec<u32>) {
        use photo::DV;
        let s = &self.drawn_state();
        let p = sv3(s);
        let (mut lv, mut li) = (Vec::new(), Vec::new());
        let (f, l, u) = self.aircraft_axes();
        let cockpit = self.cam_mode == 1;
        let m = c172::build(&self.surfaces().0, cockpit);
        let to_w = |q: Vec3| p + f * q.x + l * q.y + u * q.z;
        for a in &m.v {
            let wp = to_w(a.pos);
            let nw = f * a.nrm.x + l * a.nrm.y + u * a.nrm.z;
            lv.push(DV { pos: wp.to_array(), nrm: nw.to_array(), col: [1.0; 4], mat: [photo::K_AIRCRAFT, 0.0, 0.0, 0.0], loc: [a.pos.x, a.pos.y, a.pos.z, a.part] });
        }
        li.extend_from_slice(&m.i);
        let (mut ov, mut oi) = (Vec::new(), Vec::new());
        let to_scene = |c: Color| -> [f32; 4] {
            [photo::display_to_scene(c.r, exposure), photo::display_to_scene(c.g, exposure), photo::display_to_scene(c.b, exposure), c.a]
        };
        let mut ribbon_dv = |pts: &[Vec3], cols: &[Color], width: f32| {
            if pts.len() < 2 {
                return;
            }
            for i in 0..pts.len() {
                let a = pts[i.saturating_sub(1)];
                let b = pts[(i + 1).min(pts.len() - 1)];
                let dir = (b - a).normalize_or_zero();
                let view = (cam - pts[i]).normalize_or_zero();
                let side = dir.cross(view).normalize_or_zero() * (width * 0.5);
                let c = to_scene(cols[i.min(cols.len() - 1)]);
                let base = ov.len() as u32;
                for q in [pts[i] - side, pts[i] + side] {
                    ov.push(DV { pos: q.to_array(), nrm: [0.0; 3], col: c, mat: [photo::K_OVERLAY, 0.0, 0.0, 0.0], loc: [0.0; 4] });
                }
                if i > 0 {
                    oi.extend_from_slice(&[base - 2, base - 1, base + 1, base - 2, base + 1, base]);
                }
            }
        };
        let pts: Vec<Vec3> = self.trail.iter().map(|t| t.0).chain(std::iter::once(p)).collect();
        let cols: Vec<Color> = self.trail.iter().map(|t| t.1).collect();
        if !cols.is_empty() {
            ribbon_dv(&pts, &cols, 1.6);
        }
        if self.show_paths {
            for (path, ok) in &self.paths {
                let c = if *ok { Color::new(0.2, 0.95, 0.35, 0.8) } else { Color::new(1.0, 0.2, 0.2, 0.8) };
                ribbon_dv(path, &[c], 1.3);
            }
            if !self.plan_path.is_empty() {
                ribbon_dv(&self.plan_path, &[Color::new(1.0, 0.85, 0.2, 0.95)], 2.2);
            }
        }
        if let Some(k) = &self.kamikaze {
            let t = vec3(k.target[0] as f32, k.target[1] as f32, k.target[2] as f32);
            let pulse = 0.5 + 0.5 * (get_time() as f32 * 6.0).sin();
            let r = 6.0 + 4.0 * pulse;
            let c = Color::new(1.0, 0.1, 0.1, 0.6);
            for i in 0..8 {
                let a = i as f32 / 8.0 * std::f32::consts::PI;
                let ring: Vec<Vec3> = (0..=24).map(|j| {
                    let b = j as f32 / 24.0 * std::f32::consts::TAU;
                    t + r * vec3(b.cos() * a.sin(), b.sin() * a.sin(), a.cos())
                }).collect();
                ribbon_dv(&ring, &[c], r * 0.4);
            }
            ribbon_dv(&[t, t + vec3(0.0, 0.0, 120.0)], &[Color::new(1.0, 0.2, 0.2, 0.8)], 0.6);
        }
        let base = ov.len() as u32;
        for q in c172::prop_disc() {
            ov.push(DV { pos: to_w(q).to_array(), nrm: f.to_array(), col: [1.0; 4], mat: [photo::K_AIRCRAFT, 0.0, 0.0, 0.0], loc: [q.x, q.y, q.z, c172::P_PROP] });
        }
        oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
        (lv, li, ov, oi)
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
        // Exact-rollout filters (`--env`): filter name, escape (committed or verified) and check time.
        #[allow(unused_mut)]
        let mut env: Option<(String, &str, f64, bool)> = None;
        #[cfg(feature = "jsb")]
        if let (Some(k), Some(g)) = (cityflight::envfilter::kind(), &self.sim.env_gate) {
            let e = g.law.or(g.witness).map(|l| l.esc);
            env = Some((format!("{k:?} exact rollout").to_lowercase(), e.map_or("none verified", |i| cityflight::envfilter::ESCAPES[i].name), *g.cpu_ms.last().unwrap_or(&0.0) as f64, g.witness.is_some() || g.law.is_some()));
        }
        let (h_txt, esc, ms) = match &env {
            Some((_, e, ms, ok)) => ((if *ok { "verified" } else { "none verified" }).to_string(), *e, *ms),
            None => (h_txt, esc, fs.ms),
        };
        let rows: Vec<(&str, String)> = vec![
            ("AIRSPEED", format!("{:.1} m/s  {:.0} kt", s[V], s[V] * 1.94384)),
            ("HEIGHT AGL", format!("{:.0} m", agl)),
            ("THROTTLE", format!("{:.0} %", s[THR] * 100.0)),
            ("PATH / BANK", format!("{:+.1}°  {:+.0}°", s[GAM].to_degrees(), -s[PHI].to_degrees())),
            ("h  BARRIER", h_txt),
            ("BLEND λ", if on { format!("{:.2}", if fs.mode == Mode::Commit { 1.0 } else { fs.lam }) } else { "-".into() }),
            ("ESCAPE", esc.to_string()),
            ("FILTER TIME", if on { format!("{:.2} ms/tick", ms) } else { "-".into() }),
            ("TRUE CLEARANCE", format!("{:.1} m", self.sim.true_clear)),
            ("MIN CLEARANCE", format!("{:.1} m", self.sim.min_true_clear)),
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
                Mode::Commit if env.is_some() => format!("COMMITTED ESCAPE · {esc}"),
                Mode::Commit => format!("COMMITTED ESCAPE · {}", fs.act_esc.map(|i| ESC_NAMES[i]).unwrap_or("-")),
                Mode::Blend => format!("blending {:.0} %", fs.lam * 100.0),
                _ => "pilot in control".to_string(),
            };
            let phase = match &env {
                Some((name, ..)) => name.clone(),
                None => format!("{}{}", self.phase.name(), if self.robust { " + P3 robust" } else { "" }),
            };
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
        if let Some(l) = &self.label {
            pills.push((l.clone(), Color::new(0.12, 0.14, 0.2, 0.92), WHITE));
        }
        if self.mismatch {
            pills.push(("MISMATCH: wind + weaker aircraft".into(), Color::new(0.55, 0.25, 0.7, 0.92), WHITE));
        }
        if self.kamikaze.is_some() {
            pills.push(("KAMIKAZE AUTOPILOT".into(), Color::new(0.6, 0.05, 0.05, 0.92), WHITE));
        }
        if let Some(sc) = &self.showcase {
            let what = ["SHOWCASE PILOT · threading the gap", "SHOWCASE PILOT · turning into the tower", "SHOWCASE PILOT · levelled off"];
            pills.push((what[sc.phase() as usize].into(), Color::new(0.15, 0.3, 0.65, 0.92), WHITE));
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
            "{} · H help · Space filter · B escapes · C camera ({}) · V renderer ({}) · 1-5 scenarios · Y showcase · K kamikaze · T harness · R reset",
            SCENARIOS[self.scenario],
            CAM_NAMES[self.cam_mode],
            RENDERER_NAMES[self.renderer]
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
        let lines: [(&str, &str); 22] = [
            ("W/S  ↑/↓", "pitch (stick forward = nose down; I inverts)"),
            ("A/D  ←/→", "roll · release the keys to hold flight path and bank"),
            ("Q / E", "throttle down / up"),
            ("Space", "safety filter on / off"),
            ("F", "filter: P1 blend+commit · P2 closed-form · permissive"),
            ("G", "Phase 3 robust margins on / off"),
            ("B", "show escape paths (green valid, red not, yellow committed)"),
            ("M", "model mismatch: wind and a weaker, slower aircraft"),
            ("C", "camera: chase · cockpit · orbit · overhead · fly-by"),
            ("1 2 3 4 5", "tower run · dive · ridge · slow and low · tower gap"),
            ("Y", "tower gap with the scripted showcase pilot (threads the gap, turns into a tower)"),
            ("K", "kamikaze autopilot (flies at buildings and terrain)"),
            ("T", "run the 200-episode headless harness"),
            ("R", "reset the scenario"),
            ("V", "renderer: classic · photoreal · ray traced (Metal RT + MetalFX)"),
            (", .  ; '", "photoreal sun: elevation down / up, azimuth"),
            ("P  [ ]  - =  9 0", "weather preset · fog density · fog height · fog anisotropy"),
            ("L  O  Z/X  N/J", "footage look · lens preset · f-stop · focal length"),
            ("6", "cinematic: fly-by camera, clear weather, 50 mm f/4"),
            ("U", "ray traced: MetalFX denoiser on / off"),
            ("H / Esc", "toggle / close this help"),
            ("", ""),
        ];
        let ph = 150.0 + lines.len() as f32 * 24.0;
        let (x, y) = ((w - pw) * 0.5, (h - ph) * 0.5);
        draw_rectangle(x, y, pw, ph, Color::new(0.03, 0.05, 0.08, 0.9));
        ui.text("Backup-CBF City Flight", x + 24.0, y + 40.0, 26.0, WHITE, false);
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
        let warn1 = "The guarantee holds only under the nominal model with full state knowledge.";
        let warn2 = "With mismatch on (M) it no longer strictly holds; the harness measures what happens.";
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

/// Photoreal knobs: P weather preset, [ ] fog density, - = fog height, 9 0 fog anisotropy.
fn photo_keys(app: &mut App, ph: &mut photo::Photo) {
    if is_key_pressed(KeyCode::Key6) {
        set_cinematic(app, ph);
    }
    if is_key_pressed(KeyCode::U) {
        ph.settings.rt_denoiser = !ph.settings.rt_denoiser;
    }
    if is_key_pressed(KeyCode::L) {
        app.footage = !app.footage;
    }
    if is_key_pressed(KeyCode::O) {
        app.lens = (app.lens + 1) % LENSES.len();
        app.focal_mm = LENSES[app.lens].1;
        app.fstop = LENSES[app.lens].2;
    }
    if is_key_pressed(KeyCode::Z) {
        app.fstop = (app.fstop / 1.4142).max(0.7);
    }
    if is_key_pressed(KeyCode::X) {
        app.fstop = (app.fstop * 1.4142).min(22.0);
    }
    if is_key_pressed(KeyCode::J) {
        app.focal_mm = (app.focal_mm * 1.25).min(200.0);
    }
    if is_key_pressed(KeyCode::N) {
        app.focal_mm = (app.focal_mm / 1.25).max(14.0);
    }
    let f = &mut ph.settings.fog;
    if is_key_pressed(KeyCode::P) {
        ph.settings.preset = (ph.settings.preset + 1) % photo::PRESETS.len();
        set_preset(app, ph, ph.settings.preset);
        return;
    }
    if is_key_pressed(KeyCode::RightBracket) {
        f.density *= 1.4;
    }
    if is_key_pressed(KeyCode::LeftBracket) {
        f.density /= 1.4;
    }
    if is_key_pressed(KeyCode::Equal) {
        f.falloff *= 1.3;
    }
    if is_key_pressed(KeyCode::Minus) {
        f.falloff /= 1.3;
    }
    if is_key_pressed(KeyCode::Key0) {
        f.anisotropy = (f.anisotropy + 0.05).min(0.95);
    }
    if is_key_pressed(KeyCode::Key9) {
        f.anisotropy = (f.anisotropy - 0.05).max(-0.5);
    }
}

/// Cinematic look: fly-by camera, clear weather, a 50 mm lens at f/4 focused on the aircraft (subtle bokeh).
fn set_cinematic(app: &mut App, ph: &mut photo::Photo) {
    app.cam_mode = 4;
    app.flyby = None;
    app.footage = false;
    app.lens = LENS_CINEMATIC;
    app.focal_mm = LENSES[LENS_CINEMATIC].1;
    app.fstop = LENSES[LENS_CINEMATIC].2;
    set_preset(app, ph, 0);
}

fn set_preset(app: &mut App, ph: &mut photo::Photo, k: usize) {
    let (_, fog, el, az) = photo::PRESETS[k];
    ph.settings.preset = k;
    ph.settings.fog = fog;
    app.sun_el = el;
    app.sun_az = az;
}

#[macroquad::main(window_conf)]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)).cloned();
    let shot = arg("--shot");
    let shot_frames: u32 = arg("--frames").and_then(|s| s.parse().ok()).unwrap_or(90);
    #[cfg(feature = "jsb")]
    if args.iter().any(|a| a == "--jsb") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    // The gate checks its escapes in parallel (one thread each, the verdict independent of how many) instead of
    // under a wall-clock cap, so what flies does not depend on how busy the machine is. `--time-cap MS` brings
    // the cap back; `--check-threads 0` the budgeted sequential check.
    #[cfg(feature = "jsb")]
    cityflight::envfilter::TIME_CAP_MS.store(arg("--time-cap").and_then(|s| s.parse().ok()).unwrap_or(0), std::sync::atomic::Ordering::Relaxed);
    #[cfg(feature = "jsb")]
    cityflight::envfilter::CHECK_THREADS.store(
        arg("--check-threads").and_then(|s| s.parse().ok()).unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(1, |n| n.get().saturating_sub(1)).clamp(1, cityflight::envfilter::N_ESC)
        }),
        std::sync::atomic::Ordering::Relaxed,
    );
    #[cfg(feature = "jsb")]
    if let Some(l) = arg("--law") {
        cityflight::envfilter::LAW_SEL.store(cityflight::envfilter::parse_law(&l), std::sync::atomic::Ordering::Relaxed);
    }
    #[cfg(feature = "jsb")]
    if let Some(m) = arg("--margin").and_then(|s| s.parse::<f64>().ok()) {
        cityflight::envfilter::set_filter_margin(m, arg("--check-every").and_then(|s| s.parse().ok()).unwrap_or(cityflight::envfilter::SAMPLE));
    }
    #[cfg(feature = "jsb")]
    if let Some(n) = arg("--escapes").and_then(|s| s.parse().ok()) {
        cityflight::envfilter::N_USED.store(n, std::sync::atomic::Ordering::Relaxed);
    }
    #[cfg(feature = "jsb")]
    if let Some(f) = arg("--env") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
        cityflight::envfilter::ENV_FILTER.store(cityflight::envfilter::parse(&f), std::sync::atomic::Ordering::Relaxed);
        if matches!(cityflight::envfilter::kind(), Some(cityflight::envfilter::Kind::Fitted { .. })) {
            cityflight::envfilter::table();
        }
    }

    clear_background(Color::new(FOG[0], FOG[1], FOG[2], 1.0));
    next_frame().await;
    let world: &'static World = Box::leak(Box::new(World::new(1337)));
    let terrain_px = terrain_texture(world);
    let scene = StaticScene::new(world, &terrain_px);
    let mut photo = if use_gl() { None } else { Some(photo::Photo::new(world)) };
    drop(terrain_px);
    let ui = Ui {
        mono: load_font(&["/System/Library/Fonts/SFNSMono.ttf", "/System/Library/Fonts/Menlo.ttc"]),
        sans: load_font(&["/System/Library/Fonts/SFNS.ttf", "/System/Library/Fonts/Helvetica.ttc"]),
    };
    let scenario: usize = arg("--scenario").and_then(|s| s.parse::<usize>().ok()).map(|s| s.clamp(1, SCENARIOS.len()) - 1).unwrap_or(0);
    let s0 = scenario_start(world, scenario);
    let sim = Sim::new(world, s0, SimCfg::default());
    let drawn = Drawn::new(&sim);
    let mut app = App {
        world,
        sim,
        fbw: Fbw::from_state(&s0),
        scenario,
        phase: Phase::P1,
        robust: false,
        mismatch: false,
        kamikaze: None,
        hostile: None,
        showcase: None,
        flyby: None,
        crash_logged: false,
        show_paths: args.iter().any(|a| a == "--paths"),
        show_help: shot.is_none(),
        cam_mode: arg("--cam").and_then(|s| s.parse().ok()).unwrap_or(0),
        invert: false,
        stick: (0.0, 0.0),
        acc: 0.0,
        drawn,
        drawn_ctl: [(c172::Controls::default(), 0.0); 2],
        drawn_k: None,
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
        prop_angle: 0.0,
        footage: args.iter().any(|a| a == "--footage"),
        lens: 0,
        focal_mm: LENSES[0].1,
        fstop: LENSES[0].2,
        sun_el: SUN[2].asin().to_degrees(),
        sun_az: SUN[1].atan2(SUN[0]).to_degrees(),
        label: None,
        renderer: match (photo.is_some(), args.iter().any(|a| a == "--classic"), args.iter().any(|a| a == "--rt")) {
            (true, false, true) => 2,
            (true, false, false) => 1,
            _ => 0,
        },
    };
    app.reset(scenario);
    if let (Some(k), Some(ph)) = (arg("--preset").and_then(|s| s.parse::<usize>().ok()), photo.as_mut()) {
        set_preset(&mut app, ph, k.min(photo::PRESETS.len() - 1));
    }
    if let (true, Some(ph)) = (args.iter().any(|a| a == "--cinematic"), photo.as_mut()) {
        set_cinematic(&mut app, ph);
    }
    if let Some(c) = arg("--cam").and_then(|s| s.parse().ok()) {
        app.cam_mode = c;
    }
    if let (Some(s), Some(ph)) = (arg("--fog"), photo.as_mut()) {
        let v: Vec<f32> = s.split(',').filter_map(|x| x.parse().ok()).collect();
        let f = &mut ph.settings.fog;
        for (k, x) in v.iter().enumerate() {
            match k {
                0 => f.density = *x,
                1 => f.falloff = *x,
                _ => f.anisotropy = *x,
            }
        }
    }
    if let Some(ph) = photo.as_mut() {
        ph.settings.rt_denoiser = args.iter().any(|a| a == "--rt-denoiser");
        if let Some(s) = arg("--rt-scale").and_then(|s| s.parse::<f32>().ok()) {
            ph.settings.rt_scale = s.clamp(0.25, 1.0);
        }
    }
    if let Some(k) = arg("--lens").and_then(|s| s.parse::<usize>().ok()) {
        app.lens = k.min(LENSES.len() - 1);
        app.focal_mm = LENSES[app.lens].1;
        app.fstop = LENSES[app.lens].2;
    }
    if let Some(s) = arg("--sun") {
        let v: Vec<f32> = s.split(',').filter_map(|x| x.parse().ok()).collect();
        if let Some(&el) = v.first() {
            app.sun_el = el;
        }
        if let Some(&az) = v.get(1) {
            app.sun_az = az;
        }
    }
    if args.iter().any(|a| a == "--kamikaze") {
        app.kamikaze = Some(Kamikaze::new(app.seed));
    }
    if args.iter().any(|a| a == "--showcase") {
        app.start_showcase(true);
    }
    // Same start, seed and pilot as the harness: episodes 0.. are random starts (every fourth a kamikaze
    // pilot), 1000 + i is scenario i + 1 with a kamikaze pilot.
    if let Some(e) = arg("--episode").and_then(|s| s.parse::<u64>().ok()) {
        let (s0, kami) = if e >= 1000 {
            (scenario_start(world, ((e - 1000) as usize).min(SCENARIOS.len() - 1)), true)
        } else {
            let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xE915);
            (random_start(world, &mut rng), e % 4 == 3)
        };
        app.seed = e;
        app.sim = Sim::new(world, s0, app.cfg(true));
        app.fbw = Fbw::from_state(&s0);
        app.kamikaze = if kami { Some(Kamikaze::new(e)) } else { None };
        app.hostile = if kami { None } else { Some(Hostile::new(e)) };
        app.trail.clear();
        let (f, _, _) = body_axes(&s0);
        app.cam_pos = sv3(&s0) - f * 30.0 + vec3(0.0, 0.0, 8.0);
    }
    // Boundary-regime demos: a given start (`--start x,y,z,v,gamma°,heading°,bank°,throttle`), optionally moved
    // back `--lead S` seconds along its velocity, flown by the released sticks (holding flight path and bank).
    #[cfg(feature = "jsb")]
    if let Some(s0) = arg("--start").and_then(|a| cityflight::regimes::parse_start(&a)) {
        let s0 = cityflight::regimes::lead_state(&s0, arg("--lead").and_then(|s| s.parse().ok()).unwrap_or(0.0));
        app.sim = Sim::new(world, s0, app.cfg(true));
        app.fbw = Fbw::from_state(&app.sim.s);
        app.kamikaze = None;
        app.hostile = None;
        app.showcase = None;
        app.trail.clear();
        let (f, _, _) = body_axes(&s0);
        app.cam_pos = sv3(&s0) - f * 30.0 + vec3(0.0, 0.0, 8.0);
    }
    app.label = arg("--label");
    if args.iter().any(|a| a == "--off") {
        app.sim.set_filter(false);
    }
    let mut frame = 0u32;
    let mut perf = (0.0f64, 0u32, 0.0f64, 0.0f64);
    let mut perf_t = std::time::Instant::now();
    loop {
        let loop_start = std::time::Instant::now();
        let dt = get_frame_time().min(0.1) as f64;
        if shot.is_none() {
            app.input(dt);
            if let Some(ph) = photo.as_mut() {
                photo_keys(&mut app, ph);
            }
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
        match (app.renderer, photo.as_mut()) {
            (1 | 2, Some(ph)) => {
                let (lv, li, mut ov, mut oi) = app.photo_dynamic(cam.position, 1.0);
                let night = (1.0 - (app.sun_el + 4.0) / 10.0).clamp(0.0, 1.0);
                let fwd = (cam.target - cam.position).normalize();
                let right = fwd.cross(cam.up).normalize();
                let up = right.cross(fwd);
                ph.lamp_sprites(&mut ov, &mut oi, cam.position, right, up, night);
                let lights = app.aircraft_lights(&mut ov, &mut oi, cam.position, right, up);
                ph.draw(&photo::FrameIn {
                    cam_pos: cam.position,
                    cam_target: cam.target,
                    cam_up: cam.up,
                    fovy: cam.fovy,
                    sun: app.sun_dir(),
                    time: get_time() as f32,
                    dyn_lit: (&lv, &li),
                    dyn_overlay: (&ov, &oi),
                    prop: if app.footage {
                        [app.prop_angle, app.surfaces().1 / 60.0 * std::f32::consts::TAU, 0.9 / 60.0, 1.0 / 480.0]
                    } else {
                        [app.prop_angle, app.surfaces().1 / 60.0 * std::f32::consts::TAU, 0.0, 1.0 / 120.0]
                    },
                    lens: photo::Lens {
                        focus: if app.cam_mode == 1 { 400.0 } else { (sv3(&app.drawn_state()) - cam.position).length().max(2.0) },
                        focal_mm: app.focal_mm,
                        fstop: app.fstop,
                        tilt_shift: LENSES[app.lens].5,
                        cats_eye: LENSES[app.lens].4,
                        hexagon: LENSES[app.lens].3,
                        footage: app.footage,
                        shutter: 90.0,
                        frame_dt: if shot.is_some() { 1.0 / 60.0 } else { dt as f32 },
                    },
                    cockpit: app.cam_mode == 1,
                    rt: app.renderer == 2,
                    model: {
                        let (f, l, u) = app.aircraft_axes();
                        [sv3(&app.drawn_state()), f, l, u]
                    },
                    land_pos: lights.0,
                    land_dir: lights.1,
                    nav: lights.2,
                });
            }
            _ => {
                app.draw_sky(&cam);
                scene.draw(&cam);
                app.draw_world_dynamic(&cam);
            }
        }
        set_default_camera();
        app.draw_tint();
        app.draw_hud(&ui);

        frame += 1;
        let metal = !use_gl();
        if shot.is_some() {
            let now = std::time::Instant::now();
            if frame > 10 {
                perf.0 += now.duration_since(perf_t).as_secs_f64();
                perf.1 += 1;
                perf.3 += now.duration_since(loop_start).as_secs_f64() * 1000.0;
                if metal {
                    perf.2 += unsafe { get_internal_gl() }.quad_context.as_metal().map(|m| m.last_gpu_ms()).unwrap_or(0.0);
                }
            }
            perf_t = now;
        }
        if let Some(path) = &shot {
            if frame >= shot_frames {
                let n = perf.1.max(1) as f64;
                eprintln!(
                    "perf: {:.1} fps (wall, vsync-capped), gpu {:.2} ms/frame, cpu {:.2} ms/frame over {} frames, {}",
                    n / perf.0.max(1e-9),
                    perf.2 / n,
                    perf.3 / n,
                    perf.1,
                    RENDERER_NAMES[app.renderer]
                );
                if metal {
                    unsafe { get_internal_gl() }.quad_context.as_metal().unwrap().request_capture();
                    next_frame().await;
                    let cap = unsafe { get_internal_gl() }.quad_context.as_metal().unwrap().take_capture();
                    if let Some((w, h, px)) = cap {
                        photo::save_capture(path, w, h, px);
                    } else {
                        eprintln!("capture failed");
                    }
                } else {
                    get_screen_data().export_png(path);
                }
                break;
            }
        }
        next_frame().await;
    }
}
