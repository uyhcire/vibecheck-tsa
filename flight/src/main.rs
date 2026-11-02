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
mod gun;
mod hotas;
mod photo;
mod rt;
mod sfscene;
mod shaders;

use cityflight::combat::{self, Dogfight, FxKind, HITS_TO_KILL};
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
/// San Francisco's sun matches the aerial photo's shadows, so the rendered ones fall the same way.
const SF_SUN: [f32; 3] = [0.40, -0.50, 0.77];
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

/// Photoreal sun elevation and azimuth (degrees) on a map.
fn sun_angles(map: MapId) -> (f32, f32) {
    let s = if map == MapId::SanFrancisco { SF_SUN } else { SUN };
    let n = (s[0] * s[0] + s[1] * s[1] + s[2] * s[2]).sqrt();
    ((s[2] / n).asin().to_degrees(), s[1].atan2(s[0]).to_degrees())
}

/// One map's world and the GPU scenes built for it (once, on first use).
struct MapScenes {
    world: &'static World,
    scene: StaticScene,
    photo: Option<photo::Photo>,
}

impl MapScenes {
    fn new(world: World) -> MapScenes {
        let world: &'static World = Box::leak(Box::new(world));
        let (terrain_px, tw, th) = terrain_texture(world);
        let scene = StaticScene::new(world, &terrain_px, tw, th);
        let photo = if use_gl() { None } else { Some(photo::Photo::new(world)) };
        MapScenes { world, scene, photo }
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

/// The classic renderer's ground texture over the map, with its width and height.
fn terrain_texture(w: &World) -> (Vec<u8>, usize, usize) {
    if w.map == MapId::SanFrancisco {
        return sfscene::painted_ground(w);
    }
    let mut px = vec![0u8; TEX * TEX * 4];
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let rows_per = TEX.div_ceil(threads);
    std::thread::scope(|sc| {
        for (ci, chunk) in px.chunks_mut(rows_per * TEX * 4).enumerate() {
            sc.spawn(move || {
                for (ri, row) in chunk.chunks_mut(TEX * 4).enumerate() {
                    let py = ci * rows_per + ri;
                    let y = -GRID_HALF + (py as f64 + 0.5) * 2.0 * GRID_HALF / TEX as f64;
                    for i in 0..TEX {
                        let x = -GRID_HALF + (i as f64 + 0.5) * 2.0 * GRID_HALF / TEX as f64;
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
    (px, TEX, TEX)
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
    fn new(w: &World, px: &[u8], tw: usize, th: usize) -> StaticScene {
        let InternalGlContext { quad_context: ctx, .. } = unsafe { get_internal_gl() };
        // Terrain: same vertices and triangle split as the collision truth.
        let (tnx, tny) = (w.tnx, w.tny);
        let mut tv = Vec::with_capacity(tnx * tny);
        for j in 0..tny {
            for i in 0..tnx {
                let x = w.x0 + i as f64 * TSP;
                let y = w.y0 + j as f64 * TSP;
                let hh = |a: usize, b: usize| w.terr[b.min(tny - 1) * tnx + a.min(tnx - 1)];
                let dx = hh(i + 1, j) - hh(i.saturating_sub(1), j);
                let dy = hh(i, j + 1) - hh(i, j.saturating_sub(1));
                let n = vec3(-dx, -dy, 2.0 * TSP as f32).normalize();
                tv.push(SV {
                    pos: [x as f32, y as f32, w.terr[j * tnx + i]],
                    nrm: [n.x, n.y, n.z],
                    col: [1.0, 1.0, 1.0],
                    uv: [((x - w.x0) / (w.x1 - w.x0)) as f32, ((y - w.y0) / (w.y1 - w.y0)) as f32],
                    win: 0.0,
                });
            }
        }
        let mut ti: Vec<u32> = Vec::with_capacity((tnx - 1) * (tny - 1) * 6);
        for j in 0..tny - 1 {
            for i in 0..tnx - 1 {
                let a = (j * tnx + i) as u32;
                let b = a + 1;
                let c = a + tnx as u32 + 1;
                let d = a + tnx as u32;
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
                width: tw as u32,
                height: th as u32,
                allocate_mipmaps: true,
                ..Default::default()
            },
        );
        ctx.texture_generate_mipmaps(tex);
        let white = ctx.new_texture_from_rgba8(1, 1, &[255, 255, 255, 255]);

        // Buildings: five faces per box.
        let mut bv: Vec<SV> = Vec::with_capacity(w.boxes.len() * 20);
        let mut bi: Vec<u32> = Vec::with_capacity(w.boxes.len() * 30);
        // A wall per footprint edge plus the roof (a box is four walls). Bridge and freeway collision
        // curtains are not drawn.
        for b in w.boxes.iter().filter(|b| matches!(b.kind, Kind::Building | Kind::BridgeTower | Kind::GoldenGate)) {
            let col = building_color(b);
            let roof = [col[0] * 0.62 + 0.08, col[1] * 0.62 + 0.08, col[2] * 0.62 + 0.09];
            let (z0, z1) = (b.z0 as f32, b.z1 as f32);
            let wflag = if b.kind == Kind::Building { 1.0 } else { 0.0 };
            let poly = w.outline(b);
            for e in 0..poly.len() {
                let (p, q) = (poly[e], poly[(e + 1) % poly.len()]);
                let (ex, ey) = ((q[0] - p[0]) as f32, (q[1] - p[1]) as f32);
                let l = (ex * ex + ey * ey).sqrt().max(1e-4);
                let (px, py, qx, qy) = (p[0] as f32, p[1] as f32, q[0] as f32, q[1] as f32);
                let base = bv.len() as u32;
                for pos in [[px, py, z0], [qx, qy, z0], [qx, qy, z1], [px, py, z1]] {
                    bv.push(SV { pos, nrm: [ey / l, -ex / l, 0.0], col, uv: [0.5, 0.5], win: wflag });
                }
                bi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
            }
            let base = bv.len() as u32;
            for p in &poly {
                bv.push(SV { pos: [p[0] as f32, p[1] as f32, z1], nrm: [0.0, 0.0, 1.0], col: roof, uv: [0.5, 0.5], win: 0.0 });
            }
            for t in 1..poly.len().saturating_sub(1) as u32 {
                bi.extend_from_slice(&[base, base + t, base + t + 1]);
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
        self.draw_into(cam, None);
    }

    /// Draw into `pass` (the window if `None`), over what is there.
    fn draw_into(&self, cam: &Camera3D, pass: Option<mq::RenderPass>) {
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
        match pass {
            Some(p) => ctx.begin_pass(Some(p), mq::PassAction::Nothing),
            None => ctx.begin_default_pass(mq::PassAction::Nothing),
        }
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
        // macroquad clamps a draw call at 5,000 indices.
        if idx.len() + 6 >= 5000 {
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

fn draw_aircraft(p: Vec3, (f, l, u): (Vec3, Vec3, Vec3), ctl: &c172::Controls, tint: [f32; 3], fly: bool) {
    let m = c172::build(ctl, false);
    let sun = sun_n();
    let verts: Vec<Vertex> = m
        .v
        .iter()
        .map(|a| {
            let wp = p + f * a.pos.x + l * a.pos.y + u * a.pos.z;
            let nw = f * a.nrm.x + l * a.nrm.y + u * a.nrm.z;
            let base = if fly {
                fly_paint(a.part, a.pos)
            } else {
                match a.part as i32 {
                    6 => [0.08, 0.08, 0.08],
                    4 => [0.6, 0.6, 0.62],
                    _ => [0.93, 0.93, 0.92],
                }
            };
            let k = 0.5 + 0.55 * nw.dot(sun).max(0.0);
            let c = |i: usize| (base[i] * tint[i] * k).min(1.0);
            Vertex::new(wp.x, wp.y, wp.z, 0.0, 0.0, Color::new(c(0), c(1), c(2), 1.0))
        })
        .collect();
    // macroquad clamps a draw call at 5,000 indices: whole triangles under that.
    for chunk in m.i.chunks(4998) {
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

fn dv3(p: [f64; 3]) -> Vec3 {
    vec3(p[0] as f32, p[1] as f32, p[2] as f32)
}

/// Screen position of a world point, or `None` behind the camera.
fn project(cam: &Camera3D, p: Vec3) -> Option<Vec2> {
    let c = cam.matrix() * p.extend(1.0);
    (c.w > 0.1).then(|| vec2((c.x / c.w + 1.0) * 0.5 * screen_width(), (1.0 - c.y / c.w) * 0.5 * screen_height()))
}

/// Camera-facing quad for the photoreal overlay pass: kind 8 is a soft disc in display colour, kind 9 an HDR glow
/// that falls to zero at the quad's edge.
fn sprite(ov: &mut Vec<photo::DV>, oi: &mut Vec<u32>, c: Vec3, r: f32, col: [f32; 4], kind: f32, right: Vec3, up: Vec3) {
    let base = ov.len() as u32;
    for (sx, sy) in [(-1.0f32, -1.0f32), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)] {
        let p = c + (right * sx + up * sy) * r;
        ov.push(photo::DV { pos: p.to_array(), nrm: [0.0; 3], col, mat: [kind, 0.0, 0.0, 0.0], loc: [sx, sy, 0.0, 0.0] });
    }
    oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
}

/// A tracer: a kind-9 glow stretched from `a` to `b`, facing the camera.
fn streak(ov: &mut Vec<photo::DV>, oi: &mut Vec<u32>, a: Vec3, b: Vec3, width: f32, col: [f32; 4], cam: Vec3) {
    let side = (b - a).cross(cam - (a + b) * 0.5).normalize_or_zero() * (width * 0.5);
    let base = ov.len() as u32;
    for (p, l) in [(a - side, [-1.0, -1.0]), (b - side, [1.0, -1.0]), (b + side, [1.0, 1.0]), (a + side, [-1.0, 1.0])] {
        ov.push(photo::DV { pos: p.to_array(), nrm: [0.0; 3], col, mat: [9.0, 0.0, 0.0, 0.0], loc: [l[0], l[1], 0.0, 0.0] });
    }
    oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
}

/// The gun cross with an aura: a soft radial glow, a halo ring and glowing arms; hot (orange, pulsing) when the
/// lead pipper sits on it.
fn glow_cross(q: Vec2, hot: bool, t: f32) {
    let (col, k) = if hot { (Color::new(1.0, 0.45, 0.15, 1.0), 1.0 + 0.2 * (t * 14.0).sin()) } else { (Color::new(1.0, 0.85, 0.3, 1.0), 1.0) };
    let boost = if hot { 1.8 } else { 1.0 };
    for i in 0..16 {
        let f = i as f32 / 16.0;
        draw_circle(q.x, q.y, (72.0 - 60.0 * f) * k, Color { a: (0.018 + 0.05 * f * f) * boost, ..col });
    }
    let r = 21.0 * k;
    for (w, a) in [(14.0, 0.07), (8.0, 0.14), (4.0, 0.3)] {
        draw_circle_lines(q.x, q.y, r, w, Color { a: a * boost, ..col });
    }
    draw_circle_lines(q.x, q.y, r, 1.5, Color { a: 0.95, ..col });
    for (w, a) in [(12.0, 0.10), (7.0, 0.2), (4.0, 0.35), (2.0, 1.0)] {
        let c = Color { a: a * if w > 2.0 { boost } else { 1.0 }, ..col };
        for (dx, dy) in [(1.0, 0.0), (-1.0, 0.0), (0.0, 1.0), (0.0, -1.0)] {
            draw_line(q.x + dx * 5.0, q.y + dy * 5.0, q.x + dx * 15.0 * k, q.y + dy * 15.0 * k, w, c);
        }
    }
    draw_circle(q.x, q.y, 6.0, Color { a: 0.2 * boost, ..col });
    draw_circle(q.x, q.y, 3.5, Color { a: 0.4 * boost, ..col });
    draw_circle(q.x, q.y, 1.6, col);
}

/// The fly's paint for the classic renderer (the photoreal one paints it in its shader, `mat.y` = 1): a tan
/// thorax, a banded abdomen, red compound eyes over the cabin, smoky wings and dark legs (struts).
fn fly_paint(part: f32, q: Vec3) -> [f32; 3] {
    let (tan, dark) = ([0.62, 0.42, 0.18], [0.1, 0.07, 0.05]);
    let wing = [0.55, 0.58, 0.64];
    let eye = |c: Vec3| ((q - c) / vec3(0.8, 0.3, 0.42)).length_squared() < 1.0;
    match part as i32 {
        1 => wing,
        3 if q.y.abs() > 2.2 => wing,
        4 | 6 => dark,
        _ if eye(vec3(0.95, 0.42, 0.5)) || eye(vec3(0.95, -0.42, 0.5)) => [0.7, 0.05, 0.03],
        _ if q.x < -0.9 && (q.x * 1.25).rem_euclid(1.0) < 0.4 => dark,
        _ => tan,
    }
}

/// A camera's view and projection without its render target (`Camera3D` is not `Clone`).
fn cam_copy(c: &Camera3D) -> Camera3D {
    Camera3D { position: c.position, target: c.target, up: c.up, fovy: c.fovy, aspect: c.aspect, z_near: c.z_near, z_far: c.z_far, ..Default::default() }
}

/// Viridis (matplotlib's), from its eleven tenth-steps: the fly panel's colour for firing and saliency.
fn viridis(t: f32) -> Color {
    const V: [[f32; 3]; 11] = [
        [0.267, 0.005, 0.329],
        [0.282, 0.141, 0.459],
        [0.255, 0.267, 0.529],
        [0.208, 0.373, 0.553],
        [0.165, 0.471, 0.557],
        [0.129, 0.569, 0.549],
        [0.133, 0.659, 0.518],
        [0.267, 0.749, 0.439],
        [0.478, 0.820, 0.318],
        [0.741, 0.875, 0.149],
        [0.993, 0.906, 0.144],
    ];
    let x = t.clamp(0.0, 1.0) * 10.0;
    let (i, f) = ((x as usize).min(9), x - (x as usize).min(9) as f32);
    let c: [f32; 3] = std::array::from_fn(|k| V[i][k] + (V[i + 1][k] - V[i][k]) * f);
    Color::new(c[0], c[1], c[2], 1.0)
}

/// The fly brain for the dogfight, with saliency on (it costs a backward pass on 3 ticks in 10).
fn gui_brain() -> Option<cityflight::flybrain::Brain> {
    let mut b = cityflight::flybrain::Brain::load_default()?;
    b.saliency_on = true;
    Some(b)
}

/// Size of the fly panel, which is also the fly's view (logical px).
const FLY_VIEW: (f32, f32) = (470.0, 470.0);

/// A sky sphere around `c` for offscreen views (the window's sky is a screen-space gradient): fog colour at and
/// below the horizon, the zenith colour above.
fn sky_dome(c: Vec3) {
    let (rings, segs, r) = (10usize, 24usize, 9000.0f32);
    let fog = Color::new(FOG[0], FOG[1], FOG[2], 1.0);
    let mut verts = Vec::new();
    let mut idx: Vec<u16> = Vec::new();
    for i in 0..=rings {
        let el = -0.5 * std::f32::consts::PI + std::f32::consts::PI * i as f32 / rings as f32;
        let t = (el / 1.0).clamp(0.0, 1.0).powf(0.7);
        let col = Color::new(fog.r + (SKY_TOP.r - fog.r) * t, fog.g + (SKY_TOP.g - fog.g) * t, fog.b + (SKY_TOP.b - fog.b) * t, 1.0);
        for j in 0..=segs {
            let az = std::f32::consts::TAU * j as f32 / segs as f32;
            let p = c + vec3(el.cos() * az.cos(), el.cos() * az.sin(), el.sin()) * r;
            verts.push(Vertex::new(p.x, p.y, p.z, 0.0, 0.0, col));
            if i > 0 && j > 0 {
                let (a, b) = (((i - 1) * (segs + 1) + j - 1) as u16, (i * (segs + 1) + j - 1) as u16);
                idx.extend_from_slice(&[a, b, b + 1, a, b + 1, a + 1]);
            }
        }
    }
    draw_mesh(&Mesh { vertices: verts, indices: idx, texture: None });
}

/// Both aircraft darken with hits.
fn damage_tint(base: [f32; 3], hits: u32) -> [f32; 3] {
    let k = 1.0 - 0.55 * (hits as f32 / HITS_TO_KILL as f32).min(1.0);
    base.map(|c| c * k)
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
    /// Tab pressed: switch to the other map before the next frame.
    switch_map: bool,
    show_paths: bool,
    /// Wingtip anti-collision strobes (off by default; `--strobes` or key 7).
    strobes: bool,
    show_help: bool,
    cam_mode: usize,
    invert: bool,
    stick: (f64, f64),
    hotas: hotas::Hotas,
    /// The HOTAS report seen last frame (`None`: no stick yet), for lever moves and button presses.
    hotas_prev: Option<hotas::Sticks>,
    /// Cosmetic guns (`gun.rs`); `trigger` is Shift or the HOTAS trigger held this frame, `fire_hold` is `--fire`.
    guns: gun::Guns,
    trigger: bool,
    fire_hold: bool,
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
    /// Dogfight: a fly hunting the player. It starts when the trigger is pulled in normal flight (if
    /// `fly_summon`, toggled with 8); during it the trigger fires the dogfight's guns instead of the cosmetic ones.
    dogfight: Option<Dogfight>,
    fly_summon: bool,
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

const CAM_NAMES: [&str; 6] = ["chase", "cockpit", "orbit", "overhead", "fly-by", "fly cam"];
const RENDERER_NAMES: [&str; 3] = ["classic", "photoreal", "ray traced"];

/// Clickable filter toggle, just under the instrument panel.
fn filter_button() -> Rect {
    Rect::new(16.0, 277.0, 300.0, 42.0)
}

impl App {
    fn cfg(&self, filter_on: bool) -> SimCfg {
        SimCfg { filter_on, filter: FilterCfg { phase: self.phase, robust: self.robust }, wind: self.mismatch, model_error: self.mismatch, seed: self.seed }
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
        self.guns.clear();
        self.paths.clear();
        self.plan_path.clear();
        self.acc = 0.0;
        self.stick = (0.0, 0.0);
        if self.kamikaze.is_some() {
            self.kamikaze = Some(Kamikaze::new(self.seed));
        }
        // Back to normal flight: the next pull of the trigger summons a new fly.
        self.dogfight = None;
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
        // HOTAS: the stick sets pitch and roll unless a key is held; the lever sets the throttle when it
        // moves, so Q/E and a reset's throttle hold until then.
        let hs = self.hotas.get();
        let prev = std::mem::replace(&mut self.hotas_prev, hs);
        let mut hotas_pressed = 0;
        if let Some(hs) = hs {
            if prev.is_none() {
                eprintln!("HOTAS: stick connected");
            }
            if !down(KeyCode::W, KeyCode::Up) && !down(KeyCode::S, KeyCode::Down) {
                let p = hotas::deadzone(hs.pitch, 0.1);
                self.stick.0 = if self.invert { -p } else { p };
            }
            if !down(KeyCode::A, KeyCode::Left) && !down(KeyCode::D, KeyCode::Right) {
                self.stick.1 = hotas::deadzone(hs.roll, 0.1);
            }
            if prev.is_some_and(|p| p.throttle != hs.throttle) {
                self.fbw.thr = hs.throttle;
            }
            hotas_pressed = hs.buttons & !prev.map_or(0, |p| p.buttons);
        }
        // Guns: for as long as Shift or the trigger is held.
        self.trigger = down(KeyCode::LeftShift, KeyCode::RightShift) || hs.is_some_and(|h| h.buttons & hotas::BTN_TRIGGER != 0);
        let clicked = is_mouse_button_pressed(MouseButton::Left) && filter_button().contains(mouse_position().into());
        if is_key_pressed(KeyCode::Space) || clicked || hotas_pressed & hotas::BTN_FILTER != 0 {
            let on = !self.sim.cfg.filter_on;
            self.sim.set_filter(on);
        }
        if is_key_pressed(KeyCode::B) {
            self.show_paths = !self.show_paths;
        }
        if is_key_pressed(KeyCode::Key7) {
            self.strobes = !self.strobes;
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
        if is_key_pressed(KeyCode::K) || hotas_pressed & hotas::BTN_KAMIKAZE != 0 {
            self.kamikaze = if self.kamikaze.is_some() { None } else { Some(Kamikaze::new(self.seed)) };
            self.showcase = None;
            if self.kamikaze.is_none() {
                self.fbw = Fbw { thr: self.fbw.thr, ..Fbw::from_state(&self.sim.s) };
            }
        }
        if is_key_pressed(KeyCode::R) {
            self.reset(self.scenario);
        }
        let scenarios = scenario_names(self.world.map).len();
        for (key, id) in [(KeyCode::Key1, 0), (KeyCode::Key2, 1), (KeyCode::Key3, 2), (KeyCode::Key4, 3), (KeyCode::Key5, 4)] {
            if is_key_pressed(key) && id < scenarios {
                self.reset(id);
            }
        }
        if is_key_pressed(KeyCode::Tab) {
            self.switch_map = true;
        }
        if is_key_pressed(KeyCode::Y) && self.world.map == MapId::Grid {
            self.start_showcase(self.showcase.is_none());
        }
        if is_key_pressed(KeyCode::T) {
            self.toggle_harness();
        }
        if is_key_pressed(KeyCode::Key8) {
            self.fly_summon = !self.fly_summon;
            if !self.fly_summon {
                self.dogfight = None;
            }
        }
        // Normal flight until the trigger is pulled: then the fly appears and hunts you.
        if self.trigger && self.fly_summon && self.dogfight.is_none() && !self.sim.crashed {
            self.dogfight = Some(Dogfight::new(self.seed, gui_brain()));
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
    /// The aircraft has crashed and gone in the explosion's fireball: draw no aircraft and no lights.
    fn wrecked(&self) -> bool {
        self.sim.crashed && self.guns.boom_age().map_or(true, |a| a > gun::SWALLOWED)
    }

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
        let jsb_surf = self.sim.jsb.as_ref().map(|j| (j.surf, j.obs.rpm)).or(self.sim.lean.as_ref().map(|g| (g.surf, g.obs.rpm)));
        #[cfg(feature = "jsb")]
        if let Some((sf, rpm)) = jsb_surf {
            let c = c172::Controls { elevator: (sf[0] * 0.40) as f32, aileron: (sf[1] * 0.35) as f32, rudder: (sf[2] * 0.28) as f32 };
            return (c, rpm as f32);
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
        if self.player_dead() {
            return ([0.0; 4], [0.0, 0.0, -1.0, 1.0], [[0.0; 4]; 3]);
        }
        let p = sv3(&self.drawn_state());
        let (f, l, u) = self.aircraft_axes();
        let to_w = |q: Vec3| p + f * q.x + l * q.y + u * q.z;
        let t = get_time() as f32;
        // Real C172 wingtip strobes: about 66 flashes a minute, about 50 ms each; nav lights stay steady.
        let strobe = if self.strobes && (t * 1.1).fract() < 0.05 { 1.0 } else { 0.0 };
        let navs = [(vec3(0.1, 5.47, 1.07), [3.0, 0.15, 0.08]), (vec3(0.1, -5.47, 1.07), [0.15, 3.0, 0.6]), (vec3(-5.78, 0.0, 0.36), [2.5, 2.5, 2.5])];
        let mut nav = [[0.0f32; 4]; 3];
        let shown = self.cam_mode != 1 && !self.wrecked();
        let on = if self.wrecked() { 0.0 } else { 1.0 };
        for (k, (q, c)) in navs.iter().enumerate() {
            let w = to_w(*q);
            let r = (0.12 + (w - cam).length() * 0.0015).min(1.5);
            if shown {
                photo::glow(ov, oi, w, r, [c[0], c[1], c[2], 1.0], right, up);
                if k < 2 && strobe > 0.0 {
                    photo::glow(ov, oi, w, r * 1.5, [12.0, 12.0, 12.0, 1.0], right, up);
                }
            }
            nav[k] = [w.x, w.y, w.z, 3.0 * on];
        }
        let lp = to_w(vec3(0.55, 1.9, 0.86));
        let ld = (f * 0.99 - u * 0.09).normalize();
        if shown && (cam - lp).normalize().dot(ld) > 0.85 {
            photo::glow(ov, oi, lp, 0.4 + (lp - cam).length() * 0.002, [30.0, 28.0, 25.0, 1.0], right, up);
        }
        (lp.extend(1500.0 * on).to_array(), ld.extend(13f32.to_radians().cos()).to_array(), nav)
    }

    fn player_dead(&self) -> bool {
        self.dogfight.as_ref().is_some_and(|d| d.player_dead)
    }

    fn player_tint(&self) -> [f32; 3] {
        damage_tint([1.0; 3], self.dogfight.as_ref().map_or(0, |d| d.player_hits))
    }

    /// The bandit as drawn this frame (between its last two ticks), its body axes and its paint.
    fn bandit_drawn(&self) -> Option<(Vec3, (Vec3, Vec3, Vec3), [f32; 3])> {
        let b = self.dogfight.as_ref()?.bandit.as_ref()?;
        let t = (self.acc / DT_F).clamp(0.0, 1.0);
        let s: State = std::array::from_fn(|i| b.prev[i] + (b.s[i] - b.prev[i]) * t);
        let a = airframe_axes(&s, drawn_alpha(&combat::bandit_params(), &s));
        let v = |x: [f64; 3]| vec3(x[0] as f32, x[1] as f32, x[2] as f32);
        Some((sv3(&s), (v(a[0]), v(a[1]), v(a[2])), damage_tint([1.0; 3], b.hits)))
    }

    /// Render the fly's view (from its eye, banking with it) into `rt` with the classic renderer: sky, city, the
    /// player's aircraft, tracers and smoke. `None` when there is no fly brain or no fly in the air.
    fn render_fly_view(&self, scene: &StaticScene, rt: &RenderTarget) -> Option<Camera3D> {
        self.dogfight.as_ref()?.brain.as_ref()?;
        let (bp, (bf, _, bu), _) = self.bandit_drawn()?;
        let eye = bp + bf * 1.5 + bu * 1.2;
        let cam = Camera3D {
            position: eye,
            target: eye + bf * 100.0,
            up: bu,
            fovy: 1.1,
            aspect: Some(FLY_VIEW.0 / FLY_VIEW.1),
            z_near: 0.5,
            z_far: 16000.0,
            render_target: Some(rt.clone()),
            ..Default::default()
        };
        let pass = rt.render_pass.raw_miniquad_id();
        {
            // Not `clear_background`, which would drop the frame's pending draws.
            let mut gl = unsafe { get_internal_gl() };
            gl.flush();
            gl.quad_context.begin_pass(Some(pass), mq::PassAction::clear_color(FOG[0], FOG[1], FOG[2], 1.0));
            gl.quad_context.end_render_pass();
        }
        set_camera(&cam);
        sky_dome(eye);
        scene.draw_into(&cam, Some(pass));
        if !self.player_dead() {
            draw_aircraft(sv3(&self.drawn_state()), self.aircraft_axes(), &self.surfaces().0, self.player_tint(), false);
        }
        self.draw_combat_classic(&cam);
        set_default_camera();
        Some(cam)
    }

    /// The fly panel, one square: the fly's view (from its eye) behind everything; on it, saliency (how strongly
    /// each LC10's input moves the brain's bank, climb and fire, at that LC10's receptive field); over that, every
    /// neuron at its place in the brain lit by its firing, the strongest wiring, the fly's gun reticle and a
    /// bracket on the player; along the bottom, what the descending neurons decode to.
    fn draw_fly_panel(&self, ui: &Ui, br: &cityflight::flybrain::Brain, view: Option<(&RenderTarget, &Camera3D)>) {
        let (w, h) = (screen_width(), screen_height());
        let (pw, ph) = FLY_VIEW;
        let (x0, y0) = (w - pw - 14.0, h - 30.0 - ph - 12.0);
        let inside = |q: &Vec2| q.x > x0 && q.x < x0 + pw && q.y > y0 && q.y < y0 + ph;
        let dimw = Color::new(1.0, 1.0, 1.0, 0.65);
        let red = viridis(1.0);
        let fly = self.dogfight.as_ref().and_then(|d| d.bandit.as_ref());
        match view {
            Some((rt, _)) => {
                draw_texture_ex(&rt.texture, x0, y0, WHITE, DrawTextureParams { dest_size: Some(vec2(pw, ph)), ..Default::default() });
                draw_rectangle(x0, y0, pw, ph, Color::new(0.0, 0.0, 0.0, 0.32));
            }
            None => draw_rectangle(x0, y0, pw, ph, Color::new(0.02, 0.03, 0.05, 0.85)),
        }
        draw_rectangle_lines(x0, y0, pw, ph, 1.0, Color::new(1.0, 1.0, 1.0, 0.25));
        // Saliency at each LC10's receptive field, where that direction falls in the fly's view.
        if let (Some((_, fcam)), Some(b)) = (view, fly) {
            let [f, l, u] = airframe_axes(&b.s, 0.0).map(dv3);
            let eye = fcam.position;
            let focal = 0.5 * ph / (0.5 * fcam.fovy).tan();
            let to_px = |p: Vec3| {
                let c = fcam.matrix() * p.extend(1.0);
                (c.w > 0.1).then(|| vec2(x0 + (c.x / c.w + 1.0) * 0.5 * pw, y0 + (1.0 - c.y / c.w) * 0.5 * ph))
            };
            for (a, c) in br.rf_c.iter().enumerate() {
                let Some(q) = to_px(eye + (f * c[0] + l * c[1] + u * c[2]) * 1000.0).filter(|q| inside(q)) else { continue };
                let sal = br.saliency[a].clamp(0.0, 1.0);
                let r = (br.rf_s2[a].sqrt() * focal).clamp(3.0, 60.0);
                draw_circle(q.x, q.y, 1.2, Color::new(1.0, 1.0, 1.0, 0.18));
                if sal > 0.06 {
                    let col = viridis(sal);
                    for (k, rr) in [(0.05, 1.6), (0.09, 1.0), (0.16, 0.55)] {
                        draw_circle(q.x, q.y, r * rr, Color { a: k * (0.4 + sal), ..col });
                    }
                }
            }
            // The fly's guns point along its flight path; the player, bracketed.
            if let Some(q) = to_px(eye + f * 300.0).filter(inside) {
                draw_circle_lines(q.x, q.y, 9.0, 1.5, red);
                for (dx, dy) in [(1.0, 0.0), (-1.0, 0.0), (0.0, 1.0), (0.0, -1.0)] {
                    draw_line(q.x + dx * 12.0, q.y + dy * 12.0, q.x + dx * 18.0, q.y + dy * 18.0, 1.5, red);
                }
            }
            if !self.player_dead() {
                let pp = sv3(&self.sim.s);
                if let Some(q) = to_px(pp).filter(inside) {
                    let cyan = Color::new(0.3, 0.85, 1.0, 1.0);
                    for (sx, sy) in [(-1.0, -1.0), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)] {
                        let c = vec2(q.x + sx * 8.0, q.y + sy * 8.0);
                        draw_line(c.x, c.y, c.x - sx * 4.0, c.y, 1.5, cyan);
                        draw_line(c.x, c.y, c.x, c.y - sy * 4.0, 1.5, cyan);
                    }
                    ui.text(&format!("you {:.0} m", (pp - dv3(combat::pos(&b.s))).length()), q.x + 12.0, q.y + 4.0, 11.0, cyan, true);
                }
            }
        }
        // The brain, as a thumbnail in the bottom right: neurons at their FlyWire positions, lit by firing, and the
        // strongest wiring.
        if let Some(lay) = &br.layout {
            let (tw, th) = (200.0, 132.0);
            let (tx, ty) = (x0 + pw - tw - 8.0, y0 + ph - 84.0 - th - 8.0);
            draw_rectangle(tx, ty, tw, th, Color::new(0.02, 0.03, 0.05, 0.6));
            draw_rectangle_lines(tx, ty, tw, th, 1.0, Color::new(1.0, 1.0, 1.0, 0.2));
            ui.text("brain", tx + 6.0, ty + 13.0, 10.0, dimw, false);
            let (bx, by, bw, bh) = (tx + 6.0, ty + 16.0, tw - 12.0, th - 20.0);
            let (sx, sy) = (lay.hi[0] - lay.lo[0], lay.hi[1] - lay.lo[1]);
            let k = (bw / sx).min(bh / sy);
            let (ox, oy) = (bx + 0.5 * (bw - sx * k), by + 0.5 * (bh - sy * k));
            let at = |v: usize| vec2(ox + (lay.pos[v][0] - lay.lo[0]) * k, oy + (lay.pos[v][1] - lay.lo[1]) * k);
            // Colour is firing on viridis; size tells the classes apart (descending largest, LC10 smallest).
            let (na, ne) = (br.n_aff, br.n_eff);
            let size = |v: usize| if v < na { 0.8 } else if v >= br.n - ne { 1.4 } else { 1.0 };
            let mean = br.activity.iter().sum::<f32>() / br.n as f32;
            let scale = (3.0 * mean).max(0.02);
            let lit = |v: usize| (br.activity[v] / scale).clamp(0.0, 1.0);
            for &(s, d, _) in &lay.edges {
                let b = lit(s as usize);
                let (p, q) = (at(s as usize), at(d as usize));
                draw_line(p.x, p.y, q.x, q.y, 0.7, Color { a: 0.04 + 0.4 * b * b, ..viridis(0.25 + 0.75 * b) });
            }
            for v in 0..br.n {
                let (p, b) = (at(v), lit(v));
                let c = viridis(0.12 + 0.88 * b);
                if b > 0.2 {
                    draw_circle(p.x, p.y, 1.5 + 3.0 * b, Color { a: 0.2 * b, ..c });
                }
                let r = size(v) * (0.55 + 0.5 * b);
                draw_rectangle(p.x - r, p.y - r, 2.0 * r, 2.0 * r, Color { a: 0.45 + 0.55 * b, ..c });
            }
        }
        // Title and legend over a dark band; the motor readout along the bottom.
        draw_rectangle(x0, y0, pw, 30.0, Color::new(0.02, 0.03, 0.05, 0.7));
        ui.text("FLY", x0 + 10.0, y0 + 20.0, 15.0, WHITE, false);
        let sub = format!("view · saliency · FlyGM on FlyWire v783, {} neurons", br.n);
        ui.text(&sub, x0 + 44.0, y0 + 19.0, 12.0, dimw, false);
        if br.last[3] > 0.5 && fly.is_some() {
            ui.text("FIRE", x0 + pw - ui.width("FIRE", 15.0, false) - 10.0, y0 + 20.0, 15.0, viridis(1.0), false);
        }
        if fly.is_none() {
            let t = "fly inbound…";
            ui.text(t, x0 + (pw - ui.width(t, 13.0, false)) * 0.5, y0 + 56.0, 13.0, dimw, false);
        }
        let band = y0 + ph - 84.0;
        draw_rectangle(x0, band, pw, 84.0, Color::new(0.02, 0.03, 0.05, 0.72));
        // Legend: the viridis scale shared by firing and saliency, then the classes by marker size.
        ui.text("quiet", x0 + 10.0, band + 20.0, 11.0, dimw, false);
        let (cx, cw) = (x0 + 12.0 + ui.width("quiet", 11.0, false), 90.0);
        for i in 0..30 {
            let t = i as f32 / 29.0;
            draw_rectangle(cx + 4.0 + t * cw, band + 11.0, cw / 29.0 + 0.5, 9.0, viridis(t));
        }
        ui.text("firing / salient", cx + cw + 10.0, band + 20.0, 11.0, dimw, false);
        let (na, ne) = (br.n_aff, br.n_eff);
        let mut lx = cx + cw + 20.0 + ui.width("firing / salient", 11.0, false);
        for (r, label) in [(0.8, format!("LC10 {na}")), (1.0, format!("central {}", br.n - na - ne)), (1.4, format!("descending {ne}"))] {
            let rr = 2.2 * r;
            draw_rectangle(lx + 3.0 - rr, band + 16.0 - rr, 2.0 * rr, 2.0 * rr, viridis(0.8));
            ui.text(&label, lx + 9.0, band + 20.0, 11.0, dimw, false);
            lx += ui.width(&label, 11.0, false) + 18.0;
        }
        let [bank, climb, thr, _] = br.last;
        let my = band + 34.0;
        let gauge = |x: f32, label: &str, val: f32, signed: bool, text: String| {
            ui.text(label, x, my + 10.0, 11.0, dimw, false);
            let gw = 96.0;
            draw_rectangle(x, my + 16.0, gw, 7.0, Color::new(1.0, 1.0, 1.0, 0.12));
            let c = viridis(0.75);
            if signed {
                let m = x + gw * 0.5;
                let e = m + val.clamp(-1.0, 1.0) * gw * 0.5;
                draw_rectangle(m.min(e), my + 16.0, (e - m).abs(), 7.0, c);
            } else {
                draw_rectangle(x, my + 16.0, gw * val.clamp(0.0, 1.0), 7.0, c);
            }
            ui.text(&text, x + gw + 6.0, my + 24.0, 11.0, WHITE, true);
        };
        let deg = |r: f64| r.to_degrees() as f32;
        let lr = if bank > 0.0 { "L" } else { "R" };
        gauge(x0 + 10.0, "BANK", -deg(bank) / 70.0, true, format!("{:.0}° {lr}", deg(bank).abs()));
        gauge(x0 + 160.0, "CLIMB", deg(climb) / 35.0, true, format!("{:+.0}°", deg(climb)));
        let thr = thr.clamp(0.0, 1.0);
        gauge(x0 + 310.0, "THROTTLE", thr as f32, false, format!("{:.0}%", thr * 100.0));
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
            let opts = HarnessOpts { only: None, episodes: 200, threads, kamikaze_secs: 300.0, extended: false };
            let t0 = std::time::Instant::now();
            let rep = run_harness(world, &opts, &|n, d, t| *p2.lock().unwrap() = (n.to_string(), d, t));
            let text = format!("{}\n{} threads, {:.0} s", format_report(&rep), threads, t0.elapsed().as_secs_f64());
            *r2.lock().unwrap() = Some(text);
        });
        self.harness = Some(HarnessJob { progress, result, visible: true });
    }

    fn step(&mut self, dt: f64) {
        if let Some(d) = &mut self.dogfight {
            d.fx_step(self.world, dt);
        }
        if self.sim.crashed || self.sim.landed {
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
            let prev = self.sim.s;
            self.sim.tick(u);
            if let Some(d) = &mut self.dogfight {
                d.tick(self.world, &prev, &self.sim.s, self.trigger);
                if self.sim.crashed {
                    d.kill_player(&self.sim.s);
                }
                if d.player_dead {
                    self.sim.crashed = true;
                }
            }
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
                    // A dogfight explodes the aircraft itself (`Dogfight::kill_player`).
                    if self.dogfight.is_none() {
                        let s = self.sim.s;
                        self.guns.explode(sv3(&s), body_axes(&s).0 * s[V] as f32);
                    }
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

    /// The guns, once per frame after `step`: cosmetic, fired from the aircraft as drawn, never inside `Sim::tick`.
    fn update_guns(&mut self, dt: f64) {
        let s = self.drawn_state();
        let mount = gun::Mount { p: sv3(&s), axes: self.aircraft_axes(), vel: body_axes(&s).0 * s[V] as f32 };
        // In a dogfight the trigger fires the dogfight's guns (`combat.rs`), not these.
        let held = (self.trigger || self.fire_hold) && !self.sim.crashed && self.dogfight.is_none();
        self.guns.update(self.world, held, dt as f32, &mount);
    }

    fn update_paths(&mut self) {
        #[cfg(feature = "jsb")]
        if let Some(g) = &self.sim.lean {
            // The Lean gate: the held controller's predicted path (the committed escape, or the pilot's candidate).
            self.paths.clear();
            self.plan_path = g.path().iter().map(|q| vec3(q[0] as f32, q[1] as f32, q[2] as f32)).collect();
            return;
        }
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
                pred.rollout(&s, hold, pl.esc, te, pl.eref, f64::NEG_INFINITY, Some(&mut p));
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
            // Chase the dogfight's fly (the player's chase view when there is none).
            5 => match self.bandit_drawn() {
                Some((bp, (bf, _, _), _)) => {
                    let bh = vec3(bf.x, bf.y, 0.0).normalize_or_zero();
                    (bp - bf * 20.0 - bh * 5.0 + vec3(0.0, 0.0, 6.0), bp + bf * 20.0, Vec3::Z)
                }
                None => (p - f * 24.0 - fh * 6.0 + vec3(0.0, 0.0, 7.0), p + f * 25.0, Vec3::Z),
            },
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
        if !self.player_dead() {
            draw_disc(vec3(p.x, p.y, gz), 6.0 + alt * 0.02, Color::new(0.0, 0.0, 0.0, (0.45 - alt * 0.0015).max(0.08)));
        }
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
        if self.cam_mode != 1 && !self.wrecked() {
            draw_aircraft(p, self.aircraft_axes(), &self.surfaces().0, self.player_tint(), false);
        }
        if let Some((bp, axes, tint)) = self.bandit_drawn() {
            draw_aircraft(bp, axes, &c172::Controls::default(), tint, true);
        }
        self.guns.draw(&gun::View::of(cam));
        self.draw_combat_classic(cam);
    }

    /// Tracers and smoke, fire, flashes and debris for the classic renderer.
    fn draw_combat_classic(&self, cam: &Camera3D) {
        let Some(d) = &self.dogfight else { return };
        for b in d.bullets.iter().filter(|b| b.tracer) {
            let p = dv3(b.p);
            let w = 0.35 + (p - cam.position).length() * 0.002;
            ribbon(&[p - dv3(b.v) * 0.03, p], &[Color::new(1.0, 0.8, 0.35, 0.95)], w, cam.position);
        }
        let fwd = (cam.target - cam.position).normalize_or_zero();
        let right = fwd.cross(cam.up).normalize_or_zero();
        let up = right.cross(fwd);
        let mut fx: Vec<_> = d.fx.iter().map(|f| ((dv3(f.p) - cam.position).length_squared(), f)).collect();
        fx.sort_by(|a, b| b.0.total_cmp(&a.0));
        let (mut verts, mut idx): (Vec<Vertex>, Vec<u16>) = (Vec::new(), Vec::new());
        for (_, f) in fx {
            let a = f.strength() as f32;
            let col = match f.kind {
                FxKind::Smoke => {
                    let g = 0.62 - 0.5 * f.shade as f32;
                    Color::new(g, g, g * 1.02, a)
                }
                FxKind::Dust => Color::new(0.55, 0.5, 0.42, a),
                FxKind::Fire => Color::new(1.0, 0.5 + 0.35 * a, 0.12, a),
                FxKind::Flash | FxKind::Spark => Color::new(1.0, 0.92, 0.6, a),
                FxKind::Debris => Color::new(0.08, 0.08, 0.08, 1.0),
            };
            let rim = if f.kind == FxKind::Debris { col } else { Color { a: 0.0, ..col } };
            // macroquad clamps a draw call at 5,000 indices.
            if idx.len() + 30 >= 5000 {
                draw_mesh(&Mesh { vertices: std::mem::take(&mut verts), indices: std::mem::take(&mut idx), texture: None });
            }
            let (c, r, base) = (dv3(f.p), f.radius() as f32, verts.len() as u16);
            verts.push(Vertex::new(c.x, c.y, c.z, 0.0, 0.0, col));
            for k in 0..10u16 {
                let t = k as f32 / 10.0 * std::f32::consts::TAU;
                let q = c + (right * t.cos() + up * t.sin()) * r;
                verts.push(Vertex::new(q.x, q.y, q.z, 0.0, 0.0, rim));
                idx.extend_from_slice(&[base, base + 1 + k, base + 1 + (k + 1) % 10]);
            }
        }
        if !idx.is_empty() {
            draw_mesh(&Mesh { vertices: verts, indices: idx, texture: None });
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
        // Hidden once wrecked: after a crash's fireball, or when shot down in a dogfight.
        let dead = self.wrecked();
        let to_w = |q: Vec3| p + f * q.x + l * q.y + u * q.z;
        let mut push_mesh = |m: &c172::Mesh, to_w: &dyn Fn(Vec3) -> Vec3, (f, l, u): (Vec3, Vec3, Vec3), tint: [f32; 3], livery: f32| {
            let base = lv.len() as u32;
            for a in &m.v {
                let nw = f * a.nrm.x + l * a.nrm.y + u * a.nrm.z;
                let col = [tint[0], tint[1], tint[2], 1.0];
                lv.push(DV { pos: to_w(a.pos).to_array(), nrm: nw.to_array(), col, mat: [photo::K_AIRCRAFT, livery, 0.0, 0.0], loc: [a.pos.x, a.pos.y, a.pos.z, a.part] });
            }
            li.extend(m.i.iter().map(|i| i + base));
        };
        if !dead {
            push_mesh(&c172::build(&self.surfaces().0, cockpit), &to_w, (f, l, u), self.player_tint(), 0.0);
        }
        let bandit = self.bandit_drawn();
        if let Some((bp, (bf, bl, bu), tint)) = bandit {
            let bw = |q: Vec3| bp + bf * q.x + bl * q.y + bu * q.z;
            push_mesh(&c172::build(&c172::Controls::default(), false), &bw, (bf, bl, bu), tint, 1.0);
        }
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
        let mut discs: Vec<(Box<dyn Fn(Vec3) -> Vec3>, Vec3, f32)> = Vec::new();
        if !dead {
            discs.push((Box::new(to_w), f, 0.0));
        }
        if let Some((bp, (bf, bl, bu), _)) = bandit {
            discs.push((Box::new(move |q: Vec3| bp + bf * q.x + bl * q.y + bu * q.z), bf, 1.0));
        }
        for (to_w, f, livery) in discs {
            let base = ov.len() as u32;
            for q in c172::prop_disc() {
                ov.push(DV { pos: to_w(q).to_array(), nrm: f.to_array(), col: [1.0; 4], mat: [photo::K_AIRCRAFT, livery, 0.0, 0.0], loc: [q.x, q.y, q.z, c172::P_PROP] });
            }
            oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
        }
        (lv, li, ov, oi)
    }

    /// Tracers (glows), fire and flashes (HDR glows), smoke, dust and debris (soft discs) for the photoreal overlay.
    fn photo_combat(&self, ov: &mut Vec<photo::DV>, oi: &mut Vec<u32>, cam: Vec3, right: Vec3, up: Vec3) {
        let Some(d) = &self.dogfight else { return };
        for b in d.bullets.iter().filter(|b| b.tracer) {
            let p = dv3(b.p);
            let w = 0.5 + (p - cam).length() * 0.003;
            streak(ov, oi, p - dv3(b.v) * 0.03, p, w, [3.0, 1.4, 0.4, 1.0], cam);
        }
        let mut fx: Vec<_> = d.fx.iter().map(|f| ((dv3(f.p) - cam).length_squared(), f)).collect();
        fx.sort_by(|a, b| b.0.total_cmp(&a.0));
        let disp = |c: f32| photo::display_to_scene(c, 1.0);
        for (_, f) in fx {
            let (c, r, a) = (dv3(f.p), f.radius() as f32, f.strength() as f32);
            match f.kind {
                FxKind::Smoke => {
                    let g = disp(0.6 - 0.5 * f.shade as f32);
                    sprite(ov, oi, c, r, [g, g, g * 1.02, a], 8.0, right, up);
                }
                FxKind::Dust => sprite(ov, oi, c, r, [disp(0.55), disp(0.5), disp(0.42), a], 8.0, right, up),
                FxKind::Debris => sprite(ov, oi, c, r, [disp(0.06), disp(0.06), disp(0.06), 1.0], 8.0, right, up),
                FxKind::Fire => sprite(ov, oi, c, r, [0.9 * a, 0.3 * a, 0.06 * a, 1.0], 9.0, right, up),
                FxKind::Flash => sprite(ov, oi, c, r, [3.0 * a, 2.2 * a, 1.2 * a, 1.0], 9.0, right, up),
                FxKind::Spark => sprite(ov, oi, c, r, [4.0 * a, 2.8 * a, 1.2 * a, 1.0], 9.0, right, up),
            }
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
        // Exact-rollout filters (`--safety-filter`): filter name, escape (committed or verified) and check time.
        #[allow(unused_mut)]
        let mut env: Option<(String, &str, f64, bool)> = None;
        #[cfg(feature = "jsb")]
        if let Some(g) = &self.sim.lean {
            let e = if g.escaping { "escape" } else { "pilot" };
            env = Some(("lean gate (proved)".to_string(), e, *g.wall_ms.last().unwrap_or(&0.0) as f64, g.start_ok));
        }
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
            "{} · {} · H help · Tab map · Space filter · B escapes · C camera ({}) · V renderer ({}) · 1-{} scenarios{} · K kamikaze · T harness · R reset{}{}",
            self.world.map.name(),
            scenario_names(self.world.map)[self.scenario],
            CAM_NAMES[self.cam_mode],
            RENDERER_NAMES[self.renderer],
            scenario_names(self.world.map).len(),
            if self.world.map == MapId::Grid { " · Y showcase" } else { "" },
            if self.hotas_prev.is_some() { " · HOTAS" } else { "" },
            if self.world.map == MapId::SanFrancisco { " · map data: DataSF, © OpenStreetMap contributors, USGS" } else { "" }
        );
        draw_rectangle(0.0, h - 30.0, w, 30.0, Color::new(0.04, 0.06, 0.09, 0.55));
        ui.text(&hint, 14.0, h - 10.0, 13.0, dim, false);
        let fps = format!("{} fps  t={:.1}s", get_fps(), self.sim.time());
        ui.text(&fps, w - ui.width(&fps, 13.0, true) - 14.0, h - 10.0, 13.0, dim, true);

        if self.sim.crashed {
            let df = self.dogfight.as_ref().filter(|d| d.player_dead);
            // Lighter in a dogfight, so the explosion shows through.
            draw_rectangle(0.0, 0.0, w, h, Color::new(0.3, 0.0, 0.0, if df.is_some() { 0.12 } else { 0.35 }));
            let t = if df.is_some_and(|d| d.player_hits >= HITS_TO_KILL) { "SHOT DOWN" } else { "CRASH" };
            ui.text(t, (w - ui.width(t, 64.0, false)) * 0.5, h * 0.42, 64.0, WHITE, false);
            let sub = match df {
                Some(d) => format!("{} kills · R fly again · Tab leaves the dogfight", d.kills),
                None => format!(
                    "true clearance {:.1} m at t = {:.1} s · filter was {} · R retry · Space toggles the filter",
                    self.sim.crash_clear,
                    self.sim.time(),
                    if on { "ON" } else { "OFF" }
                ),
            };
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

    /// Dogfight overlay: hit flash, health bars, bandit marker or edge arrow, gun cross and lead pipper.
    fn draw_combat_hud(&self, ui: &Ui, cam: &Camera3D) {
        let Some(d) = &self.dogfight else { return };
        let (w, h) = (screen_width(), screen_height());
        let flash = 0.35 * (-d.since_hit as f32 * 6.0).exp();
        if flash > 0.01 {
            draw_rectangle(0.0, 0.0, w, h, Color::new(0.8, 0.05, 0.0, flash));
        }
        // Health bars and kills, top centre under the status pills.
        let red = Color::new(1.0, 0.3, 0.22, 1.0);
        let y = 52.0;
        let bar = |x: f32, label: &str, hits: u32, col: Color| {
            let left = 1.0 - (hits as f32 / HITS_TO_KILL as f32).min(1.0);
            ui.text(label, x, y + 22.0, 14.0, WHITE, false);
            draw_rectangle(x + 64.0, y + 11.0, 130.0, 12.0, Color::new(0.0, 0.0, 0.0, 0.5));
            draw_rectangle(x + 64.0, y + 11.0, 130.0 * left, 12.0, col);
        };
        let x0 = w * 0.5 - 230.0;
        draw_rectangle(x0 - 12.0, y, 484.0, 34.0, Color::new(0.04, 0.06, 0.09, 0.55));
        bar(x0, "YOU", d.player_hits, Color::new(0.3, 0.8, 1.0, 1.0));
        match &d.bandit {
            Some(b) => bar(x0 + 210.0, "FLY", b.hits, viridis(0.9)),
            None => ui.text("fly inbound…", x0 + 210.0, y + 22.0, 14.0, Color::new(1.0, 1.0, 1.0, 0.6), false),
        }
        ui.text(&format!("kills {}", d.kills), x0 + 410.0, y + 22.0, 14.0, WHITE, false);
        match &d.brain {
            // Drawn last, from the main loop (`draw_fly_hud`), so it sits over the markers.
            Some(_) => {}
            None => {
                let t = "fly pilot: hand-written pursuit law (no assets/flybrain.bin)";
                ui.text(t, (w - ui.width(t, 12.0, false)) * 0.5, y + 50.0, 12.0, Color::new(1.0, 1.0, 1.0, 0.7), false);
            }
        }
        if d.since_kill < 2.5 {
            let a = (2.5 - d.since_kill as f32).min(1.0);
            ui.text(d.kill_msg, (w - ui.width(d.kill_msg, 44.0, false)) * 0.5, h * 0.3, 44.0, Color::new(1.0, 0.85, 0.3, a), false);
        }
        if d.player_dead {
            return;
        }
        let Some(b) = &d.bandit else {
            if let Some(q) = project(cam, sv3(&self.sim.s) + dv3(combat::dir(&self.sim.s)) * 600.0) {
                glow_cross(q, false, get_time() as f32);
            }
            return;
        };
        let player = &self.sim.s;
        let bp = dv3(combat::pos(&b.s));
        let range = (bp - sv3(player)).length();
        let on_screen = project(cam, bp).filter(|q| q.x > 0.0 && q.x < w && q.y > 0.0 && q.y < h);
        match on_screen.filter(|_| self.cam_mode != 5) {
            // Fly cam looks at the fly: no bracket over it.
            None if self.cam_mode == 5 => {}
            Some(q) => {
                // Bracket and range.
                let r = (2200.0 / range.max(1.0)).clamp(12.0, 60.0);
                for (sx, sy) in [(-1.0, -1.0), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)] {
                    let c = vec2(q.x + sx * r, q.y + sy * r);
                    draw_line(c.x, c.y, c.x - sx * r * 0.5, c.y, 2.0, red);
                    draw_line(c.x, c.y, c.x, c.y - sy * r * 0.5, 2.0, red);
                }
                ui.text(&format!("{:.0} m", range), q.x + r + 6.0, q.y + 5.0, 14.0, red, true);
            }
            None => {
                // Edge arrow toward the bandit.
                let fwd = (cam.target - cam.position).normalize_or_zero();
                let right = fwd.cross(cam.up).normalize_or_zero();
                let up = right.cross(fwd);
                let rel = bp - cam.position;
                let dir = vec2(rel.dot(right), -rel.dot(up)).normalize_or(vec2(0.0, 1.0));
                let c = vec2(w * 0.5, h * 0.5) + dir * (w.min(h) * 0.42);
                let n = vec2(-dir.y, dir.x);
                draw_triangle(c + dir * 16.0, c - dir * 8.0 + n * 11.0, c - dir * 8.0 - n * 11.0, red);
                ui.text(&format!("{:.0} m", range), c.x - 20.0, c.y + 30.0, 14.0, red, true);
            }
        }
        // Gun cross on the flight path at the bandit's range, and where to put it (the lead pipper).
        let at = if range < 1200.0 { range } else { 600.0 };
        let cross = project(cam, sv3(player) + dv3(combat::dir(player)) * at);
        let pip = (range < 1200.0).then(|| project(cam, dv3(combat::lead_point(player, &b.s)))).flatten();
        if let Some(q) = pip {
            draw_circle(q.x, q.y, 11.0, Color { a: 0.12, ..red });
            draw_circle_lines(q.x, q.y, 7.0, 2.0, red);
        }
        if let Some(q) = cross {
            let hot = pip.is_some_and(|p| p.distance(q) < 14.0);
            glow_cross(q, hot, get_time() as f32);
        }
    }

    fn draw_help(&self, ui: &Ui) {
        let (w, h) = (screen_width(), screen_height());
        let pw = 700.0f32.min(w - 40.0);
        let lines: [(&str, &str); 27] = [
            ("W/S  ↑/↓", "pitch (stick forward = nose down; I inverts)"),
            ("A/D  ←/→", "roll · release the keys to hold flight path and bank"),
            ("Q / E", "throttle down / up"),
            ("Space", "safety filter on / off"),
            ("Shift", "guns: hold to fire. The first shot summons the fly (a connectome brain), which you can shoot down"),
            ("F", "filter: P1 blend+commit · P2 closed-form · permissive"),
            ("G", "Phase 3 robust margins on / off"),
            ("B", "show escape paths (green valid, red not, yellow committed)"),
            ("7", "wingtip strobes on/off"),
            ("M", "model mismatch: wind and a weaker, slower aircraft"),
            ("C", "camera: chase · cockpit · orbit · overhead · fly-by"),
            ("1 2 3 4 5", "tower run (Salesforce run) · dive · ridge (Nob Hill) · slow and low · tower gap (grid only)"),
            ("Y", "tower gap with the scripted showcase pilot (grid city; threads the gap, turns into a tower)"),
            ("Tab", "map: grid city · San Francisco"),
            ("K", "kamikaze autopilot (flies at buildings and terrain)"),
            ("8", "fly opponent on the trigger: on (default) / off"),
            ("T", "run the 200-episode headless harness"),
            ("R", "reset the scenario"),
            ("V", "renderer: classic · photoreal · ray traced (Metal RT + MetalFX)"),
            (", .  ; '", "photoreal sun: elevation down / up, azimuth"),
            ("P  [ ]  - =  9 0", "weather preset · fog density · fog height · fog anisotropy"),
            ("L  O  Z/X  N/J", "footage look · lens preset · f-stop · focal length"),
            ("6", "cinematic: fly-by camera, clear weather, 50 mm f/4"),
            ("U", "ray traced: MetalFX denoiser on / off"),
            ("HOTAS", "stick pitch / roll · lever throttle · trigger guns · stick button 2 filter · USB button 3 kamikaze"),
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
    cityflight::jsb::parse_fuel_args(&args);
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
    if args.iter().any(|a| a == "--funnel") {
        cityflight::autoland::FUNNEL.store(true, std::sync::atomic::Ordering::Relaxed);
        cityflight::envfilter::N_USED.store(cityflight::autoland::N_AUTO as u8, std::sync::atomic::Ordering::Relaxed);
    }
    #[cfg(feature = "jsb")]
    if let Some(lb) = arg("--fuel").and_then(|s| s.parse().ok()) {
        cityflight::jsb::set_fuel_lb(lb);
    }
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
    if let Some(f) = arg("--safety-filter") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
        if f == "exact-rollout-lean" {
            // The Lean gate rolls out with fuel freeze (CityGate.Plane.step); a burning flown plant would not match it.
            assert!(cityflight::jsb::fuel_freeze_default(), "--fuel-drain does not combine with exact-rollout-lean (the Lean gate always rolls out with fuel freeze)");
            cityflight::leangate::LEAN_GATE.store(true, std::sync::atomic::Ordering::Relaxed);
        }
        cityflight::envfilter::ENV_FILTER.store(cityflight::envfilter::parse(&f), std::sync::atomic::Ordering::Relaxed);
        if matches!(cityflight::envfilter::kind(), Some(cityflight::envfilter::Kind::Fitted { .. })) {
            cityflight::envfilter::table();
        }
    }

    clear_background(Color::new(FOG[0], FOG[1], FOG[2], 1.0));
    next_frame().await;
    // San Francisco unless `--map grid`.
    let map = match arg("--map") {
        None => MapId::SanFrancisco,
        Some(m) => MapId::parse(&m).unwrap_or_else(|| {
            eprintln!("--map takes grid or sf");
            std::process::exit(2);
        }),
    };
    // The other map's scenes, parked while it is not shown (Tab builds them on first use).
    let mut parked: [Option<MapScenes>; 2] = [None, None];
    let MapScenes { world, mut scene, mut photo } = MapScenes::new(World::load(map));
    let ui = Ui {
        mono: load_font(&["/System/Library/Fonts/SFNSMono.ttf", "/System/Library/Fonts/Menlo.ttc"]),
        sans: load_font(&["/System/Library/Fonts/SFNS.ttf", "/System/Library/Fonts/Helvetica.ttc"]),
    };
    let scenario: usize = arg("--scenario").and_then(|s| s.parse::<usize>().ok()).map(|s| s.clamp(1, scenario_names(map).len()) - 1).unwrap_or(0);
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
        switch_map: false,
        show_paths: args.iter().any(|a| a == "--paths"),
        strobes: args.iter().any(|a| a == "--strobes"),
        show_help: shot.is_none(),
        cam_mode: arg("--cam").and_then(|s| s.parse().ok()).unwrap_or(0),
        invert: false,
        stick: (0.0, 0.0),
        hotas: hotas::Hotas::open(),
        hotas_prev: None,
        guns: gun::Guns::new(),
        trigger: false,
        fire_hold: args.iter().any(|a| a == "--fire"),
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
        sun_el: sun_angles(map).0,
        sun_az: sun_angles(map).1,
        label: None,
        dogfight: None,
        fly_summon: true,
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
    if args.iter().any(|a| a == "--dogfight") {
        app.dogfight = Some(Dogfight::new(app.seed, gui_brain()));
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
            (scenario_start(world, ((e - 1000) as usize).min(scenario_names(map).len() - 1)), true)
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
    // --at x,y,agl,heading_deg: start anywhere (map metres), level at 50 m/s.
    if let Some(at) = arg("--at") {
        let v: Vec<f64> = at.split(',').filter_map(|t| t.trim().parse().ok()).collect();
        if v.len() == 4 {
            let s0 = trimmed(v[0], v[1], world.terrain(v[0], v[1]) + v[2], 50.0, 0.0, v[3].to_radians(), 0.64);
            app.sim = Sim::new(world, s0, app.cfg(true));
            app.fbw = Fbw::from_state(&s0);
            app.trail.clear();
            let (f, _, _) = body_axes(&s0);
            app.cam_pos = sv3(&s0) - f * 30.0 + vec3(0.0, 0.0, 8.0);
        }
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
    // The fly's view for the dogfight HUD, rendered offscreen by the classic renderer.
    let dpi = screen_dpi_scale();
    let fly_rt = render_target_ex((FLY_VIEW.0 * dpi) as u32, (FLY_VIEW.1 * dpi) as u32, RenderTargetParams { sample_count: 1, depth: true });
    fly_rt.texture.set_filter(FilterMode::Linear);
    let mut fly_cam_last: Option<Camera3D> = None;
    let mut frame = 0u32;
    let mut perf = (0.0f64, 0u32, 0.0f64, 0.0f64);
    let mut perf_t = std::time::Instant::now();
    loop {
        if std::mem::take(&mut app.switch_map) {
            let next = app.world.map.next();
            let settings = photo.as_ref().map(|p| p.settings);
            let ms = match parked[next as usize].take() {
                Some(ms) => ms,
                None => {
                    clear_background(Color::new(FOG[0], FOG[1], FOG[2], 1.0));
                    let t = format!("Loading {}...", next.name());
                    ui.text(&t, (screen_width() - ui.width(&t, 28.0, false)) * 0.5, screen_height() * 0.5, 28.0, WHITE, false);
                    next_frame().await;
                    MapScenes::new(World::load(next))
                }
            };
            parked[app.world.map as usize] = Some(MapScenes { world: app.world, scene, photo });
            MapScenes { world: app.world, scene, photo } = ms;
            if let (Some(ph), Some(st)) = (photo.as_mut(), settings) {
                ph.settings = st;
            }
            (app.sun_el, app.sun_az) = sun_angles(next);
            app.kamikaze = None;
            app.showcase = None;
            app.reset(0);
        }
        let loop_start = std::time::Instant::now();
        let dt = get_frame_time().min(0.1) as f64;
        if shot.is_none() {
            app.input(dt);
            if let Some(ph) = photo.as_mut() {
                photo_keys(&mut app, ph);
            }
        }
        let step_dt = if shot.is_some() { 1.0 / 60.0 } else { dt };
        app.step(step_dt);
        app.update_guns(step_dt);
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
        // The fly's view re-renders the whole city, so every other frame (the panel keeps the last one, and the
        // camera it was rendered with, so its overlays stay aligned).
        let fly_cam = if app.bandit_drawn().is_none() || app.dogfight.as_ref().is_none_or(|d| d.brain.is_none()) {
            None
        } else if frame % 2 == 1 && fly_cam_last.is_some() {
            fly_cam_last.as_ref().map(cam_copy)
        } else {
            app.render_fly_view(&scene, &fly_rt)
        };
        fly_cam_last = fly_cam.as_ref().map(cam_copy);
        match (app.renderer, photo.as_mut()) {
            (1 | 2, Some(ph)) => {
                let (lv, li, mut ov, mut oi) = app.photo_dynamic(cam.position, 1.0);
                let night = (1.0 - (app.sun_el + 4.0) / 10.0).clamp(0.0, 1.0);
                let fwd = (cam.target - cam.position).normalize();
                let right = fwd.cross(cam.up).normalize();
                let up = right.cross(fwd);
                ph.lamp_sprites(&mut ov, &mut oi, cam.position, right, up, night);
                let lights = app.aircraft_lights(&mut ov, &mut oi, cam.position, right, up);
                app.photo_combat(&mut ov, &mut oi, cam.position, right, up);
                app.guns.photo(&mut ov, &mut oi, &gun::View::of(&cam));
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
                        focus: match (app.cam_mode, app.bandit_drawn()) {
                            (1, _) => 400.0,
                            (5, Some((bp, ..))) => (bp - cam.position).length().max(2.0),
                            _ => (sv3(&app.drawn_state()) - cam.position).length().max(2.0),
                        },
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
        app.draw_combat_hud(&ui, &cam);
        if let Some(br) = app.dogfight.as_ref().and_then(|d| d.brain.as_ref()) {
            app.draw_fly_panel(&ui, br, fly_cam.as_ref().map(|c| (&fly_rt, c)));
        }
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
