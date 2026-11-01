//! Photoreal renderer (Metal only).

use crate::shaders;
use cityflight::world::*;
use macroquad::miniquad as mq;
use macroquad::prelude::*;

/// `mat` = (kind, seed, z0, z1); facade `fac` = (wall origin, wall length, floor height, column width).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PV {
    pub pos: [f32; 3],
    pub nrm: [f32; 3],
    pub col: [f32; 3],
    pub uv: [f32; 2],
    pub mat: [f32; 4],
    pub fac: [f32; 4],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct DV {
    pub pos: [f32; 3],
    pub nrm: [f32; 3],
    pub col: [f32; 4],
    pub mat: [f32; 4],
    /// Body-axes position and part id (aircraft); zero for overlays.
    pub loc: [f32; 4],
}

pub const K_TERRAIN: f32 = 0.0;
pub const K_FACADE: f32 = 1.0;
pub const K_ROOF: f32 = 2.0;
pub const K_CLUTTER: f32 = 3.0;
pub const K_AIRCRAFT: f32 = 4.0;
pub const K_OVERLAY: f32 = 5.0;
/// `mat[1]` of a `K_OVERLAY` vertex: a soft see-through sprite (dust, smoke) that must not write depth, or
/// the fog and clouds would stop at its transparent edges.
pub const OVERLAY_SOFT: f32 = 1.0;

/// Must match `FrameU` in the MSL prelude.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FrameU {
    pub viewproj: [f32; 16],
    pub inv_viewproj: [f32; 16],
    pub prev_viewproj: [f32; 16],
    pub cam: [f32; 4],
    pub sun: [f32; 4],
    pub sun_col: [f32; 4],
    pub screen: [f32; 4],
    pub params: [f32; 4],
    pub amb: [f32; 4],
    pub sh: [[f32; 4]; 9],
    pub shadow: [[f32; 16]; 4],
    pub splits: [f32; 4],
    pub shadow_texel: [f32; 4],
    pub prop: [f32; 4],
    pub flags: [f32; 4],
    pub fog: [f32; 4],
    pub fog2: [f32; 4],
    pub land_pos: [f32; 4],
    pub land_dir: [f32; 4],
    pub nav: [[f32; 4]; 3],
    pub post0: [f32; 4],
    pub post1: [f32; 4],
    pub post2: [f32; 4],
    pub post3: [f32; 4],
    pub post4: [f32; 4],
    pub post5: [f32; 4],
    pub viewproj_nj: [f32; 16],
    pub prev_model: [[f32; 4]; 4],
    pub post6: [f32; 4],
}

pub struct Lens {
    pub focus: f32,
    pub focal_mm: f32,
    pub fstop: f32,
    pub tilt_shift: bool,
    pub cats_eye: f32,
    pub hexagon: bool,
    pub footage: bool,
    /// Shutter angle in degrees at 30 fps (footage mode).
    pub shutter: f32,
    pub frame_dt: f32,
}

#[derive(Clone, Copy)]
pub struct Settings {
    /// Multiplier on the automatic exposure.
    pub exposure: f32,
    pub fog: Fog,
    pub preset: usize,
    /// Internal resolution of the ray-traced mode relative to the window (MetalFX upscales).
    pub rt_scale: f32,
    /// MetalFX output size relative to the window; post runs there and the last pass scales to the window.
    pub rt_out_scale: f32,
    /// MetalFX temporal denoising scaler instead of the joint-bilateral filter and plain temporal scaler.
    pub rt_denoiser: bool,
}

#[derive(Clone, Copy)]
pub struct Fog {
    /// Extinction at ground level, 1/m.
    pub density: f32,
    /// Height scale of the exponential layer, m.
    pub falloff: f32,
    pub anisotropy: f32,
    pub valley_top: f32,
    pub valley_density: f32,
    pub cloud_cover: f32,
    pub cloud_base: f32,
    pub cloud_top: f32,
    pub haze: f32,
}

/// Weather presets: (name, fog, sun elevation and azimuth in degrees).
pub const PRESETS: [(&str, Fog, f32, f32); 4] = [
    ("clear", Fog { density: 3e-5, falloff: 500.0, anisotropy: 0.6, valley_top: 0.0, valley_density: 0.0, cloud_cover: 0.38, cloud_base: 1500.0, cloud_top: 2500.0, haze: 8.0 }, 44.0, -129.0),
    ("hazy", Fog { density: 1.6e-4, falloff: 420.0, anisotropy: 0.72, valley_top: 0.0, valley_density: 0.0, cloud_cover: 0.5, cloud_base: 1400.0, cloud_top: 2300.0, haze: 25.0 }, 30.0, -100.0),
    ("valley fog", Fog { density: 5e-5, falloff: 300.0, anisotropy: 0.78, valley_top: 70.0, valley_density: 1.2e-3, cloud_cover: 0.25, cloud_base: 1700.0, cloud_top: 2500.0, haze: 14.0 }, 9.0, 60.0),
    ("dusk", Fog { density: 1.1e-4, falloff: 380.0, anisotropy: 0.7, valley_top: 0.0, valley_density: 0.0, cloud_cover: 0.45, cloud_base: 1500.0, cloud_top: 2400.0, haze: 18.0 }, 1.0, -160.0),
];

pub struct FrameIn<'a> {
    pub cam_pos: Vec3,
    pub cam_target: Vec3,
    pub cam_up: Vec3,
    pub fovy: f32,
    pub sun: Vec3,
    pub time: f32,
    pub dyn_lit: (&'a [DV], &'a [u32]),
    /// Propeller angle (rad), rate (rad/s), rolling-shutter readout (s), exposure (s).
    pub prop: [f32; 4],
    pub cockpit: bool,
    pub land_pos: [f32; 4],
    pub land_dir: [f32; 4],
    pub nav: [[f32; 4]; 3],
    pub dyn_overlay: (&'a [DV], &'a [u32]),
    pub lens: Lens,
    pub rt: bool,
    /// Aircraft position and body axes (forward, left, up).
    pub model: [Vec3; 4],
}

struct RtTex {
    g: Vec<mq::TextureId>,
    gi: mq::TextureId,
    refl: mq::TextureId,
    composed: mq::TextureId,
    noisy: mq::TextureId,
    spec: mq::TextureId,
    rough: mq::TextureId,
    up: mq::TextureId,
}

struct Targets {
    w: u32,
    h: u32,
    ow: u32,
    oh: u32,
    rtt: Option<RtTex>,
    hdr: mq::TextureId,
    amb: mq::TextureId,
    depth: mq::TextureId,
    scene_pass: mq::RenderPass,
    ao: mq::TextureId,
    ao_pass: mq::RenderPass,
    vol: mq::TextureId,
    vol_pass: mq::RenderPass,
    comb: mq::TextureId,
    comb_pass: mq::RenderPass,
    dof: mq::TextureId,
    dof_pass: mq::RenderPass,
    bloom: Vec<(mq::TextureId, mq::RenderPass, u32, u32)>,
}

struct DynBuf {
    vb: mq::BufferId,
    ib: mq::BufferId,
    cap_v: usize,
    cap_i: usize,
}

pub struct Photo {
    terr_pipe: mq::Pipeline,
    bld_pipe: mq::Pipeline,
    terr: mq::Bindings,
    terr_n: i32,
    /// San Francisco's Bay Area backdrop (terrain pipeline).
    back: Option<(mq::Bindings, i32)>,
    bld: mq::Bindings,
    bld_n: i32,
    sky_pipe: mq::Pipeline,
    comp_pipe: mq::Pipeline,
    dof_pipe: mq::Pipeline,
    down_pipe: mq::Pipeline,
    up_pipe: mq::Pipeline,
    final_pipe: mq::Pipeline,
    ssao_pipe: mq::Pipeline,
    vol_pipe: mq::Pipeline,
    lamps: Vec<Vec3>,
    exposure_auto: f32,
    rt: Option<crate::rt::Rt>,
    rt_failed: bool,
    rt_mesh: (Vec<[f32; 3]>, Vec<u32>, Vec<crate::rt::Tri>),
    galb: mq::TextureId,
    prev_model: [Vec3; 4],
    rt_reset: bool,
    dyn_pipe: mq::Pipeline,
    overlay_pipe: mq::Pipeline,
    /// The overlay pipeline, writing depth: for the ribbons (trail, escape paths), so the fog and clouds
    /// composited later stop at them instead of running on to whatever is behind (often sky and clouds).
    ribbon_pipe: mq::Pipeline,
    fs_vb: mq::BufferId,
    fs_ib: mq::BufferId,
    dyn_lit: DynBuf,
    dyn_ov: DynBuf,
    targets: Option<Targets>,
    prev_viewproj: Mat4,
    lut_pipe: mq::Pipeline,
    sky_lut: mq::TextureId,
    lut_pass: mq::RenderPass,
    sky_light: Option<(Vec3, f32, crate::atmos::SkyLight)>,
    shadow_tex: [mq::TextureId; 4],
    shadow_pass: [mq::RenderPass; 4],
    shadow_pv_pipe: mq::Pipeline,
    shadow_dv_pipe: mq::Pipeline,
    pub settings: Settings,
}

fn shader(ctx: &mut dyn mq::RenderingBackend, src: &str, images: &[&str]) -> mq::ShaderId {
    ctx.new_shader(
        mq::ShaderSource::Msl { program: src },
        mq::ShaderMeta {
            images: images.iter().map(|s| s.to_string()).collect(),
            uniforms: mq::UniformBlockLayout { uniforms: vec![mq::UniformDesc::new("frame", mq::UniformType::Mat4)] },
        },
    )
    .unwrap_or_else(|e| panic!("shader: {e}"))
}

fn building_seed(b: &Building) -> f32 {
    let h = ((b.x0 * 7.31 + b.y0 * 3.17 + b.lot as f64 * 0.618).sin() * 43758.5453).fract().abs();
    h as f32
}

pub fn building_albedo(b: &Building) -> [f32; 3] {
    let t = b.tint;
    let tall = b.z1 - b.z0 > 70.0;
    let pal_tall = [[0.50, 0.58, 0.67], [0.40, 0.46, 0.53], [0.66, 0.70, 0.74], [0.56, 0.62, 0.58]];
    let pal_low = [[0.76, 0.73, 0.68], [0.64, 0.46, 0.38], [0.84, 0.81, 0.74], [0.70, 0.66, 0.58], [0.58, 0.60, 0.62]];
    let c = if tall { pal_tall[((t * 3.999) as usize).min(3)] } else { pal_low[((t * 4.999) as usize).min(4)] };
    [srgb_to_lin(c[0]), srgb_to_lin(c[1]), srgb_to_lin(c[2])]
}

pub fn srgb_to_lin(c: f32) -> f32 {
    if c <= 0.04045 {
        c / 12.92
    } else {
        ((c + 0.055) / 1.055).powf(2.4)
    }
}

fn lin_to_srgb(c: f32) -> f32 {
    if c <= 0.0031308 {
        c * 12.92
    } else {
        1.055 * c.powf(1.0 / 2.4) - 0.055
    }
}

/// ACES filmic fit (Narkowicz), the same curve the composite shader uses.
pub fn aces(x: f32) -> f32 {
    ((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14)).clamp(0.0, 1.0)
}

/// Scene-linear value that displays as sRGB `c` after exposure, tonemap and gamma.
pub fn display_to_scene(c: f32, exposure: f32) -> f32 {
    let target = srgb_to_lin(c.clamp(0.0, 0.999));
    let (mut lo, mut hi) = (0.0f32, 64.0f32);
    for _ in 0..24 {
        let m = 0.5 * (lo + hi);
        if aces(m) < target {
            lo = m;
        } else {
            hi = m;
        }
    }
    0.5 * (lo + hi) / exposure
}

fn mk_dyn(ctx: &mut dyn mq::RenderingBackend, cap_v: usize, cap_i: usize) -> DynBuf {
    DynBuf {
        vb: ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Stream, mq::BufferSource::empty::<DV>(cap_v)),
        ib: ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Stream, mq::BufferSource::empty::<u32>(cap_i)),
        cap_v,
        cap_i,
    }
}

impl Photo {
    pub fn new(w: &World) -> Photo {
        let sf = w.map == MapId::SanFrancisco;
        let ((galb_px, gaw, gah), (gmask_px, gmw, gmh)) = if sf {
            crate::sfscene::ground(w)
        } else {
            let (a, m) = crate::ground::bake(w);
            let n = crate::ground::TEX;
            ((a, n, n), (m, n, n))
        };
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
                tv.push(PV {
                    pos: [x as f32, y as f32, w.terr[j * tnx + i]],
                    nrm: [n.x, n.y, n.z],
                    col: [1.0, 1.0, 1.0],
                    uv: [((x - w.x0) / (w.x1 - w.x0)) as f32, ((y - w.y0) / (w.y1 - w.y0)) as f32],
                    mat: [K_TERRAIN, 0.0, 0.0, 0.0],
                    fac: [0.0; 4],
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
        let gtex = |ctx: &mut dyn mq::RenderingBackend, px: &[u8], tw: usize, th: usize| {
            let t = ctx.new_texture(
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
            ctx.texture_generate_mipmaps(t);
            t
        };
        let galb = gtex(ctx, &galb_px, gaw, gah);
        let gmask = gtex(ctx, &gmask_px, gmw, gmh);
        drop((galb_px, gmask_px));
        let sets = |ctx: &mut dyn mq::RenderingBackend, names: &[&str]| -> Vec<mq::TextureId> {
            names
                .iter()
                .flat_map(|n| {
                    let t = crate::assets::load(ctx, n, 4.0, 4.0);
                    [t.alb, t.nrm, t.orm]
                })
                .collect()
        };
        let ground_sets = sets(ctx, &crate::assets::GROUND);
        let roof_sets = sets(ctx, &crate::assets::ROOF);
        let fac_sets: Vec<mq::TextureId> = crate::assets::FACADES
            .iter()
            .flat_map(|f| {
                let t = crate::assets::load(ctx, f.0, f.1, f.2);
                [t.alb, t.nrm, t.orm]
            })
            .collect();

        let sky_lut = ctx.new_render_texture(mq::TextureParams {
            format: mq::TextureFormat::RGBA16F,
            width: shaders::SKY_LUT_W,
            height: shaders::SKY_LUT_H,
            min_filter: mq::FilterMode::Linear,
            mag_filter: mq::FilterMode::Linear,
            ..Default::default()
        });
        let lut_pass = ctx.new_render_pass(sky_lut, None);

        let (bv, bi) = if sf { crate::sfscene::building_mesh(w) } else { building_mesh(w) };
        let mk = |ctx: &mut dyn mq::RenderingBackend, v: &[PV], i: &[u32], images: Vec<mq::TextureId>| mq::Bindings {
            vertex_buffers: vec![ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(v))],
            index_buffer: ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(i)),
            images,
        };
        let shadow_tex: [mq::TextureId; 4] = std::array::from_fn(|_| {
            ctx.new_render_texture(mq::TextureParams {
                format: mq::TextureFormat::Depth32,
                width: SHADOW_RES,
                height: SHADOW_RES,
                min_filter: mq::FilterMode::Linear,
                mag_filter: mq::FilterMode::Linear,
                ..Default::default()
            })
        });
        let shadow_pass: [mq::RenderPass; 4] = std::array::from_fn(|c| ctx.new_render_pass_mrt(&[], None, Some(shadow_tex[c])));
        let mut timg = vec![sky_lut, galb, gmask];
        timg.extend(&ground_sets);
        timg.extend(&shadow_tex);
        let terr = mk(ctx, &tv, &ti, timg);
        // San Francisco: the Bay Area beyond the square, drawn with the terrain shader and its own imagery.
        let back = if sf { crate::sfscene::backdrop(w) } else { None }.map(|b| {
            let mut img = vec![sky_lut, gtex(ctx, &b.alb, b.n, b.n), gtex(ctx, &b.mask, b.mask_n, b.mask_n)];
            img.extend(&ground_sets);
            img.extend(&shadow_tex);
            (mk(ctx, &b.v, &b.i, img), b.i.len() as i32)
        });
        let mut bimg = vec![sky_lut];
        bimg.extend(&fac_sets);
        bimg.extend(&roof_sets);
        bimg.extend(&shadow_tex);
        let bld = mk(ctx, &bv, &bi, bimg);

        let names = |n: usize| -> Vec<String> { (0..n).map(|k| format!("t{k}")).collect() };
        let rev_z = mq::PipelineParams { depth_test: mq::Comparison::GreaterOrEqual, depth_write: true, ..Default::default() };
        let pv_attrs = [
            mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float3),
            mq::VertexAttribute::new("in_nrm", mq::VertexFormat::Float3),
            mq::VertexAttribute::new("in_col", mq::VertexFormat::Float3),
            mq::VertexAttribute::new("in_uv", mq::VertexFormat::Float2),
            mq::VertexAttribute::new("in_mat", mq::VertexFormat::Float4),
            mq::VertexAttribute::new("in_fac", mq::VertexFormat::Float4),
        ];
        let tsrc = shaders::terrain();
        let tn = names(terr.images.len());
        let tsh = shader(ctx, &tsrc, &tn.iter().map(|s| s.as_str()).collect::<Vec<_>>());
        let terr_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &pv_attrs, tsh, rev_z);
        let bsrc = shaders::building(&crate::assets::FACADES);
        let bn = names(bld.images.len());
        let bsh = shader(ctx, &bsrc, &bn.iter().map(|s| s.as_str()).collect::<Vec<_>>());
        let bld_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &pv_attrs, bsh, rev_z);
        let dyn_attrs = [
            mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float3),
            mq::VertexAttribute::new("in_nrm", mq::VertexFormat::Float3),
            mq::VertexAttribute::new("in_col", mq::VertexFormat::Float4),
            mq::VertexAttribute::new("in_mat", mq::VertexFormat::Float4),
            mq::VertexAttribute::new("in_loc", mq::VertexFormat::Float4),
        ];
        let dyn_src = shaders::dynamic();
        let dsh = shader(ctx, &dyn_src, &["sky_lut", "s0", "s1", "s2", "s3"]);
        let shadow_params = mq::PipelineParams { depth_test: mq::Comparison::LessOrEqual, depth_write: true, ..Default::default() };
        let spv_src = shaders::shadow_pv();
        let spv = shader(ctx, &spv_src, &[]);
        let shadow_pv_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &pv_attrs, spv, shadow_params);
        let sdv_src = shaders::shadow_dv();
        let sdv = shader(ctx, &sdv_src, &[]);
        let dyn_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &dyn_attrs, dsh, rev_z);
        let shadow_dv_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &dyn_attrs, sdv, shadow_params);
        let overlay_params = mq::PipelineParams {
            depth_test: mq::Comparison::GreaterOrEqual,
            depth_write: false,
            color_blend: Some(mq::BlendState::new(
                mq::Equation::Add,
                mq::BlendFactor::Value(mq::BlendValue::SourceAlpha),
                mq::BlendFactor::OneMinusValue(mq::BlendValue::SourceAlpha),
            )),
            ..Default::default()
        };
        let overlay_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &dyn_attrs, dsh, overlay_params);
        let ribbon_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &dyn_attrs, dsh, mq::PipelineParams { depth_write: true, ..overlay_params });
        let fs_attr = [mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float2)];
        let sky_src = shaders::sky();
        let ssh = shader(ctx, &sky_src, &["sky_lut"]);
        let lut_src = shaders::sky_lut();
        let lsh = shader(ctx, &lut_src, &[]);
        let lut_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &fs_attr, lsh, mq::PipelineParams::default());
        let sky_pipe = ctx.new_pipeline(
            &[mq::BufferLayout::default()],
            &fs_attr,
            ssh,
            mq::PipelineParams { depth_test: mq::Comparison::GreaterOrEqual, depth_write: false, ..Default::default() },
        );
        let comp_src = shaders::combine();
        let csh = shader(ctx, &comp_src, &["hdr", "amb", "ao", "depth", "vol"]);
        let post = |ctx: &mut dyn mq::RenderingBackend, src: String, images: &[&str], blend: bool| {
            let sh = shader(ctx, &src, images);
            let params = if blend {
                mq::PipelineParams {
                    color_blend: Some(mq::BlendState::new(mq::Equation::Add, mq::BlendFactor::One, mq::BlendFactor::One)),
                    ..Default::default()
                }
            } else {
                mq::PipelineParams::default()
            };
            ctx.new_pipeline(&[mq::BufferLayout::default()], &[mq::VertexAttribute::new("in_pos", mq::VertexFormat::Float2)], sh, params)
        };
        let dof_pipe = post(ctx, shaders::dof(), &["comb"], false);
        let down_pipe = post(ctx, shaders::down(), &["src"], false);
        let up_pipe = post(ctx, shaders::up(), &["src"], true);
        let final_pipe = post(ctx, shaders::final_pass(), &["comb", "dof", "bloom", "depth", "amb"], false);
        let ao_src = shaders::ssao();
        let aosh = shader(ctx, &ao_src, &["depth"]);
        let ssao_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &fs_attr, aosh, mq::PipelineParams::default());
        let vol_src = shaders::volume();
        let vsh = shader(ctx, &vol_src, &["depth", "sky_lut", "s0", "s1", "s2", "s3"]);
        let vol_pipe = ctx.new_pipeline(&[mq::BufferLayout::default()], &fs_attr, vsh, mq::PipelineParams::default());
        let comp_pipe = ctx.new_pipeline(
            &[mq::BufferLayout::default()],
            &fs_attr,
            csh,
            mq::PipelineParams { depth_test: mq::Comparison::Always, depth_write: false, ..Default::default() },
        );
        let fs_v: [[f32; 2]; 3] = [[-1.0, -1.0], [3.0, -1.0], [-1.0, 3.0]];
        let fs_vb = ctx.new_buffer(mq::BufferType::VertexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(&fs_v));
        let fs_ib = ctx.new_buffer(mq::BufferType::IndexBuffer, mq::BufferUsage::Immutable, mq::BufferSource::slice(&[0u16, 1, 2]));
        let dyn_lit = mk_dyn(ctx, 65536, 131072);
        let dyn_ov = mk_dyn(ctx, 200_000, 400_000);
        Photo {
            terr_pipe,
            bld_pipe,
            terr,
            terr_n: ti.len() as i32,
            back,
            bld,
            bld_n: bi.len() as i32,
            sky_pipe,
            comp_pipe,
            dof_pipe,
            down_pipe,
            up_pipe,
            final_pipe,
            ssao_pipe,
            vol_pipe,
            lamps: if sf { Vec::new() } else { street_lamps(w) },
            exposure_auto: 6.0,
            rt: None,
            rt_failed: false,
            rt_mesh: rt_mesh(&tv, &ti, &bv, &bi),
            galb,
            prev_model: [Vec3::ZERO; 4],
            rt_reset: true,
            dyn_pipe,
            overlay_pipe,
            ribbon_pipe,
            fs_vb,
            fs_ib,
            dyn_lit,
            dyn_ov,
            targets: None,
            prev_viewproj: Mat4::IDENTITY,
            lut_pipe,
            sky_lut,
            lut_pass,
            sky_light: None,
            shadow_tex,
            shadow_pass,
            shadow_pv_pipe,
            shadow_dv_pipe,
            settings: Settings { exposure: 1.0, fog: PRESETS[0].1, preset: 0, rt_scale: 0.5, rt_out_scale: 0.6667, rt_denoiser: false },
        }
    }

    fn ensure_targets(&mut self, ctx: &mut dyn mq::RenderingBackend, rt: bool) -> (u32, u32, u32, u32) {
        let (sw, sh) = mq::window::screen_size();
        let (ow, oh) = if rt {
            ((sw * self.settings.rt_out_scale) as u32 & !1, (sh * self.settings.rt_out_scale) as u32 & !1)
        } else {
            (sw as u32, sh as u32)
        };
        let (w, h) = if rt { ((sw * self.settings.rt_scale) as u32 & !1, (sh * self.settings.rt_scale) as u32 & !1) } else { (ow, oh) };
        if let Some(t) = &self.targets {
            if (t.w, t.h, t.ow, t.oh, t.rtt.is_some()) == (w, h, ow, oh, rt) {
                return (w, h, ow, oh);
            }
        }
        let mk = |ctx: &mut dyn mq::RenderingBackend, format, w: u32, h: u32, samples| {
            ctx.new_render_texture(mq::TextureParams {
                format,
                width: w.max(1),
                height: h.max(1),
                sample_count: samples,
                min_filter: mq::FilterMode::Linear,
                mag_filter: mq::FilterMode::Linear,
                ..Default::default()
            })
        };
        let (hdr, amb, depth, scene_pass, rtt) = if rt {
            let g: Vec<mq::TextureId> = (0..7).map(|_| mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1)).collect();
            let depth = mk(ctx, mq::TextureFormat::Depth32, w, h, 1);
            let pass = ctx.new_render_pass_mrt(&g, None, Some(depth));
            let r = RtTex {
                gi: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                refl: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                composed: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                noisy: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                spec: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                rough: mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1),
                up: mk(ctx, mq::TextureFormat::RGBA16F, ow, oh, 1),
                g: g.clone(),
            };
            (r.up, g[1], depth, pass, Some(r))
        } else {
            let hdr_ms = mk(ctx, mq::TextureFormat::RGBA16F, w, h, 4);
            let amb_ms = mk(ctx, mq::TextureFormat::RGBA16F, w, h, 4);
            let depth_ms = mk(ctx, mq::TextureFormat::Depth32, w, h, 4);
            let hdr = mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1);
            let amb = mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1);
            let depth = mk(ctx, mq::TextureFormat::Depth32, w, h, 1);
            let pass = ctx.new_render_pass_mrt(&[hdr_ms, amb_ms], Some(&[hdr, amb]), Some(depth_ms));
            ctx.as_metal().expect("photoreal renderer needs Metal").set_depth_resolve(pass, depth);
            (hdr, amb, depth, pass, None)
        };
        let ao = mk(ctx, mq::TextureFormat::RGBA8, w / 2, h / 2, 1);
        let ao_pass = ctx.new_render_pass(ao, None);
        let vol = mk(ctx, mq::TextureFormat::RGBA16F, w / 2, h / 2, 1);
        let vol_pass = ctx.new_render_pass(vol, None);
        let tex = |ctx: &mut dyn mq::RenderingBackend, w: u32, h: u32| {
            let t = mk(ctx, mq::TextureFormat::RGBA16F, w, h, 1);
            (t, ctx.new_render_pass(t, None))
        };
        let (comb, comb_pass) = tex(ctx, ow, oh);
        let (dof, dof_pass) = tex(ctx, ow / 2, oh / 2);
        let bloom = (2..6)
            .map(|k| {
                let (bw, bh) = ((ow >> k).max(1), (oh >> k).max(1));
                let (t, p) = tex(ctx, bw, bh);
                (t, p, bw, bh)
            })
            .collect();
        self.targets = Some(Targets { w, h, ow, oh, hdr, amb, depth, scene_pass, ao, ao_pass, vol, vol_pass, comb, comb_pass, dof, dof_pass, bloom, rtt });
        (w, h, ow, oh)
    }

    pub fn draw(&mut self, f: &FrameIn) {
        let mut gl = unsafe { get_internal_gl() };
        gl.flush();
        let ctx = gl.quad_context;
        let use_rt = f.rt && !self.rt_failed;
        if use_rt && self.rt.is_none() {
            let m = ctx.as_metal().unwrap();
            let (dev, q) = (m.raw_device(), m.raw_command_queue());
            self.rt = crate::rt::Rt::new(dev, q, &shaders::trace(), &self.rt_mesh.0, &self.rt_mesh.1, &self.rt_mesh.2);
            self.rt_failed = self.rt.is_none();
            self.rt_reset = true;
        }
        let use_rt = use_rt && self.rt.is_some();
        let (w, h, ow, oh) = self.ensure_targets(ctx, use_rt);
        let aspect = ow as f32 / oh as f32;
        let view = Mat4::look_at_rh(f.cam_pos, f.cam_target, f.cam_up);
        let proj = Mat4::perspective_infinite_reverse_rh(f.fovy, aspect, if f.cockpit { 0.05 } else { 0.5 });
        let vp_nj = proj * view;
        let frame_no = self.rt.as_ref().map(|r| r.frame).unwrap_or(0);
        let jit = if use_rt { crate::rt::jitter(frame_no) } else { Vec2::ZERO };
        let proj_j = Mat4::from_translation(vec3(2.0 * jit.x / w as f32, -2.0 * jit.y / h as f32, 0.0)) * proj;
        let vp = proj_j * view;
        if self.prev_model[1] == Vec3::ZERO {
            self.prev_model = f.model;
        }
        let haze = self.settings.fog.haze;
        if self.sky_light.as_ref().map(|s| (s.0, s.1)) != Some((f.sun, haze)) {
            let sl = crate::atmos::sky_light(f.sun, haze, vec3(0.2, 0.2, 0.19));
            self.sky_light = Some((f.sun, haze, sl));
        }
        let sl = &self.sky_light.as_ref().unwrap().2;
        let mut sh = [[0.0f32; 4]; 9];
        for k in 0..9 {
            sh[k] = sl.sh[k].extend(0.0).to_array();
        }
        let night = (1.0 - ((f.sun.z.asin().to_degrees() + 4.0) / 10.0)).clamp(0.0, 1.0);
        let fg = self.settings.fog;
        let lum = |c: Vec3| 0.2126 * c.x + 0.7152 * c.y + 0.0722 * c.z;
        let e_up = lum(sl.sun_col) * f.sun.z.max(0.0) + lum(crate::atmos::sh_eval(&sl.sh, Vec3::Z));
        let target = (6.0 * (0.71 / (e_up + 0.004)).sqrt()).min(200.0);
        self.exposure_auto += (target - self.exposure_auto) * 0.08;
        let exposure = self.exposure_auto * self.settings.exposure;
        let cascades: [(Mat4, f32); 4] = std::array::from_fn(|c| {
            cascade(view, f.fovy, aspect, if c == 0 { 0.5 } else { SPLITS[c - 1] }, SPLITS[c], f.sun)
        });
        let mut u = FrameU {
            viewproj: vp.to_cols_array(),
            inv_viewproj: vp.inverse().to_cols_array(),
            prev_viewproj: self.prev_viewproj.to_cols_array(),
            cam: [f.cam_pos.x, f.cam_pos.y, f.cam_pos.z, f.time],
            sun: [f.sun.x, f.sun.y, f.sun.z, exposure],
            sun_col: [sl.sun_col.x, sl.sun_col.y, sl.sun_col.z, 0.0075],
            screen: [w as f32, h as f32, 1.0 / w as f32, 1.0 / h as f32],
            params: [haze, 0.0, 0.0, 0.0],
            amb: sl.amb.extend(0.0).to_array(),
            sh,
            shadow: cascades.map(|c| c.0.to_cols_array()),
            splits: SPLITS,
            shadow_texel: cascades.map(|c| c.1),
            prop: f.prop,
            flags: [if f.cockpit { 1.0 } else { 0.0 }, 0.0, night, if self.lamps.is_empty() { 1.0 } else { 0.0 }],
            fog: [fg.density, fg.falloff, fg.anisotropy, fg.valley_top],
            fog2: [fg.valley_density, fg.cloud_cover, fg.cloud_base, fg.cloud_top],
            land_pos: f.land_pos,
            land_dir: f.land_dir,
            nav: f.nav,
            post0: [f.lens.focus, f.lens.focal_mm * 1e-3, f.lens.focal_mm * 1e-3 / f.lens.fstop, 0.024],
            post1: [if f.lens.footage { 1.0 } else { 0.0 }, if f.lens.tilt_shift { 1.0 } else { 0.0 }, f.lens.cats_eye, if f.lens.hexagon { 1.0 } else { 0.0 }],
            post2: [
                if f.lens.footage { f.lens.shutter / 360.0 / 30.0 } else { 0.0 },
                f.lens.frame_dt,
                if f.lens.footage { 0.06 } else { 0.035 },
                if f.lens.footage { -0.22 } else { 0.0 },
            ],
            post3: [f.time * 0.37, if f.lens.footage { 0.004 } else { 0.0 }, if f.lens.footage { 0.75 } else { 0.35 }, 40.0],
            post4: [ow as f32, oh as f32, 1.0 / ow as f32, 1.0 / oh as f32],
            post5: [0.0, if use_rt { 1.0 } else { 0.0 }, frame_no as f32, 0.0],
            viewproj_nj: vp_nj.to_cols_array(),
            prev_model: self.prev_model.map(|v| v.extend(0.0).to_array()),
            post6: {
                let (fw, fh) = mq::window::screen_size();
                [fw, fh, 1.0 / fw, 1.0 / fh]
            },
        };
        self.prev_model = f.model;
        self.prev_viewproj = vp_nj;
        let t = self.targets.as_ref().unwrap();

        let upload = |ctx: &mut dyn mq::RenderingBackend, b: &DynBuf, v: &[DV], i: &[u32]| -> i32 {
            if i.is_empty() {
                return 0;
            }
            let nv = v.len().min(b.cap_v);
            let ni = i.len().min(b.cap_i);
            ctx.buffer_update(b.vb, mq::BufferSource::slice(&v[..nv]));
            ctx.buffer_update(b.ib, mq::BufferSource::slice(&i[..ni]));
            ni as i32
        };
        let n_lit = upload(ctx, &self.dyn_lit, f.dyn_lit.0, f.dyn_lit.1);
        // Ribbons first (they write depth), then the glow sprites, soft sprites and prop disc, which are mostly
        // see-through and don't.
        let (ov, oi) = f.dyn_overlay;
        let (rib, rest): (Vec<&[u32]>, Vec<&[u32]>) =
            oi.chunks(3).partition(|t| ov[t[0] as usize].mat[0] == K_OVERLAY && ov[t[0] as usize].mat[1] != OVERLAY_SOFT);
        let n_ov = upload(ctx, &self.dyn_ov, ov, &[rib.concat(), rest.concat()].concat());
        let n_rib = (rib.len() as i32 * 3).min(n_ov);

        if use_rt {
            let (v, i) = f.dyn_lit;
            let pos: Vec<[f32; 3]> = v.iter().map(|d| d.pos).collect();
            let tris: Vec<crate::rt::Tri> = i
                .chunks(3)
                .map(|c| {
                    let (a, b, cc) = (Vec3::from(pos[c[0] as usize]), Vec3::from(pos[c[1] as usize]), Vec3::from(pos[c[2] as usize]));
                    let n = (b - a).cross(cc - a).normalize_or_zero();
                    crate::rt::Tri { alb: [0.62, 0.62, 0.6, 1.0], n: n.extend(0.0).to_array() }
                })
                .collect();
            let cb = ctx.as_metal().unwrap().raw_command_buffer();
            self.rt.as_mut().unwrap().update(cb, &pos, i, &tris);
        }
        let fs_bind = |images: Vec<mq::TextureId>| mq::Bindings { vertex_buffers: vec![self.fs_vb], index_buffer: self.fs_ib, images };
        ctx.begin_pass(Some(self.lut_pass), mq::PassAction::Nothing);
        ctx.apply_pipeline(&self.lut_pipe);
        ctx.apply_bindings(&fs_bind(vec![]));
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, 3, 1);
        ctx.end_render_pass();

        for c in 0..4 {
            ctx.begin_pass(Some(self.shadow_pass[c]), mq::PassAction::Clear { color: None, depth: Some(1.0), stencil: None });
            u.params[1] = c as f32;
            ctx.apply_pipeline(&self.shadow_pv_pipe);
            for (b, n) in [(&self.terr, self.terr_n), (&self.bld, self.bld_n)] {
                ctx.apply_bindings(&mq::Bindings { vertex_buffers: b.vertex_buffers.clone(), index_buffer: b.index_buffer, images: vec![] });
                ctx.apply_uniforms(mq::UniformsSource::table(&u));
                ctx.draw(0, n, 1);
            }
            if n_lit > 0 {
                ctx.apply_pipeline(&self.shadow_dv_pipe);
                ctx.apply_bindings(&mq::Bindings { vertex_buffers: vec![self.dyn_lit.vb], index_buffer: self.dyn_lit.ib, images: vec![] });
                ctx.apply_uniforms(mq::UniformsSource::table(&u));
                ctx.draw(0, n_lit, 1);
            }
            ctx.end_render_pass();
        }

        ctx.begin_pass(Some(t.scene_pass), mq::PassAction::Clear { color: Some((0.0, 0.0, 0.0, 1.0)), depth: Some(0.0), stencil: None });
        for (p, b, n) in [(&self.terr_pipe, &self.terr, self.terr_n), (&self.bld_pipe, &self.bld, self.bld_n)] {
            ctx.apply_pipeline(p);
            ctx.apply_bindings(b);
            ctx.apply_uniforms(mq::UniformsSource::table(&u));
            ctx.draw(0, n, 1);
        }
        if let Some((b, n)) = &self.back {
            ctx.apply_pipeline(&self.terr_pipe);
            ctx.apply_bindings(b);
            ctx.apply_uniforms(mq::UniformsSource::table(&u));
            ctx.draw(0, *n, 1);
        }
        if n_lit > 0 {
            ctx.apply_pipeline(&self.dyn_pipe);
            let mut im = vec![self.sky_lut];
            im.extend(&self.shadow_tex);
            ctx.apply_bindings(&mq::Bindings { vertex_buffers: vec![self.dyn_lit.vb], index_buffer: self.dyn_lit.ib, images: im });
            ctx.apply_uniforms(mq::UniformsSource::table(&u));
            ctx.draw(0, n_lit, 1);
        }
        // Sky last: only where nothing was drawn (depth still 0).
        ctx.apply_pipeline(&self.sky_pipe);
        ctx.apply_bindings(&fs_bind(vec![self.sky_lut]));
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, 3, 1);
        for (p, a, b) in [(&self.ribbon_pipe, 0, n_rib), (&self.overlay_pipe, n_rib, n_ov)] {
            if b > a {
                ctx.apply_pipeline(p);
                ctx.apply_bindings(&mq::Bindings { vertex_buffers: vec![self.dyn_ov.vb], index_buffer: self.dyn_ov.ib, images: vec![self.sky_lut] });
                ctx.apply_uniforms(mq::UniformsSource::table(&u));
                ctx.draw(a, b - a, 1);
            }
        }
        ctx.end_render_pass();

        if let (Some(r), Some(rt)) = (&t.rtt, self.rt.as_mut()) {
            let m = ctx.as_metal().unwrap();
            let raw = |id: mq::TextureId| m.raw_texture(id);
            let inputs = [raw(r.g[0]), raw(r.g[1]), raw(r.g[2]), raw(r.g[3]), raw(r.g[4]), raw(r.g[5]), raw(t.depth), raw(self.sky_lut), raw(self.galb)];
            let outputs = [raw(r.noisy), raw(r.spec), raw(r.rough), raw(r.gi), raw(r.refl)];
            let denoiser = self.settings.rt_denoiser;
            rt.use_denoiser = denoiser;
            let color = if denoiser { r.noisy } else { r.composed };
            let fx = [raw(color), raw(t.depth), raw(r.g[6]), raw(r.g[4]), raw(r.spec), raw(r.g[5]), raw(r.rough), raw(r.up)];
            let comp = [raw(r.g[0]), raw(r.g[1]), raw(r.g[2]), raw(r.g[3]), raw(r.g[4]), raw(r.g[5]), raw(t.depth), raw(r.gi), raw(r.refl), raw(r.composed)];
            let cb = m.raw_command_buffer();
            let bytes = unsafe { std::slice::from_raw_parts(&u as *const FrameU as *const u8, std::mem::size_of::<FrameU>()) };
            rt.trace(cb, bytes, &inputs, &outputs, w, h);
            if !denoiser {
                rt.compose(cb, bytes, &comp, w, h);
            }
            rt.upscale(cb, &fx, (w, h, ow, oh), jit, view, proj, self.rt_reset);
            self.rt_reset = false;
        } else {
            ctx.begin_pass(Some(t.ao_pass), mq::PassAction::Nothing);
            ctx.apply_pipeline(&self.ssao_pipe);
            ctx.apply_bindings(&fs_bind(vec![t.depth]));
            ctx.apply_uniforms(mq::UniformsSource::table(&u));
            ctx.draw(0, 3, 1);
            ctx.end_render_pass();
        }

        ctx.begin_pass(Some(t.vol_pass), mq::PassAction::Nothing);
        ctx.apply_pipeline(&self.vol_pipe);
        let mut vimg = vec![t.depth, self.sky_lut];
        vimg.extend(&self.shadow_tex);
        ctx.apply_bindings(&fs_bind(vimg));
        ctx.apply_uniforms(mq::UniformsSource::table(&u));
        ctx.draw(0, 3, 1);
        ctx.end_render_pass();

        let pass = |ctx: &mut dyn mq::RenderingBackend, pass: Option<mq::RenderPass>, pipe: &mq::Pipeline, images: Vec<mq::TextureId>, u: &FrameU, load: bool| {
            match pass {
                Some(p) => ctx.begin_pass(Some(p), if load { mq::PassAction::Nothing } else { mq::PassAction::clear_color(0.0, 0.0, 0.0, 0.0) }),
                None => ctx.begin_default_pass(mq::PassAction::Nothing),
            }
            ctx.apply_pipeline(pipe);
            ctx.apply_bindings(&mq::Bindings { vertex_buffers: vec![self.fs_vb], index_buffer: self.fs_ib, images });
            ctx.apply_uniforms(mq::UniformsSource::table(u));
            ctx.draw(0, 3, 1);
            ctx.end_render_pass();
        };
        pass(ctx, Some(t.comb_pass), &self.comp_pipe, vec![t.hdr, t.amb, t.ao, t.depth, t.vol], &u, false);
        pass(ctx, Some(t.dof_pass), &self.dof_pipe, vec![t.comb], &u, false);
        let mut src = (t.dof, ow / 2, oh / 2);
        for (k, b) in t.bloom.iter().enumerate() {
            u.params = [u.params[0], if k == 0 { 1.0 } else { 0.0 }, 1.0 / src.1 as f32, 1.0 / src.2 as f32];
            pass(ctx, Some(b.1), &self.down_pipe, vec![src.0], &u, false);
            src = (b.0, b.2, b.3);
        }
        for k in (0..t.bloom.len() - 1).rev() {
            let (lo, hi) = (&t.bloom[k + 1], &t.bloom[k]);
            u.params = [u.params[0], 0.0, 1.0 / lo.2 as f32, 1.0 / lo.3 as f32];
            pass(ctx, Some(hi.1), &self.up_pipe, vec![lo.0], &u, true);
        }
        pass(ctx, None, &self.final_pipe, vec![t.comb, t.dof, t.bloom[0].0, t.depth, t.amb], &u, true);
    }
}

fn street_lamps(w: &World) -> Vec<Vec3> {
    let mut v = Vec::new();
    for k in 0..=20usize {
        let sx = street_x(k) as f32;
        let off = (w.street_w[k] / 2.0 - 2.5) as f32;
        let mut a = -CITY_HALF as f32 + 15.0;
        while a < CITY_HALF as f32 {
            for side in [-1.0f32, 1.0] {
                for (x, y) in [(sx + side * off, a), (a, sx + side * off)] {
                    v.push(vec3(x, y, w.terrain(x as f64, y as f64) as f32 + 8.0));
                }
            }
            a += 30.0;
        }
    }
    v
}

/// Camera-facing glow sprites (dynamic-shader kind 7): HDR colour, soft disc.
pub fn glow(ov: &mut Vec<DV>, oi: &mut Vec<u32>, c: Vec3, r: f32, col: [f32; 4], right: Vec3, up: Vec3) {
    let base = ov.len() as u32;
    for (sx, sy) in [(-1.0f32, -1.0f32), (1.0, -1.0), (1.0, 1.0), (-1.0, 1.0)] {
        let p = c + (right * sx + up * sy) * r;
        ov.push(DV { pos: p.to_array(), nrm: [0.0; 3], col, mat: [7.0, 0.0, 0.0, 0.0], loc: [sx, sy, 0.0, 0.0] });
    }
    oi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
}

impl Photo {
    /// Street-lamp sprites for the overlay pass at night.
    pub fn lamp_sprites(&self, ov: &mut Vec<DV>, oi: &mut Vec<u32>, cam: Vec3, right: Vec3, up: Vec3, night: f32) {
        if night <= 0.0 {
            return;
        }
        for &l in &self.lamps {
            let d = (l - cam).length();
            if d < 1800.0 {
                let r = 0.3 + d * 0.0012;
                glow(ov, oi, l, r, [5.0 * night, 3.5 * night, 1.9 * night, 1.0], right, up);
            }
        }
    }
}

/// Static triangles for the ray-tracing BLAS, with an approximate albedo per triangle.
fn rt_mesh(tv: &[PV], ti: &[u32], bv: &[PV], bi: &[u32]) -> (Vec<[f32; 3]>, Vec<u32>, Vec<crate::rt::Tri>) {
    let mut pos: Vec<[f32; 3]> = tv.iter().map(|v| v.pos).collect();
    let base = pos.len() as u32;
    pos.extend(bv.iter().map(|v| v.pos));
    let mut idx = ti.to_vec();
    idx.extend(bi.iter().map(|i| i + base));
    const FACADE_ALB: [[f32; 3]; 6] = [[0.06, 0.08, 0.1], [0.28, 0.31, 0.33], [0.24, 0.19, 0.16], [0.3, 0.2, 0.16], [0.33, 0.31, 0.29], [0.24, 0.17, 0.13]];
    let tris = idx
        .chunks(3)
        .map(|c| {
            let (a, b, cc) = (Vec3::from(pos[c[0] as usize]), Vec3::from(pos[c[1] as usize]), Vec3::from(pos[c[2] as usize]));
            let n = (b - a).cross(cc - a).normalize_or_zero();
            let alb = if (c[0] as usize) < tv.len() {
                [0.0, 0.0, 0.0, 0.0]
            } else {
                let v = &bv[c[0] as usize - tv.len()];
                let base = match v.mat[0] {
                    k if k == K_FACADE => FACADE_ALB[(v.uv[0] as usize).min(5)],
                    k if k == K_ROOF => [0.22, 0.21, 0.2],
                    _ => [0.4, 0.4, 0.4],
                };
                [base[0] * v.col[0], base[1] * v.col[1], base[2] * v.col[2], 1.0]
            };
            crate::rt::Tri { alb, n: n.extend(0.0).to_array() }
        })
        .collect();
    (pos, idx, tris)
}

const SHADOW_RES: u32 = 2048;
const SPLITS: [f32; 4] = [35.0, 140.0, 520.0, 2400.0];

/// Light view-projection for one view-frustum slice, snapped to whole texels so shadows don't shimmer.
fn cascade(view: Mat4, fovy: f32, aspect: f32, near: f32, far: f32, sun: Vec3) -> (Mat4, f32) {
    let inv = (Mat4::perspective_rh(fovy, aspect, near, far) * view).inverse();
    let mut corners = [Vec3::ZERO; 8];
    for (k, c) in corners.iter_mut().enumerate() {
        let ndc = vec4(if k & 1 == 0 { -1.0 } else { 1.0 }, if k & 2 == 0 { -1.0 } else { 1.0 }, if k & 4 == 0 { 0.0 } else { 1.0 }, 1.0);
        let p = inv * ndc;
        *c = p.truncate() / p.w;
    }
    let center = corners.iter().fold(Vec3::ZERO, |a, &b| a + b) / 8.0;
    let r = corners.iter().map(|c| (*c - center).length()).fold(0.0f32, f32::max).ceil();
    let up = if sun.z.abs() > 0.99 { Vec3::Y } else { Vec3::Z };
    let lv = Mat4::look_at_rh(center + sun * 4000.0, center, up);
    let texel = 2.0 * r / SHADOW_RES as f32;
    let lc = lv.transform_point3(center);
    let snap = vec3((lc.x / texel).round() * texel - lc.x, (lc.y / texel).round() * texel - lc.y, 0.0);
    let proj = Mat4::orthographic_rh(-r + snap.x, r + snap.x, -r + snap.y, r + snap.y, 1.0, 9000.0);
    (proj * lv, texel)
}

fn building_mesh(w: &World) -> (Vec<PV>, Vec<u32>) {
    let mut bv: Vec<PV> = Vec::with_capacity(w.boxes.len() * 40);
    let mut bi: Vec<u32> = Vec::with_capacity(w.boxes.len() * 60);
    let mut quad = |bv: &mut Vec<PV>, n: [f32; 3], q: [[f32; 3]; 4], col: [f32; 3], uv: [f32; 2], mat: [f32; 4], fac: [f32; 4]| {
        let base = bv.len() as u32;
        for p in q {
            bv.push(PV { pos: p, nrm: n, col, uv, mat, fac });
        }
        bi.extend_from_slice(&[base, base + 1, base + 2, base, base + 2, base + 3]);
    };
    for b in &w.boxes {
        let seed = building_seed(b);
        let c = building_albedo(b);
        let lum = 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
        let tint = [0.7 + 0.3 * c[0] / lum, 0.7 + 0.3 * c[1] / lum, 0.7 + 0.3 * c[2] / lum];
        let zc = w.terrain(0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1)) as f32;
        let grounded = b.z0 < zc as f64 + 0.5;
        let z_base = if grounded { zc } else { b.z0 as f32 };
        let h = b.z1 as f32 - z_base;
        let pick = |opts: &[usize]| opts[((seed * 977.0) as usize) % opts.len()];
        let ft = if h > 70.0 {
            pick(&[0, 1, 2, 0, 1])
        } else if h > 30.0 {
            pick(&[1, 2, 3, 4, 5])
        } else {
            pick(&[3, 4, 5])
        };
        let (_, cols, rows, _) = crate::assets::FACADES[ft];
        let floor_h = if ft >= 3 { 3.2 } else { 3.6 } * (0.95 + 0.1 * (seed * 31.0).fract());
        let col_nom = floor_h * rows / cols;
        let (x0, x1, y0, y1, z0, z1) = (b.x0 as f32, b.x1 as f32, b.y0 as f32, b.y1 as f32, b.z0 as f32, b.z1 as f32);
        let mat_f = [K_FACADE, seed, z_base, z1];
        let uv = [ft as f32, if grounded { 1.0 } else { 0.0 }];
        let walls: [([f32; 3], [[f32; 3]; 4]); 4] = [
            ([1.0, 0.0, 0.0], [[x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [x1, y0, z1]]),
            ([-1.0, 0.0, 0.0], [[x0, y1, z0], [x0, y0, z0], [x0, y0, z1], [x0, y1, z1]]),
            ([0.0, 1.0, 0.0], [[x1, y1, z0], [x0, y1, z0], [x0, y1, z1], [x1, y1, z1]]),
            ([0.0, -1.0, 0.0], [[x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1]]),
        ];
        for (n, q) in walls {
            let right = [-n[1], n[0]];
            let sv: Vec<f32> = q.iter().map(|p| p[0] * right[0] + p[1] * right[1]).collect();
            let s0 = sv.iter().cloned().fold(f32::INFINITY, f32::min);
            let len = sv.iter().cloned().fold(f32::NEG_INFINITY, f32::max) - s0;
            let ncol = (len / col_nom).round().max(1.0);
            quad(&mut bv, n, q, tint, uv, mat_f, [s0, len / ncol, floor_h, len]);
        }
        let roof_t = if (seed * 53.0).fract() < 0.55 { 0.0 } else { 1.0 };
        let rg = 0.55 + 0.6 * (seed * 71.0).fract();
        let roof_tint = [rg * (0.85 + 0.15 * tint[0]), rg * (0.85 + 0.15 * tint[1]), rg * (0.85 + 0.15 * tint[2])];
        quad(&mut bv, [0.0, 0.0, 1.0], [[x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1]], roof_tint, [0.0; 2], [K_ROOF, seed, roof_t, 0.0], [x0, y0, x1, y1]);
        // Render-only rooftop units, low and inset so they stay inside the filter's clearance margin.
        let (wx, wy) = (x1 - x0, y1 - y0);
        if wx > 12.0 && wy > 12.0 {
            let mut r = Rng::new((seed * 1e6) as u64 + 7);
            let n = 1 + (r.f() * 4.0) as usize;
            for _ in 0..n {
                let (sx, sy) = (r.range(1.2, 3.0) as f32, r.range(1.2, 3.0) as f32);
                let sz = r.range(0.8, 1.6) as f32;
                let cx = x0 + 3.0 + sx + r.f() as f32 * (wx - 6.0 - 2.0 * sx).max(0.0);
                let cy = y0 + 3.0 + sy + r.f() as f32 * (wy - 6.0 - 2.0 * sy).max(0.0);
                let metal = if r.f() < 0.5 { 0.6 } else { 0.0 };
                let g = r.range(0.75, 1.05) as f32;
                let col = [g, g, g * 1.02];
                let (a0, a1, b0, b1, c0, c1) = (cx - sx, cx + sx, cy - sy, cy + sy, z1, z1 + sz);
                let m = [K_CLUTTER, seed, metal, 0.0];
                let faces: [([f32; 3], [[f32; 3]; 4]); 5] = [
                    ([1.0, 0.0, 0.0], [[a1, b0, c0], [a1, b1, c0], [a1, b1, c1], [a1, b0, c1]]),
                    ([-1.0, 0.0, 0.0], [[a0, b1, c0], [a0, b0, c0], [a0, b0, c1], [a0, b1, c1]]),
                    ([0.0, 1.0, 0.0], [[a1, b1, c0], [a0, b1, c0], [a0, b1, c1], [a1, b1, c1]]),
                    ([0.0, -1.0, 0.0], [[a0, b0, c0], [a1, b0, c0], [a1, b0, c1], [a0, b0, c1]]),
                    ([0.0, 0.0, 1.0], [[a0, b0, c1], [a1, b0, c1], [a1, b1, c1], [a0, b1, c1]]),
                ];
                for (fnrm, q) in faces {
                    quad(&mut bv, fnrm, q, col, [0.0; 2], m, [0.0; 4]);
                }
            }
        }
    }
    (bv, bi)
}

pub fn save_capture(path: &str, w: u32, h: u32, rgba: Vec<u8>) {
    // `export_png` flips rows (it expects GL's bottom-up readback).
    let row = w as usize * 4;
    let mut flipped = vec![0u8; rgba.len()];
    for y in 0..h as usize {
        flipped[y * row..(y + 1) * row].copy_from_slice(&rgba[(h as usize - 1 - y) * row..(h as usize - y) * row]);
    }
    Image { bytes: flipped, width: w as u16, height: h as u16 }.export_png(path);
}

#[allow(dead_code)]
pub fn lin_srgb(c: f32) -> f32 {
    lin_to_srgb(c)
}
