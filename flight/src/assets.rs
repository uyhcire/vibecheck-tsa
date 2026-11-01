//! Texture sets written by `assets/textures/fetch.py`.

use macroquad::miniquad as mq;

#[derive(Clone, Copy)]
pub struct TexSet {
    pub alb: mq::TextureId,
    pub nrm: mq::TextureId,
    pub orm: mq::TextureId,
}

pub const FACADES: [(&str, f32, f32, bool); 6] = [
    ("facade_glass", 16.0, 10.0, true),
    ("facade_grid", 14.0, 8.0, true),
    ("facade_office", 32.0, 32.0, false),
    ("facade_brick", 6.0, 6.0, false),
    ("facade_stone", 6.0, 6.0, false),
    ("facade_brown", 6.0, 6.0, false),
];
pub const GROUND: [&str; 4] = ["asphalt", "grass", "rock", "concrete"];
pub const ROOF: [&str; 2] = ["gravel", "concrete"];

fn dir() -> std::path::PathBuf {
    let here = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("assets/textures");
    if here.exists() {
        return here;
    }
    std::env::current_exe().ok().and_then(|e| e.parent().map(|p| p.join("assets/textures"))).unwrap_or(here)
}

fn decode(path: &std::path::Path) -> Option<(u32, u32, Vec<u8>)> {
    let bytes = std::fs::read(path).ok()?;
    let img = image::load_from_memory(&bytes).ok()?.to_rgba8();
    Some((img.width(), img.height(), img.into_raw()))
}

fn upload(ctx: &mut dyn mq::RenderingBackend, w: u32, h: u32, px: &[u8]) -> mq::TextureId {
    let t = ctx.new_texture(
        mq::TextureAccess::Static,
        mq::TextureSource::Bytes(px),
        mq::TextureParams {
            format: mq::TextureFormat::RGBA8,
            wrap: mq::TextureWrap::Repeat,
            min_filter: mq::FilterMode::Linear,
            mag_filter: mq::FilterMode::Linear,
            mipmap_filter: mq::MipmapFilterMode::Linear,
            width: w,
            height: h,
            allocate_mipmaps: true,
            ..Default::default()
        },
    );
    ctx.texture_generate_mipmaps(t);
    t
}

fn fallback(name: &str, cols: f32, rows: f32) -> [Vec<u8>; 3] {
    const N: usize = 256;
    let mut a = vec![0u8; N * N * 4];
    let mut n = vec![0u8; N * N * 4];
    let mut o = vec![0u8; N * N * 4];
    let base: [u8; 3] = match name {
        "asphalt" => [60, 60, 64],
        "grass" => [90, 120, 60],
        "rock" => [120, 116, 110],
        "gravel" => [130, 126, 120],
        _ => [170, 166, 158],
    };
    let mut r = cityflight::world::Rng::new(name.len() as u64 * 977);
    for j in 0..N {
        for i in 0..N {
            let k = (j * N + i) * 4;
            let jit = (r.f() * 24.0) as u8;
            let (fu, fv) = ((i as f32 / N as f32 * cols).fract(), (j as f32 / N as f32 * rows).fract());
            let win = name.starts_with("facade") && (0.15..0.85).contains(&fu) && (0.25..0.85).contains(&fv);
            let c = if win { [40, 52, 64] } else { base };
            a[k..k + 4].copy_from_slice(&[c[0].saturating_add(jit / 2), c[1].saturating_add(jit / 2), c[2].saturating_add(jit / 2), 255]);
            n[k..k + 4].copy_from_slice(&[128, 128, 255, 255]);
            o[k..k + 4].copy_from_slice(&[255, if win { 10 } else { 190 }, 0, 255]);
        }
    }
    [a, n, o]
}

pub fn load(ctx: &mut dyn mq::RenderingBackend, name: &str, cols: f32, rows: f32) -> TexSet {
    let d = dir().join(name);
    let maps = ["albedo.jpg", "normal.jpg", "orm.jpg"].map(|f| decode(&d.join(f)));
    let ids: Vec<mq::TextureId> = if maps.iter().all(|m| m.is_some()) {
        maps.into_iter().map(|m| m.unwrap()).map(|(w, h, px)| upload(ctx, w, h, &px)).collect()
    } else {
        eprintln!("textures: {name} not found under {}, using a procedural stand-in", d.display());
        fallback(name, cols, rows).iter().map(|px| upload(ctx, 256, 256, px)).collect()
    };
    TexSet { alb: ids[0], nrm: ids[1], orm: ids[2] }
}
