//! Same model as `ATMOS` in `shaders.rs`.

use macroquad::prelude::*;

const RG: f32 = 6_360e3;
const RT: f32 = 6_460e3;
const BR: Vec3 = Vec3::new(5.802e-6, 13.558e-6, 33.1e-6);
const BM_S: f32 = 3.996e-6;
const BM_E: f32 = 4.40e-6;
const BO: Vec3 = Vec3::new(0.650e-6, 1.881e-6, 0.085e-6);
const HR: f32 = 8000.0;
const HM: f32 = 1200.0;
pub const MIE_G: f32 = 0.8;

fn extinction(h: f32, ms: f32) -> Vec3 {
    let o = (1.0 - (h - 25_000.0).abs() / 15_000.0).max(0.0);
    BR * (-h / HR).exp() + Vec3::splat(BM_E * ms * (-h / HM).exp()) + BO * o
}

fn ray_top(h: f32, mu: f32) -> f32 {
    let r = RG + h;
    -r * mu + (r * r * (mu * mu - 1.0) + RT * RT).max(0.0).sqrt()
}

fn hits_ground(h: f32, mu: f32) -> bool {
    let r = RG + h;
    mu < 0.0 && r * r * (mu * mu - 1.0) + RG * RG >= 0.0
}

pub fn transmittance(h: f32, mu: f32, ms: f32) -> Vec3 {
    if hits_ground(h, mu) {
        return Vec3::ZERO;
    }
    let r = RG + h;
    let l = ray_top(h, mu);
    let n = 24;
    let dt = l / n as f32;
    let mut od = Vec3::ZERO;
    for i in 0..n {
        let t = (i as f32 + 0.5) * dt;
        let hh = (r * r + t * t + 2.0 * r * mu * t).sqrt() - RG;
        od += extinction(hh, ms) * dt;
    }
    (-od).exp()
}

fn phase_r(nu: f32) -> f32 {
    3.0 / (16.0 * std::f32::consts::PI) * (1.0 + nu * nu)
}

pub fn phase_m(nu: f32) -> f32 {
    let g = MIE_G;
    let k = 3.0 / (8.0 * std::f32::consts::PI) * (1.0 - g * g) / (2.0 + g * g);
    k * (1.0 + nu * nu) / (1.0 + g * g - 2.0 * g * nu).powf(1.5)
}

/// Single-scattered sky radiance for unit solar irradiance, plus an isotropic multiple-scattering term `amb`.
pub fn sky_radiance(h: f32, dir: Vec3, sun: Vec3, ms: f32, amb: Vec3) -> Vec3 {
    let r = RG + h;
    let mu = dir.z;
    let t_end = if hits_ground(h, mu) {
        let disc = r * r * (mu * mu - 1.0) + RG * RG;
        -r * mu - disc.sqrt()
    } else {
        ray_top(h, mu)
    };
    let nu = dir.dot(sun);
    let (pr, pm) = (phase_r(nu), phase_m(nu));
    let n = 24;
    let dt = t_end / n as f32;
    let mut tr = Vec3::ONE;
    let mut l = Vec3::ZERO;
    for i in 0..n {
        let t = (i as f32 + 0.5) * dt;
        let p = vec3(0.0, 0.0, r) + dir * t;
        let hh = p.length() - RG;
        let up = p / p.length();
        let sr = BR * (-hh / HR).exp();
        let sm = BM_S * ms * (-hh / HM).exp();
        let ext = extinction(hh, ms);
        let tsun = transmittance(hh, up.dot(sun), ms);
        let s = (sr * pr + Vec3::splat(sm * pm)) * tsun + (sr + Vec3::splat(sm)) * amb;
        let step_t = (-ext * dt).exp();
        l += tr * (s - s * step_t) / ext;
        tr *= step_t;
    }
    l
}

/// Sky lighting for a given sun: the sun colour at the ground and the irradiance SH (cosine-convolved).
pub struct SkyLight {
    pub sun_col: Vec3,
    pub sh: [Vec3; 9],
    pub amb: Vec3,
}

fn sh_basis(d: Vec3) -> [f32; 9] {
    [
        0.282095,
        0.488603 * d.y,
        0.488603 * d.z,
        0.488603 * d.x,
        1.092548 * d.x * d.y,
        1.092548 * d.y * d.z,
        0.315392 * (3.0 * d.z * d.z - 1.0),
        1.092548 * d.x * d.z,
        0.546274 * (d.x * d.x - d.y * d.y),
    ]
}

pub fn sky_light(sun: Vec3, ms: f32, ground_albedo: Vec3) -> SkyLight {
    let h = 200.0;
    let sun_col = transmittance(h, sun.z, ms);
    let mut amb = Vec3::ZERO;
    let mut sh = [Vec3::ZERO; 9];
    for pass in 0..2 {
        sh = [Vec3::ZERO; 9];
        let mut avg = Vec3::ZERO;
        let (nt, np) = (12, 24);
        let mut wsum = 0.0;
        for i in 0..nt {
            let ct = 1.0 - 2.0 * (i as f32 + 0.5) / nt as f32;
            let st = (1.0 - ct * ct).sqrt();
            for j in 0..np {
                let ph = (j as f32 + 0.5) / np as f32 * std::f32::consts::TAU;
                let d = vec3(st * ph.cos(), st * ph.sin(), ct);
                let rad = if ct > 0.0 {
                    sky_radiance(h, d, sun, ms, amb)
                } else {
                    let e_sky = 0.5 * (avg_or(amb) * std::f32::consts::PI);
                    ground_albedo / std::f32::consts::PI * (sun_col * sun.z.max(0.0) + e_sky)
                };
                let w = 4.0 * std::f32::consts::PI / (nt * np) as f32;
                let b = sh_basis(d);
                for k in 0..9 {
                    sh[k] += rad * b[k] * w;
                }
                if ct > 0.0 {
                    avg += rad;
                    wsum += 1.0;
                }
            }
        }
        if pass == 0 {
            amb = avg / wsum * 0.6;
        }
    }
    let a = [std::f32::consts::PI, 2.0 * std::f32::consts::PI / 3.0, std::f32::consts::PI / 4.0];
    for (k, c) in sh.iter_mut().enumerate() {
        *c *= a[if k == 0 { 0 } else if k < 4 { 1 } else { 2 }];
    }
    SkyLight { sun_col, sh, amb }
}

pub fn sh_eval(sh: &[Vec3; 9], d: Vec3) -> Vec3 {
    let b = sh_basis(d);
    (0..9).fold(Vec3::ZERO, |a, k| a + sh[k] * b[k]).max(Vec3::ZERO)
}

fn avg_or(amb: Vec3) -> Vec3 {
    if amb == Vec3::ZERO {
        Vec3::splat(0.05)
    } else {
        amb / 0.6
    }
}
