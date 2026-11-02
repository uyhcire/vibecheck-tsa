//! MSL sources for the photoreal renderer.

const PRELUDE: &str = r#"
#include <metal_stdlib>
using namespace metal;
struct FrameU {
    float4x4 viewproj;
    float4x4 inv_viewproj;
    float4x4 prev_viewproj;
    float4 cam;
    float4 sun;
    float4 sun_col;
    float4 screen;
    float4 params;
    float4 amb;
    float4 sh[9];
    float4x4 shadow[4];
    float4 splits;
    float4 shadow_texel;
    float4 prop;
    float4 flags;
    float4 fog;
    float4 fog2;
    float4 land_pos;
    float4 land_dir;
    float4 nav[3];
    float4 post0;
    float4 post1;
    float4 post2;
    float4 post3;
    float4 post4;
    float4 post5;
    float4x4 viewproj_nj;
    float4 prev_model[4];
    float4 post6;
};
float3 srgb_to_lin(float3 c) { return select(pow((c + 0.055) / 1.055, 2.4), c / 12.92, c <= 0.04045); }
float3 lin_to_srgb(float3 c) { return select(1.055 * pow(c, 1.0 / 2.4) - 0.055, c * 12.92, c <= 0.0031308); }
float3 aces(float3 x) { return clamp((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14), 0.0, 1.0); }
struct FsIn { float2 pos [[attribute(0)]]; };

constant float RG = 6360e3;
constant float RT = 6460e3;
constant float3 BR = float3(5.802e-6, 13.558e-6, 33.1e-6);
constant float BM_S = 3.996e-6;
constant float BM_E = 4.40e-6;
constant float3 BO = float3(0.650e-6, 1.881e-6, 0.085e-6);
constant float MIE_G = 0.8;
constant float PI = 3.14159265;

float3 extinction(float h, float ms) {
    float o = max(0.0, 1.0 - abs(h - 25000.0) / 15000.0);
    return BR * exp(-h / 8000.0) + BM_E * ms * exp(-h / 1200.0) + BO * o;
}
float ray_top(float h, float mu) { float r = RG + h; return -r * mu + sqrt(max(r * r * (mu * mu - 1.0) + RT * RT, 0.0)); }
bool hits_ground(float h, float mu) { float r = RG + h; return mu < 0.0 && r * r * (mu * mu - 1.0) + RG * RG >= 0.0; }
float3 transmittance(float h, float mu, float ms) {
    if (hits_ground(h, mu)) return float3(0.0);
    float r = RG + h; float L = ray_top(h, mu); float dt = L / 12.0; float3 od = 0.0;
    for (int i = 0; i < 12; i++) {
        float t = (float(i) + 0.5) * dt;
        float hh = sqrt(r * r + t * t + 2.0 * r * mu * t) - RG;
        od += extinction(hh, ms) * dt;
    }
    return exp(-od);
}
float phase_r(float nu) { return 3.0 / (16.0 * PI) * (1.0 + nu * nu); }
float phase_m(float nu) {
    float g = MIE_G; float k = 3.0 / (8.0 * PI) * (1.0 - g * g) / (2.0 + g * g);
    return k * (1.0 + nu * nu) / pow(1.0 + g * g - 2.0 * g * nu, 1.5);
}
float3 sky_march(float h, float3 dir, float3 sun, float ms, float3 amb) {
    float r = RG + h; float mu = dir.z;
    float t_end = hits_ground(h, mu) ? (-r * mu - sqrt(r * r * (mu * mu - 1.0) + RG * RG)) : ray_top(h, mu);
    float nu = dot(dir, sun); float pr = phase_r(nu); float pm = phase_m(nu);
    const int N = 32;
    float dt = t_end / float(N);
    float3 tr = 1.0; float3 L = 0.0;
    for (int i = 0; i < N; i++) {
        float t = (float(i) + 0.5) * dt;
        float3 p = float3(0.0, 0.0, r) + dir * t;
        float lp = length(p); float hh = lp - RG; float3 up = p / lp;
        float3 sr = BR * exp(-hh / 8000.0); float sm = BM_S * ms * exp(-hh / 1200.0);
        float3 ext = extinction(hh, ms);
        float3 tsun = transmittance(hh, dot(up, sun), ms);
        float3 S = (sr * pr + sm * pm) * tsun + (sr + sm) * amb;
        float3 st = exp(-ext * dt);
        L += tr * (S - S * st) / ext;
        tr *= st;
    }
    return L;
}
float2 sky_uv(float3 dir, float3 sun) {
    float2 sh = length(sun.xy) > 1e-4 ? normalize(sun.xy) : float2(1.0, 0.0);
    float2 dh = length(dir.xy) > 1e-5 ? normalize(dir.xy) : sh;
    float az = acos(clamp(dot(dh, sh), -1.0, 1.0));
    float l = asin(clamp(dir.z, -1.0, 1.0));
    float v = 0.5 + 0.5 * sign(l) * sqrt(abs(l) / (0.5 * PI));
    return float2(az / PI, 1.0 - v);
}
float3 sky_dir(float2 uv, float3 sun) {
    float az = uv.x * PI; float v = 1.0 - uv.y;
    float l = (v < 0.5 ? -1.0 : 1.0) * pow(abs(2.0 * v - 1.0), 2.0) * 0.5 * PI;
    float2 sh = length(sun.xy) > 1e-4 ? normalize(sun.xy) : float2(1.0, 0.0);
    float2 pp = float2(-sh.y, sh.x);
    float2 hd = cos(az) * sh + sin(az) * pp;
    return float3(cos(l) * hd, sin(l));
}
float3 sh_irradiance(constant FrameU& U, float3 d) {
    float3 e = U.sh[0].rgb * 0.282095
        + U.sh[1].rgb * 0.488603 * d.y + U.sh[2].rgb * 0.488603 * d.z + U.sh[3].rgb * 0.488603 * d.x
        + U.sh[4].rgb * 1.092548 * d.x * d.y + U.sh[5].rgb * 1.092548 * d.y * d.z
        + U.sh[6].rgb * 0.315392 * (3.0 * d.z * d.z - 1.0) + U.sh[7].rgb * 1.092548 * d.x * d.z
        + U.sh[8].rgb * 0.546274 * (d.x * d.x - d.y * d.y);
    return max(e, 0.0);
}
float3 aerial(constant FrameU& U, float3 col, float3 p, thread float3& tr_out) {
    float3 d = p - U.cam.xyz; float L = length(d); float3 dir = d / max(L, 1e-3);
    float ms = U.params.x;
    float nu = dot(dir, U.sun.xyz); float pr = phase_r(nu); float pm = phase_m(nu);
    const int N = 6;
    float dt = L / float(N);
    float3 tr = 1.0; float3 Li = 0.0;
    for (int i = 0; i < N; i++) {
        float h = max(U.cam.z + dir.z * (float(i) + 0.5) * dt, 0.0);
        float3 sr = BR * exp(-h / 8000.0); float sm = BM_S * ms * exp(-h / 1200.0);
        float3 ext = extinction(h, ms);
        float3 S = (sr * pr + sm * pm) * U.sun_col.rgb + (sr + sm) * U.amb.rgb;
        float3 st = exp(-ext * dt);
        Li += tr * (S - S * st) / ext;
        tr *= st;
    }
    tr_out = tr;
    return col * tr + Li;
}
float3 aerial(constant FrameU& U, float3 col, float3 p) { float3 t; return aerial(U, col, p, t); }
struct MOut {
    float4 c [[color(0)]]; float4 a [[color(1)]]; float4 s [[color(2)]]; float4 e [[color(3)]];
    float4 al [[color(4)]]; float4 nr [[color(5)]]; float4 mv [[color(6)]];
};
struct Terms { float3 amb; float3 sun; float3 env; float w; float rough; float3 alb; float metal; float3 n; };
Terms terms0() { Terms t; t.amb = 0.0; t.sun = 0.0; t.env = 0.0; t.w = 0.0; t.rough = 1.0; t.alb = 0.0; t.metal = 0.0; t.n = float3(0.0, 0.0, 1.0); return t; }
bool rt_mode(constant FrameU& U) { return U.post5.y > 0.5; }
float2 motion(constant FrameU& U, float3 p, float3 pprev) {
    float4 pc = U.prev_viewproj * float4(pprev, 1.0); float4 cc = U.viewproj_nj * float4(p, 1.0);
    return (pc.xy / pc.w - cc.xy / cc.w) * float2(0.5, -0.5);
}
MOut mrt2(constant FrameU& U, float3 col, Terms t, float3 p, float3 pprev) {
    float3 tr; MOut o;
    o.c = float4(aerial(U, col, p, tr), 1.0);
    o.a = float4(t.amb * tr, 1.0);
    o.s = float4(t.sun * tr, t.w);
    o.e = float4(t.env * tr, t.rough);
    o.al = float4(t.alb, t.metal);
    o.nr = float4(t.n, 1.0);
    o.mv = float4(motion(U, p, pprev), 0.0, 1.0);
    return o;
}
MOut mrt(constant FrameU& U, float3 col, Terms t, float3 p) { return mrt2(U, col, t, p, p); }
MOut flat_out(float4 c, float mask) {
    MOut o; o.c = c; o.a = float4(0.0, 0.0, 0.0, mask); o.s = 0.0; o.e = float4(0.0, 0.0, 0.0, 1.0); o.al = 0.0; o.nr = float4(0.0, 0.0, 1.0, 0.0); o.mv = 0.0; return o;
}
float3 sky_sample(texture2d<float> lut, sampler s, float3 dir, float3 sun) {
    return lut.sample(s, sky_uv(dir, sun)).rgb;
}
float fresnel(float f0, float c) { return f0 + (1.0 - f0) * pow(1.0 - saturate(c), 5.0); }
struct FsOut { float4 p [[position]]; float2 ndc; };
"#;

const PBR: &str = r#"
constexpr sampler rep_s(address::repeat, filter::linear, mip_filter::linear, max_anisotropy(8));
constexpr sampler clamp_s(address::clamp_to_edge, filter::linear, mip_filter::linear, max_anisotropy(8));
constexpr sampler lut_s(address::clamp_to_edge, filter::linear);

float hash12(float2 p) { float3 p3 = fract(float3(p.xyx) * 0.1031); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.x + p3.y) * p3.z); }
float vnoise(float2 p) {
    float2 i = floor(p); float2 f = fract(p); float2 u = f * f * (3.0 - 2.0 * f);
    return mix(mix(hash12(i), hash12(i + float2(1, 0)), u.x), mix(hash12(i + float2(0, 1)), hash12(i + float2(1, 1)), u.x), u.y);
}
float hash13(float3 p) { p = fract(p * 0.1031); p += dot(p, p.zyx + 31.32); return fract((p.x + p.y) * p.z); }
float vnoise3(float3 p) {
    float3 i = floor(p); float3 f = fract(p); float3 u = f * f * (3.0 - 2.0 * f);
    float a = mix(mix(hash13(i), hash13(i + float3(1, 0, 0)), u.x), mix(hash13(i + float3(0, 1, 0)), hash13(i + float3(1, 1, 0)), u.x), u.y);
    float b = mix(mix(hash13(i + float3(0, 0, 1)), hash13(i + float3(1, 0, 1)), u.x), mix(hash13(i + float3(0, 1, 1)), hash13(i + float3(1, 1, 1)), u.x), u.y);
    return mix(a, b, u.z);
}
float cloud_cov(constant FrameU& U, float2 xy) {
    float2 w = xy + float2(U.cam.w * 8.0, U.cam.w * 3.0);
    return vnoise(w / 2600.0) * 0.55 + vnoise(w / 1100.0 + 7.0) * 0.3 + vnoise(w / 430.0 + 3.0) * 0.15;
}
float cloud_base(constant FrameU& U, float2 xy) {
    float cov = U.fog2.y;
    return saturate((cloud_cov(U, xy) - (1.0 - cov)) / max(cov, 0.05) * 2.2);
}
float cloud_density(constant FrameU& U, float3 p, bool detail) {
    float h = (p.z - U.fog2.z) / (U.fog2.w - U.fog2.z);
    if (h <= 0.0 || h >= 1.0) return 0.0;
    float base = cloud_base(U, p.xy);
    float d = base * smoothstep(0.0, 0.12, h) * smoothstep(1.0, 0.3 + 0.45 * base, h);
    if (d <= 0.0) return 0.0;
    if (detail) {
        float e = vnoise3(p / 230.0 + float3(0.0, 0.0, U.cam.w * 0.01)) * 0.62 + vnoise3(p / 85.0) * 0.38;
        d = saturate(d - e * 0.5 * (1.15 - d));
    }
    return d * 0.03;
}
float cloud_shadow(constant FrameU& U, float3 p) {
    if (U.fog2.y <= 0.0 || U.sun.z <= 0.03) return 1.0;
    float zm = 0.5 * (U.fog2.z + U.fog2.w);
    float3 q = p + U.sun.xyz * ((zm - p.z) / U.sun.z);
    float od = cloud_base(U, q.xy) * 0.03 * (U.fog2.w - U.fog2.z) * 0.35;
    return exp(-od) * 0.88 + 0.12;
}
float spot(constant FrameU& U, float3 p, thread float3& l, thread float& dist) {
    float3 dv = p - U.land_pos.xyz; dist = length(dv); l = dv / max(dist, 1e-3);
    return smoothstep(U.land_dir.w, mix(U.land_dir.w, 1.0, 0.5), dot(l, U.land_dir.xyz));
}
float D_GGX(float nh, float a) { float a2 = a * a; float d = nh * nh * (a2 - 1.0) + 1.0; return a2 / (PI * d * d + 1e-7); }
float V_SJ(float nv, float nl, float a) { float k = a * 0.5; return 0.25 / ((nv * (1.0 - k) + k) * (nl * (1.0 - k) + k)); }
float2 env_brdf(float r, float nv) {
    float4 c0 = float4(-1.0, -0.0275, -0.572, 0.022); float4 c1 = float4(1.0, 0.0425, 1.04, -0.04);
    float4 q = r * c0 + c1; float a004 = min(q.x * q.x, exp2(-9.28 * nv)) * q.x + q.y;
    return float2(-1.04, 1.04) * a004 + q.zw;
}
float3 env_radiance(constant FrameU& U, texture2d<float> lut, float3 r, float rough, float height) {
    float3 up_irr = sh_irradiance(U, float3(0.0, 0.0, 1.0));
    float3 sky = lut.sample(lut_s, sky_uv(r, U.sun.xyz)).rgb;
    float3 env = mix(sky, sh_irradiance(U, r) / PI, smoothstep(0.15, 0.9, rough));
    float3 ground = 0.14 / PI * (U.sun_col.rgb * max(U.sun.z, 0.0) * 0.6 + up_irr);
    env = mix(env, ground, smoothstep(0.02, -0.1, r.z));
    float city = smoothstep(0.25, -0.02, r.z) * (1.0 - smoothstep(30.0, 280.0, height));
    float3 cityc = 0.16 / PI * (up_irr * 0.9 + U.sun_col.rgb * 0.3);
    return mix(env, cityc, city * 0.85);
}
struct Surf { float3 alb; float3 n; float rough; float metal; float ao; };
float3 shade(constant FrameU& U, texture2d<float> lut, Surf s, float3 p, float3 v, float shadow, thread Terms& t) {
    float3 sun = U.sun.xyz;
    if (rt_mode(U)) shadow = 1.0;
    shadow *= cloud_shadow(U, p);
    float3 h = normalize(sun + v);
    float nl = saturate(dot(s.n, sun)); float nv = max(dot(s.n, v), 1e-3);
    float nh = saturate(dot(s.n, h)); float vh = saturate(dot(v, h));
    float a = max(s.rough * s.rough, 0.002);
    float3 f0 = mix(float3(0.04), s.alb, s.metal);
    float3 F = f0 + (1.0 - f0) * pow(1.0 - vh, 5.0);
    float3 spec = D_GGX(nh, a) * V_SJ(nv, nl, a) * F * nl * U.sun_col.rgb * shadow;
    float3 irr = sh_irradiance(U, s.n) + U.sun_col.rgb * max(U.sun.z, 0.0) * (0.10 + 0.08 * saturate(-s.n.z + 0.5));
    float3 diff = s.alb * (1.0 - s.metal) / PI * (nl * U.sun_col.rgb * shadow + irr * s.ao);
    float2 ab = env_brdf(s.rough, nv);
    float spec_occ = saturate(pow(nv + s.ao, exp2(-16.0 * a - 1.0)) - 1.0 + s.ao);
    float3 envs = env_radiance(U, lut, reflect(-v, s.n), s.rough, p.z) * (f0 * ab.x + ab.y) * spec_occ;
    float3 dsun = s.alb * (1.0 - s.metal) / PI * nl * U.sun_col.rgb * shadow;
    t.amb = rt_mode(U) ? s.alb * (1.0 - s.metal) / PI * irr : s.alb * (1.0 - s.metal) / PI * irr * s.ao + 0.5 * envs;
    t.sun = dsun + spec;
    t.env = envs;
    float3 sw = (f0 * ab.x + ab.y) * spec_occ;
    t.w = dot(sw, float3(0.2126, 0.7152, 0.0722));
    t.rough = s.rough; t.alb = s.alb * (1.0 - s.metal); t.metal = s.metal; t.n = s.n;
    float3 col = diff + spec + envs;
    if (U.land_pos.w > 0.0) {
        float3 ll; float ld;
        float sp = spot(U, p, ll, ld);
        if (sp > 0.0) {
            float3 Ld = -ll;
            float nl2 = saturate(dot(s.n, Ld));
            float3 E = float3(1.0, 0.95, 0.85) * U.land_pos.w * sp / max(ld * ld, 1.0) * nl2;
            float3 h2 = normalize(Ld + v);
            float3 F2 = f0 + (1.0 - f0) * pow(1.0 - saturate(dot(v, h2)), 5.0);
            col += E * (s.alb * (1.0 - s.metal) / PI + D_GGX(saturate(dot(s.n, h2)), a) * V_SJ(nv, nl2, a) * F2);
        }
    }
    return col;
}
constexpr sampler shadow_s(coord::normalized, filter::linear, address::clamp_to_edge, compare_func::less_equal);
float shadow_factor(constant FrameU& U, array<depth2d<float>, 4> sm, float3 p, float3 n) {
    float d = length(p - U.cam.xyz);
    if (d > U.splits.w || U.sun.z < 0.0) return U.sun.z < 0.0 ? 0.0 : 1.0;
    int c = d < U.splits.x ? 0 : (d < U.splits.y ? 1 : (d < U.splits.z ? 2 : 3));
    float tx = U.shadow_texel[c];
    float ndl = dot(n, U.sun.xyz);
    float3 pp = p + n * tx * (1.0 + 1.5 * (1.0 - abs(ndl))) + U.sun.xyz * tx * 0.8;
    float4 q = U.shadow[c] * float4(pp, 1.0);
    float2 uv = float2(q.x * 0.5 + 0.5, 0.5 - q.y * 0.5);
    float ts = 1.0 / 2048.0;
    float s = 0.0;
    for (int j = -1; j <= 1; j++)
        for (int k = -1; k <= 1; k++)
            s += sm[c].sample_compare(shadow_s, uv + float2(j, k) * ts * 1.25, q.z);
    s /= 9.0;
    float fade = smoothstep(0.85, 1.0, d / U.splits.w);
    return mix(s, 1.0, fade);
}
float surf_shadow(constant FrameU& U, array<depth2d<float>, 4> sm, float3 p, float3 n) {
    return rt_mode(U) ? 1.0 : shadow_factor(U, sm, p, n);
}
float3 tnormal(texture2d<float> t, float2 uv, float3 T, float3 B, float3 N, float k) {
    float3 m = t.sample(rep_s, uv).xyz * 2.0 - 1.0;
    m.xy *= k;
    return normalize(T * m.x + B * m.y + N * m.z);
}
"#;

const TERRAIN: &str = r#"
struct VIn {
    float3 pos [[attribute(0)]]; float3 nrm [[attribute(1)]]; float3 col [[attribute(2)]];
    float2 uv [[attribute(3)]]; float4 mat [[attribute(4)]]; float4 fac [[attribute(5)]];
};
struct VOut { float4 p [[position]]; float3 pos; float3 nrm; float2 uv; };
vertex VOut vertexShader(VIn v [[stage_in]], constant FrameU& U [[buffer(0)]]) {
    VOut o; o.p = U.viewproj * float4(v.pos, 1.0); o.pos = v.pos; o.nrm = v.nrm; o.uv = v.uv; return o;
}
struct Det { float3 ratio; float3 nts; float3 orm; };
Det detail(texture2d<float> a, texture2d<float> n, texture2d<float> o, float2 uv, float w) {
    Det d;
    float2 uv2 = float2(uv.x * 0.8 - uv.y * 0.6, uv.x * 0.6 + uv.y * 0.8) * 0.37 + 0.31;
    float m = smoothstep(0.3, 0.7, vnoise(uv * 0.45));
    float3 avg = srgb_to_lin(a.sample(rep_s, uv, level(12)).rgb) + 1e-3;
    float3 c = mix(srgb_to_lin(a.sample(rep_s, uv).rgb), srgb_to_lin(a.sample(rep_s, uv2).rgb), m);
    d.ratio = c / avg * w;
    d.nts = mix(n.sample(rep_s, uv).xyz, n.sample(rep_s, uv2).xyz, m) * 2.0 - 1.0;
    d.nts *= w;
    d.orm = mix(o.sample(rep_s, uv).xyz, o.sample(rep_s, uv2).xyz, m) * w;
    return d;
}
fragment MOut fragmentShader(VOut i [[stage_in]], constant FrameU& U [[buffer(0)]],
                               texture2d<float> sky_lut [[texture(0)]],
                               texture2d<float> galb [[texture(1)]], texture2d<float> gmask [[texture(2)]],
                               array<texture2d<float>, 12> det [[texture(3)]],
                               array<depth2d<float>, 4> sm [[texture(15)]]) {
    float3 N = normalize(i.nrm);
    float3 v = normalize(U.cam.xyz - i.pos);
    float4 A = galb.sample(clamp_s, i.uv);
    float4 M = gmask.sample(clamp_s, i.uv);
    float3 macro = srgb_to_lin(A.rgb);
    float big = vnoise(i.pos.xy / 260.0) * 0.6 + vnoise(i.pos.xy / 47.0) * 0.4;
    macro *= mix(0.86, 1.12, big);
    float4 w = float4(M.r, M.g, M.b, 0.0);
    w.w = saturate(1.0 - w.x - w.y - w.z);
    float3 ratio = 0.0; float3 nts = 0.0; float3 orm = 0.0;
    float2 xy = i.pos.xy;
    float scales[4] = { 1.0 / 5.0, 1.0 / 3.0, 1.0 / 9.0, 1.0 / 4.0 };
    for (int k = 0; k < 4; k++) {
        if (w[k] < 0.01) continue;
        float2 uv = xy * scales[k];
        if (k == 2) {
            float3 an = abs(N);
            uv = an.x > an.y ? i.pos.yz * scales[k] : i.pos.xz * scales[k];
            uv = mix(uv, xy * scales[k], smoothstep(0.55, 0.8, an.z));
        }
        Det d = detail(det[3 * k], det[3 * k + 1], det[3 * k + 2], uv, w[k]);
        ratio += d.ratio; nts += d.nts; orm += d.orm;
    }
    float3 alb = saturate(macro * mix(float3(1.0), ratio, 0.85));
    float3 T = normalize(cross(float3(0.0, 1.0, 0.0), N));
    float3 B = cross(N, T);
    nts.xy *= 0.8;
    Surf s;
    s.alb = alb;
    s.n = normalize(T * nts.x + B * nts.y + N * max(nts.z, 0.2));
    s.rough = clamp(orm.g, 0.3, 1.0);
    s.metal = 0.0;
    s.ao = A.a * mix(1.0, orm.r, 0.7);
    if (rt_mode(U)) {
        float wet = smoothstep(0.52, 0.7, vnoise(xy / 6.0) * 0.7 + vnoise(xy / 1.7) * 0.3) * (w.x + w.w * 0.6);
        s.rough = mix(s.rough, 0.04, wet);
        s.alb *= mix(1.0, 0.55, wet);
        s.n = normalize(mix(s.n, N, wet));
    }
    Terms tm = terms0();
    float3 col = shade(U, sky_lut, s, i.pos, v, surf_shadow(U, sm, i.pos, N), tm);
    // Light pools under the grid city's street lamps (flags.w: a map without them).
    if (U.flags.z > 0.0 && U.flags.w < 0.5 && abs(i.pos.x) < 1222.0 && abs(i.pos.y) < 1222.0) {
        float E = 0.0;
        for (int ax = 0; ax < 2; ax++) {
            float2 q = ax == 0 ? i.pos.xy : i.pos.yx;
            float k = round((q.x + 1200.0) / 120.0);
            float sx = -1200.0 + 120.0 * k;
            float off = (fmod(k, 5.0) == 0.0 ? 20.0 : 14.0) - 2.5;
            float lx = sx + (q.x > sx ? off : -off);
            float ly = (floor(q.y / 30.0) + 0.5) * 30.0;
            float d2 = (q.x - lx) * (q.x - lx) + (q.y - ly) * (q.y - ly) + 64.0;
            E += 12.0 * 8.0 / (d2 * sqrt(d2));
        }
        float3 Ec = float3(1.0, 0.72, 0.42) * E * U.flags.z;
        col += s.alb / PI * Ec;
    }
    return mrt(U, col, tm, i.pos);
}
"#;

const BUILDING: &str = r#"
struct VIn {
    float3 pos [[attribute(0)]]; float3 nrm [[attribute(1)]]; float3 col [[attribute(2)]];
    float2 uv [[attribute(3)]]; float4 mat [[attribute(4)]]; float4 fac [[attribute(5)]];
};
struct VOut { float4 p [[position]]; float3 pos; float3 nrm; float3 col; float2 uv; float4 mat; float4 fac; };
vertex VOut vertexShader(VIn v [[stage_in]], constant FrameU& U [[buffer(0)]]) {
    VOut o; o.p = U.viewproj * float4(v.pos, 1.0);
    o.pos = v.pos; o.nrm = v.nrm; o.col = v.col; o.uv = v.uv; o.mat = v.mat; o.fac = v.fac; return o;
}
constant float4 META[6] = { FACADE_META };

float3 interior(constant FrameU& U, float3 rd, float3 right, float3 n, float2 inc, float colw, float fh, float2 cell, float bseed, bool shop) {
    float3 d = float3(dot(rd, right), rd.z, max(dot(rd, -n), 1e-3));
    float lamp = mix(0.03, 0.10, U.flags.z);
    float D = max(colw * 1.7, 5.0);
    float3 o = float3(inc.x, inc.y, 0.0);
    float tx = d.x > 0.0 ? (colw - o.x) / d.x : -o.x / min(d.x, -1e-4);
    float ty = d.y > 0.0 ? (fh - o.y) / d.y : -o.y / min(d.y, -1e-4);
    float tz = D / d.z;
    float t = min(min(tx, ty), tz);
    float3 h = o + d * t;
    float rs = hash12(cell + bseed * 97.0);
    float rs2 = hash12(cell.yx * 1.7 + bseed * 13.0);
    float3 wall = mix(float3(0.55, 0.52, 0.47), float3(0.75, 0.73, 0.68), rs);
    if (rs2 > 0.8) wall = float3(0.45, 0.50, 0.55);
    float3 flo = rs > 0.5 ? float3(0.22, 0.14, 0.08) : float3(0.25, 0.25, 0.26);
    float3 alb;
    float3 emit = 0.0;
    bool lights = hash12(cell * 3.1 + bseed) > (shop ? 0.1 : mix(0.55, 0.25, U.flags.z));
    if (t == tz) {
        alb = wall;
        float desk = step(h.y, 0.8) * step(0.25 * colw, h.x) * step(h.x, 0.8 * colw);
        alb = mix(alb, float3(0.12, 0.10, 0.09), desk);
        if (shop) alb = mix(alb, float3(0.6, 0.3, 0.2) * (0.5 + rs), step(0.4, fract(h.x * 1.3)) * step(h.y, 2.2));
    } else if (t == ty) {
        if (d.y < 0.0) alb = flo;
        else {
            alb = float3(0.8);
            float2 q = abs(float2(h.x - 0.5 * colw, h.z - 0.5 * D));
            if (lights && q.x < 0.3 * colw && q.y < 0.25 * D) emit = float3(1.0, 0.92, 0.8) * lamp * 3.0;
        }
    } else {
        alb = wall * 0.9;
    }
    float3 irr = sh_irradiance(U, n) + U.sun_col.rgb * max(dot(n, U.sun.xyz), 0.0) * 0.5;
    float fall = 1.0 - 0.6 * saturate(h.z / D);
    float3 E = irr * 0.3 * fall + (lights ? float3(1.0, 0.9, 0.75) * lamp : float3(0.0));
    float3 c = alb / PI * E + emit;
    float blind = hash12(cell.yx + bseed * 5.0);
    if (!shop && blind > 0.55) {
        float bl = fh * (1.0 - (blind - 0.55) * 1.6);
        if (inc.y > bl) c = float3(0.7, 0.68, 0.64) / PI * irr * 0.45 * (0.85 + 0.15 * step(0.5, fract(inc.y * 12.0)));
    }
    return c;
}

fragment MOut fragmentShader(VOut i [[stage_in]], constant FrameU& U [[buffer(0)]],
                               texture2d<float> sky_lut [[texture(0)]],
                               array<texture2d<float>, 18> fac [[texture(1)]],
                               array<texture2d<float>, 6> roof [[texture(19)]],
                               array<depth2d<float>, 4> sm [[texture(25)]]) {
    float shf = surf_shadow(U, sm, i.pos, normalize(i.nrm));
    float3 N = normalize(i.nrm);
    float3 v = normalize(U.cam.xyz - i.pos);
    float kind = i.mat.x;
    float seed = i.mat.y;
    float3 tint = i.col;
    Surf s;
    s.metal = 0.0;
    float3 col;
    Terms tm = terms0();
    if (kind < 1.5) {
        int ft = int(i.uv.x + 0.5);
        bool ground = i.uv.y > 0.5;
        float3 right = float3(-N.y, N.x, 0.0);
        float sw = dot(i.pos.xy, right.xy) - i.fac.x;
        float colw = i.fac.y; float fh = i.fac.z;
        float zl = i.pos.z - i.mat.z;
        float cu = sw / colw; float fv = zl / fh;
        float4 meta = META[ft];
        float2 off = floor(float2(seed * 7.0, seed * 13.0)) / meta.xy;
        float2 tuv = float2(cu / meta.x, -fv / meta.y) + off;
        float4 a = fac[3 * ft].sample(rep_s, tuv);
        float3 o = fac[3 * ft + 2].sample(rep_s, tuv).rgb;
        float glass = meta.z > 0.5 ? smoothstep(0.35, 0.65, o.b) : smoothstep(0.32, 0.18, o.g);
        float3 alb = srgb_to_lin(a.rgb);
        bool shop = ground && fv < 1.0 && fv >= 0.0;
        if (shop) {
            float x = fract(cu);
            float g = step(0.05, x) * step(x, 0.95) * step(0.06, fv) * step(fv, 0.78);
            glass = g;
            float band = step(0.82, fv) * step(fv, 0.97);
            float3 signc = mix(float3(0.5, 0.08, 0.06), float3(0.08, 0.2, 0.45), hash12(float2(floor(cu * 0.34), seed)));
            alb = mix(float3(0.06), signc, band);
            o = float3(1.0, 0.4, band > 0.5 ? 0.0 : 0.8);
        }
        float streak = vnoise(float2(sw * 1.3, zl * 0.06 + seed * 50.0));
        float grime = mix(0.78, 1.0, smoothstep(0.25, 0.75, streak)) * mix(0.75, 1.0, smoothstep(0.0, 8.0, zl));
        float3 nm = fac[3 * ft + 1].sample(rep_s, tuv).xyz * 2.0 - 1.0;
        s.n = normalize(right * nm.x + float3(0.0, 0.0, 1.0) * nm.y + N * max(nm.z, 0.3));
        s.alb = saturate(alb * tint * grime);
        s.rough = clamp(o.g, 0.2, 1.0);
        s.metal = shop ? o.b : (meta.z > 0.5 ? 0.0 : o.b * 0.5);
        s.ao = o.r * mix(0.55, 1.0, smoothstep(0.0, 5.0, zl));
        col = shade(U, sky_lut, s, i.pos, v, shf, tm);
        if (glass > 0.01) {
            float2 cell = float2(floor(cu), floor(fv));
            float2 inc = float2(fract(cu) * colw, fract(fv) * fh);
            float3 rd = -v;
            float3 room = interior(U, rd, right, N, inc, colw, fh, cell, seed, shop);
            float3 gn = normalize(N + (s.n - N) * 0.15);
            float nv = max(dot(gn, v), 1e-3);
            float F = fresnel(0.06, nv);
            float3 refl = env_radiance(U, sky_lut, reflect(-v, gn), 0.04, i.pos.z);
            float3 hv = normalize(U.sun.xyz + v);
            float ga = 0.03 * 0.03;
            float glint = D_GGX(saturate(dot(gn, hv)), ga) * V_SJ(nv, saturate(dot(gn, U.sun.xyz)), ga) * F * saturate(dot(gn, U.sun.xyz));
            float3 tintg = meta.z > 0.5 ? srgb_to_lin(a.rgb) * 1.6 + 0.2 : float3(0.85, 0.9, 0.9);
            float3 g = room * (1.0 - F) * tintg + refl * F + glint * U.sun_col.rgb * shf;
            col = mix(col, g, glass);
            tm.amb *= 1.0 - glass;
            tm.sun = mix(tm.sun, glint * U.sun_col.rgb * shf, glass);
            tm.env = mix(tm.env, refl * F, glass);
            tm.w = mix(tm.w, F, glass);
            tm.rough = mix(tm.rough, 0.04, glass);
            tm.alb *= 1.0 - glass;
        }
    } else if (kind < 2.5) {
        int rt = int(i.mat.z + 0.5);
        float2 uv = i.pos.xy / (rt == 0 ? 3.0 : 4.5);
        float3 a = srgb_to_lin(roof[3 * rt].sample(rep_s, uv).rgb);
        float3 o = roof[3 * rt + 2].sample(rep_s, uv).rgb;
        float3 nm = roof[3 * rt + 1].sample(rep_s, uv).xyz * 2.0 - 1.0;
        float2 e = min(i.pos.xy - i.fac.xy, i.fac.zw - i.pos.xy);
        float edge = 1.0 - step(0.7, min(e.x, e.y));
        float stain = vnoise(i.pos.xy / 6.0 + seed * 31.0);
        s.alb = saturate(mix(a * tint * mix(0.45, 0.7, stain), float3(0.3, 0.29, 0.28), edge));
        s.n = normalize(float3(nm.xy * 0.8, max(nm.z, 0.3)));
        s.rough = clamp(o.g, 0.4, 1.0);
        s.ao = o.r;
        col = shade(U, sky_lut, s, i.pos, v, shf, tm);
    } else {
        float3 an = abs(N);
        float2 uv = (an.x > 0.5 ? i.pos.yz : (an.y > 0.5 ? i.pos.xz : i.pos.xy)) / 2.0;
        float3 a = srgb_to_lin(roof[3].sample(rep_s, uv).rgb);
        s.alb = saturate(a * tint);
        s.n = N;
        s.rough = 0.45;
        s.metal = i.mat.z;
        s.ao = 0.8;
        col = shade(U, sky_lut, s, i.pos, v, shf, tm);
    }
    return mrt(U, col, tm, i.pos);
}
"#;

const DYNAMIC: &str = r#"
struct VIn { float3 pos [[attribute(0)]]; float3 nrm [[attribute(1)]]; float4 col [[attribute(2)]]; float4 mat [[attribute(3)]]; float4 loc [[attribute(4)]]; };
struct VOut { float4 p [[position]]; float3 pos; float3 nrm; float4 col; float4 mat; float4 loc; };
vertex VOut vertexShader(VIn v [[stage_in]], constant FrameU& U [[buffer(0)]]) {
    VOut o; o.p = U.viewproj * float4(v.pos, 1.0);
    o.pos = v.pos; o.nrm = v.nrm; o.col = v.col; o.mat = v.mat; o.loc = v.loc; return o;
}
constant uchar GLYPHS[6][7] = {
    {17, 17, 25, 21, 19, 17, 17},
    {14, 17, 19, 21, 25, 17, 14},
    {31, 1, 2, 4, 8, 8, 8},
    {14, 17, 1, 2, 4, 8, 31},
    {2, 6, 10, 18, 31, 2, 2},
    {14, 17, 16, 16, 16, 17, 14},
};
float registration(float2 q) {
    if (any(q < 0.0) || q.x >= 6.0 || q.y >= 1.0) return 0.0;
    int ch = int(q.x);
    float2 g = float2(fract(q.x) * 6.0, q.y * 7.0);
    if (g.x >= 5.0) return 0.0;
    uchar row = GLYPHS[ch][min(int(g.y), 6)];
    return float((row >> (4 - int(g.x))) & 1);
}
float arc_overlap(float a, float L, float w) {
    float o = 0.0;
    for (int k = 0; k < 3; k++) {
        float s0 = float(k) * PI; float s1 = s0 + 2.0 * w;
        o += max(0.0, min(a + L, s1) - max(a, s0));
    }
    return o;
}
float blade_cover(float phi, float w, float th0, float sweep) {
    float a = fmod(fmod(th0 - (phi - w), PI) + PI, PI);
    if (sweep < 1e-4) return (a < 2.0 * w || a > PI - 1e-4) ? 1.0 : 0.0;
    float nfull = floor(sweep / PI);
    float rem = sweep - nfull * PI;
    return (nfull * 2.0 * w + arc_overlap(a, rem, w)) / sweep;
}
fragment MOut fragmentShader(VOut i [[stage_in]], constant FrameU& U [[buffer(0)]],
                               texture2d<float> sky_lut [[texture(0)]],
                               array<depth2d<float>, 4> sm [[texture(1)]]) {
    MOut o;
    if (i.mat.x > 8.5) {
        float g = saturate(1.0 - dot(i.loc.xy, i.loc.xy));
        o = flat_out(float4(i.col.rgb / 0.3, 0.3 * g * g * i.col.a), 0.0); o.e = 0.0; return o;
    }
    if (i.mat.x > 7.5) {
        float g = saturate(1.0 - dot(i.loc.xy, i.loc.xy));
        o = flat_out(float4(i.col.rgb / U.sun.w, i.col.a * g * g), 0.0); o.e = 0.0; return o;
    }
    if (i.mat.x > 6.5) {
        // Gaussian, lowered by its value at the quad's edge so it reaches 0 there: no square shows round a big bright glow.
        float g = max(exp(-dot(i.loc.xy, i.loc.xy) * 4.0) - 0.0183, 0.0) / 0.9817;
        float al = 0.3 * g * i.col.a;
        o = flat_out(float4(i.col.rgb / 0.3, al), 0.0); o.e = 0.0; return o;
    }
    if (i.mat.x > 4.5) { o = flat_out(float4(i.col.rgb / U.sun.w, i.col.a), 0.0); o.e = 0.0; return o; }
    float part = i.loc.w;
    float3 lp = i.loc.xyz;
    float3 v = normalize(U.cam.xyz - i.pos);
    // The cockpit view's cutaways apply to the flown aircraft only, not the fly (livery `mat.y` = 1).
    bool cockpit = U.flags.x > 0.5 && i.mat.y < 0.5;
    Surf s;
    s.n = normalize(i.nrm); s.ao = 1.0; s.metal = 0.0; s.rough = 0.3;
    float3 white = float3(0.78, 0.78, 0.76);
    float3 blue = float3(0.015, 0.035, 0.12);
    float3 gold = float3(0.55, 0.32, 0.05);
    s.alb = white;
    float glass = 0.0;
    float alpha = 1.0;
    if (part < 0.5 || (part > 9.5 && cockpit)) {
        float zc = -0.02 + max(0.0, -1.3 - lp.x) * 0.075;
        if (lp.x < 2.0) {
            if (lp.z > zc && lp.z < zc + 0.11) s.alb = blue;
            else if (lp.z >= zc + 0.11 && lp.z < zc + 0.15) s.alb = gold;
        }
        float2 rq = float2(lp.y > 0.0 ? (-2.75 - lp.x) : (lp.x + 4.15), (0.47 - lp.z)) / float2(0.233, 0.22);
        if (lp.x < -2.6 && lp.x > -4.3 && registration(rq) > 0.5) s.alb = blue;
        bool side_win = lp.z > 0.33 && lp.z < 0.82 && ((lp.x > -0.30 && lp.x < 0.66) || (lp.x > -1.22 && lp.x < -0.40) || (lp.x > -1.95 && lp.x < -1.30 && lp.z > 0.36 + (-1.30 - lp.x) * 0.25));
        bool screen = lp.x > 0.70 && lp.x < 1.10 && lp.z > 0.40 && abs(lp.y) < 0.50;
        if (side_win || screen) glass = 1.0;
        if (cockpit && part > 9.5 && lp.x > 1.0) {
            if (dot(s.n, v) < 0.0) discard_fragment();
        } else if (cockpit) {
            if (glass > 0.5) discard_fragment();
            s.alb = float3(0.05, 0.05, 0.055); s.rough = 0.8;
        }
    } else if (part < 2.5) {
        if (part > 1.5 && abs(lp.y) < 0.05 && lp.z > 0.95 && lp.z < 1.08) s.alb = blue;
        if (part < 1.5 && abs(lp.y) > 5.2) s.alb = blue;
    } else if (part < 3.5) {
        s.alb = white * 0.97;
    } else if (part < 4.5) {
        s.alb = float3(0.6, 0.6, 0.6); s.metal = 0.6; s.rough = 0.4;
    } else if (part < 5.5) {
        s.alb = lp.z < -1.0 ? blue : white;
    } else if (part < 6.5) {
        s.alb = float3(0.025); s.rough = 0.9;
    } else if (part < 7.5) {
        if (cockpit && dot(s.n, v) < 0.0) discard_fragment();
        s.alb = white; s.rough = 0.2;
    } else if (part < 8.5) {
        float2 d = float2(lp.y, lp.z - (-0.05));
        float r = length(d);
        if (r > 0.95) discard_fragment();
        float w = (0.055 + 0.05 * (1.0 - r / 0.95)) / max(r, 0.05);
        float phi = atan2(d.y, d.x);
        float row = i.p.y * U.screen.w;
        float th0 = U.prop.x - U.prop.y * (row * U.prop.z);
        float cover = r < 0.2 ? 1.0 : blade_cover(phi, w, th0, U.prop.y * U.prop.w);
        s.alb = r > 0.82 ? (fract(r * 18.0) > 0.5 ? float3(0.6, 0.05, 0.03) : white) : float3(0.08, 0.08, 0.085);
        s.metal = r > 0.82 ? 0.0 : 0.5; s.rough = 0.45;
        alpha = cover;
        if (alpha < 0.003) discard_fragment();
    } else if (part < 9.5) {
        s.alb = float3(0.04); s.rough = 0.7;
        float2 g = float2(lp.y, lp.z);
        for (int k = 0; k < 6; k++) {
            float2 c = float2(0.38 - float(k % 3) * 0.11, 0.30 - float(k / 3) * 0.11);
            float dd = length(g - c);
            if (dd < 0.045) {
                s.alb = float3(0.01);
                float ang = atan2(g.y - c.y, g.x - c.x);
                if (dd > 0.035 && fract(ang * 12.0 / 6.2831) < 0.15) s.alb = float3(0.8);
                if (dd < 0.03 && abs(dot(normalize(g - c), float2(cos(float(k) + U.cam.w * 0.3), sin(float(k) + U.cam.w * 0.3)))) > 0.995) s.alb = float3(0.9);
            }
        }
    } else {
        s.alb = float3(0.05); s.rough = 0.8;
    }
    if (i.mat.y > 0.5 && part < 7.5 || i.mat.y > 0.5 && part > 9.5) {
        // Fly livery: tan thorax, banded abdomen, red faceted compound eyes over the cabin, smoky veined wings
        // with a thin-film sheen, dark legs (struts).
        float3 tan = float3(0.50, 0.32, 0.12);
        float3 dark = float3(0.06, 0.04, 0.025);
        glass = 0.0; s.metal = 0.0;
        bool wing = (part > 0.5 && part < 1.5) || (part > 2.5 && part < 3.5 && abs(lp.y) > 2.2);
        if (wing) {
            float vein = step(fract(abs(lp.y) * 0.8), 0.03) + step(fract(lp.x * 1.6 + abs(lp.y) * 0.25), 0.04);
            float nv = saturate(dot(s.n, v));
            float3 film = 0.5 + 0.5 * cos(6.2831 * (nv * 1.4 + float3(0.0, 0.33, 0.67)));
            s.alb = mix(float3(0.40, 0.42, 0.45) + 0.2 * film, dark, saturate(vein));
            s.rough = 0.12;
        } else if ((part > 3.5 && part < 4.5) || (part > 5.5 && part < 6.5)) {
            s.alb = dark; s.rough = 0.6;
        } else {
            s.alb = tan; s.rough = 0.45;
            if (lp.x < -0.9 && fract(lp.x * 1.25) < 0.4) s.alb = dark;
            if (lp.z > 0.95 && part < 0.5) s.alb = tan * 0.6;
            float3 eL = (lp - float3(0.95, 0.42, 0.5)) / float3(0.8, 0.3, 0.42);
            float3 eR = (lp - float3(0.95, -0.42, 0.5)) / float3(0.8, 0.3, 0.42);
            if (dot(eL, eL) < 1.0 || dot(eR, eR) < 1.0) {
                float row = floor(lp.z * 11.0);
                float2 f = fract(float2(lp.x * 11.0 + 0.5 * row, lp.z * 11.0)) - 0.5;
                s.alb = float3(0.55, 0.03, 0.02) * (0.55 + 0.45 * smoothstep(0.5, 0.25, max(abs(f.x), abs(f.y))));
                s.rough = 0.12;
            }
        }
    }
    s.alb *= i.col.rgb;
    float shf = surf_shadow(U, sm, i.pos, s.n);
    Terms tm = terms0();
    float3 lit = shade(U, sky_lut, s, i.pos, v, shf, tm);
    if (glass > 0.5) {
        float nv = max(dot(s.n, v), 1e-3);
        float F = fresnel(0.05, nv);
        float3 refl = env_radiance(U, sky_lut, reflect(-v, s.n), 0.03, i.pos.z);
        float3 hv = normalize(U.sun.xyz + v);
        float ga = 0.02 * 0.02;
        float glint = D_GGX(saturate(dot(s.n, hv)), ga) * V_SJ(nv, saturate(dot(s.n, U.sun.xyz)), ga) * F * saturate(dot(s.n, U.sun.xyz));
        float3 cabin = float3(0.02, 0.022, 0.025) * sh_irradiance(U, s.n);
        lit = cabin * (1.0 - F) + refl * F + glint * U.sun_col.rgb * shf;
        tm.amb = 0.0; tm.sun = glint * U.sun_col.rgb * shf; tm.env = refl * F; tm.w = F; tm.rough = 0.03; tm.alb = 0.0;
    }
    if (!rt_mode(U)) tm.amb *= 0.3;
    float3 pprev = U.prev_model[0].xyz + U.prev_model[1].xyz * lp.x + U.prev_model[2].xyz * lp.y + U.prev_model[3].xyz * lp.z;
    o = mrt2(U, lit, tm, i.pos, pprev);
    o.c.a = alpha; o.a.a = 0.0;
    if (alpha < 0.999) { o.s = 0.0; o.e.rgb = 0.0; o.al = 0.0; o.nr.w = 0.0; }
    return o;
}
"#;

const SKY: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
fragment MOut fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]],
                               texture2d<float> sky_lut [[texture(0)]], sampler sky_smp [[sampler(0)]]) {
    float4 far = U.inv_viewproj * float4(i.ndc, 1e-7, 1.0);
    float3 dir = normalize(far.xyz / far.w - U.cam.xyz);
    float3 sun = U.sun.xyz;
    float3 col = sky_sample(sky_lut, sky_smp, dir, sun);
    float c = dot(dir, sun);
    float r = U.sun_col.w;
    if (c > cos(r * 1.5)) {
        float a = acos(clamp(c, -1.0, 1.0)) / r;
        float limb = sqrt(max(1.0 - a * a, 0.0));
        float3 tsun = transmittance(max(U.cam.z, 0.0), dir.z, U.params.x);
        float disc = smoothstep(1.0, 0.97, a) * (0.4 + 0.6 * limb);
        col += tsun * disc / (PI * r * r) * 0.02;
    }
    MOut o = flat_out(float4(col, 1.0), 1.0);
    float4 pc = U.prev_viewproj * float4(dir, 0.0); float4 cc = U.viewproj_nj * float4(dir, 0.0);
    o.mv = float4((pc.xy / pc.w - cc.xy / cc.w) * float2(0.5, -0.5), 0.0, 1.0);
    return o;
}
"#;

const SKY_LUT: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]]) {
    float2 uv = i.p.xy / float2(SKY_LUT_W, SKY_LUT_H);
    float3 dir = sky_dir(uv, U.sun.xyz);
    return float4(sky_march(max(U.cam.z, 0.0), dir, U.sun.xyz, U.params.x, U.amb.rgb), 1.0);
}
"#;

const SSAO: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
float3 wpos(constant FrameU& U, float2 uv, float d) {
    float4 q = U.inv_viewproj * float4(uv.x * 2.0 - 1.0, 1.0 - uv.y * 2.0, d, 1.0);
    return q.xyz / q.w;
}
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], depth2d<float> dep [[texture(0)]]) {
    float2 uv = i.p.xy * 2.0 * U.screen.zw;
    float2 full = U.screen.xy;
    uint2 px = uint2(clamp(uv * full, float2(0.0), full - 1.0));
    float d = dep.read(px);
    if (d <= 0.0) return float4(1.0);
    float3 p = wpos(U, uv, d);
    float3 px1 = wpos(U, uv + float2(U.screen.z, 0.0), dep.read(px + uint2(1, 0)));
    float3 py1 = wpos(U, uv + float2(0.0, U.screen.w), dep.read(px + uint2(0, 1)));
    float3 n = normalize(cross(px1 - p, py1 - p));
    if (dot(n, U.cam.xyz - p) < 0.0) n = -n;
    float dist = length(p - U.cam.xyz);
    float R = clamp(dist * 0.02, 0.6, 4.0);
    float3 t = normalize(cross(n, abs(n.z) < 0.9 ? float3(0.0, 0.0, 1.0) : float3(1.0, 0.0, 0.0)));
    float3 b = cross(n, t);
    float rnd = hash12(i.p.xy) * 6.2831;
    float occ = 0.0;
    const int N = 12;
    for (int k = 0; k < N; k++) {
        float fk = (float(k) + 0.5) / float(N);
        float a = fk * 6.2831 * 2.618 + rnd;
        float r = sqrt(fk);
        float3 h = normalize(t * cos(a) * r + b * sin(a) * r + n * sqrt(max(1.0 - r * r, 0.05)));
        float3 sp = p + h * R * mix(0.2, 1.0, fract(fk * 7.13 + rnd));
        float4 q = U.viewproj * float4(sp, 1.0);
        float2 suv = float2(q.x / q.w * 0.5 + 0.5, 0.5 - q.y / q.w * 0.5);
        if (any(suv < 0.0) || any(suv > 1.0)) continue;
        float sd = dep.read(uint2(suv * full));
        float3 s = wpos(U, suv, sd);
        float ds = length(s - U.cam.xyz); float dsp = length(sp - U.cam.xyz);
        float range = smoothstep(0.0, 1.0, R / max(length(s - p), 1e-3));
        occ += (ds < dsp - 0.05 * R ? 1.0 : 0.0) * range;
    }
    float ao = 1.0 - occ / float(N);
    return float4(pow(saturate(ao), 1.5));
}
"#;

const VOLUME: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
float hg(float c, float g) { float g2 = g * g; return (1.0 - g2) / (4.0 * PI * pow(max(1.0 + g2 - 2.0 * g * c, 1e-4), 1.5)); }
float fog_density(constant FrameU& U, float3 p) {
    float t = U.cam.w;
    float h = max(p.z, 0.0);
    float d = U.fog.x * exp(-h / max(U.fog.y, 1.0));
    float vt = U.fog.w;
    if (U.fog2.x > 0.0 && vt > 0.0) {
        float n = vnoise3(p * 0.012 + float3(t * 0.02, t * 0.013, 0.0)) * 0.65 + vnoise3(p * 0.045 + float3(0.0, t * 0.05, t * 0.01)) * 0.35;
        float top = vt * (0.7 + 0.6 * n);
        d += U.fog2.x * smoothstep(top, top * 0.4, h) * (0.4 + 0.9 * n);
    }
    float drift = vnoise3(p * 0.004 + float3(t * 0.01, 0.0, 0.0));
    return d * (0.6 + 0.8 * drift);
}
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]],
                               depth2d<float> dep [[texture(0)]], texture2d<float> sky_lut [[texture(1)]],
                               array<depth2d<float>, 4> sm [[texture(2)]]) {
    float2 uv = i.p.xy * 2.0 * U.screen.zw;
    uint2 px = uint2(clamp(uv * U.screen.xy, float2(0.0), U.screen.xy - 1.0));
    float d = dep.read(px);
    float4 q = U.inv_viewproj * float4(uv.x * 2.0 - 1.0, 1.0 - uv.y * 2.0, max(d, 1e-7), 1.0);
    float3 wp = q.xyz / q.w;
    float3 ro = U.cam.xyz;
    float3 rd = normalize(wp - ro);
    float t_scene = d <= 0.0 ? 1e9 : length(wp - ro);
    float jit = hash12(i.p.xy + fract(U.cam.w * 7.31) * 113.0);
    float3 sun = U.sun.xyz;
    float mu = dot(rd, sun);
    float3 sunc = U.sun_col.rgb;
    float3 amb_up = sh_irradiance(U, float3(0.0, 0.0, 1.0)) / PI;
    float3 L = 0.0; float3 T = 1.0;
    float t_fog = min(t_scene, U.splits.w * 1.6);
    if (U.fog.x + U.fog2.x > 0.0) {
        const int N = 28;
        float ph_sun = hg(mu, U.fog.z) * 0.85 + hg(mu, -0.2) * 0.15;
        float t0 = 0.0;
        for (int k = 0; k < N; k++) {
            float f1 = (float(k) + 1.0) / float(N);
            float t1 = t_fog * f1 * f1;
            float dt = t1 - t0;
            float t = t0 + dt * jit;
            t0 = t1;
            float3 p = ro + rd * t;
            float sig = fog_density(U, p);
            if (sig < 1e-6) continue;
            float sh = shadow_factor(U, sm, p, float3(0.0, 0.0, 1.0)) * cloud_shadow(U, p);
            float3 S = sunc * sh * ph_sun + amb_up * 0.9 + U.flags.z * float3(1.0, 0.7, 0.45) * 0.02 * exp(-p.z / 150.0) * step(abs(p.x), 1300.0) * step(abs(p.y), 1300.0);
            float3 ll; float ld;
            float sp = spot(U, p, ll, ld);
            S += float3(1.0, 0.95, 0.85) * U.land_pos.w * sp * hg(dot(ll, -rd), 0.6) / max(ld * ld, 1.0);
            for (int n = 0; n < 3; n++) {
                float3 dn = p - U.nav[n].xyz; float r2 = max(dot(dn, dn), 0.25);
                float3 nc = n == 0 ? float3(1.0, 0.05, 0.02) : (n == 1 ? float3(0.05, 1.0, 0.2) : float3(1.0));
                S += nc * U.nav[n].w / r2 * (1.0 / (4.0 * PI));
            }
            float3 ext = float3(sig);
            float3 st = exp(-ext * dt);
            L += T * S * sig * (1.0 - st) / max(ext, 1e-6);
            T *= st;
        }
    }
    float cb = U.fog2.z, ct = U.fog2.w;
    if (U.fog2.y > 0.0 && abs(rd.z) > 1e-3) {
        float ta = (cb - ro.z) / rd.z, tb = (ct - ro.z) / rd.z;
        float tin = max(min(ta, tb), 0.0), tout = min(max(ta, tb), min(t_scene, 40000.0));
        if (tout > tin) {
            const int M = 36;
            float dt = (tout - tin) / float(M);
            float3 Lc = 0.0; float Tc = 1.0;
            float ph = hg(mu, 0.75) * 0.6 + hg(mu, -0.25) * 0.4;
            float3 amb = sh_irradiance(U, float3(0.0, 0.0, 1.0)) / PI;
            float t_mid = 0.0, wsum = 0.0;
            for (int k = 0; k < M; k++) {
                float t = tin + dt * (float(k) + jit);
                float3 p = ro + rd * t;
                float sig = cloud_density(U, p, true);
                if (sig < 1e-5) continue;
                float od = 0.0;
                for (int j = 1; j <= 3; j++) od += cloud_density(U, p + sun * (float(j) * 90.0), false) * 90.0;
                float tsun = exp(-od) * 0.7 + exp(-od * 0.25) * 0.3;
                float powder = 1.0 - exp(-sig * 160.0);
                float hfrac = saturate((p.z - cb) / (ct - cb));
                float3 S = sunc * tsun * ph * mix(0.6, 1.0, powder) * 1.6 + amb * mix(0.45, 1.0, hfrac);
                float st = exp(-sig * dt);
                Lc += Tc * S * (1.0 - st);
                Tc *= st;
                t_mid += t * (1.0 - st); wsum += 1.0 - st;
                if (Tc < 0.01) break;
            }
            float dist = wsum > 0.0 ? t_mid / wsum : tin;
            float haze = 1.0 - exp(-dist / 22000.0);
            float3 skyc = sky_lut.sample(lut_s, sky_uv(rd, sun)).rgb;
            Lc = mix(Lc, skyc * (1.0 - Tc), haze);
            L += T * Lc; T *= Tc;
        }
    }
    return float4(L, dot(T, float3(0.3333)));
}
"#;

const TRACE: &str = r#"
#include <metal_raytracing>
using namespace metal::raytracing;
struct Tri { float4 alb; float4 n; };
typedef intersector<triangle_data, instancing> Isect;
struct Hit { bool hit; float3 p; float3 n; float3 alb; };
Hit cast(instance_acceleration_structure as, device const Tri* st, device const Tri* at, texture2d<float> galb, float3 o, float3 d, float tmax) {
    Isect is;
    ray r(o, d, 0.02, tmax);
    auto h = is.intersect(r, as, 0xFF);
    Hit out; out.hit = h.type != intersection_type::none;
    if (!out.hit) return out;
    Tri t = h.instance_id == 0 ? st[h.primitive_id] : at[h.primitive_id];
    out.p = o + d * h.distance;
    out.n = t.n.xyz;
    if (dot(out.n, d) > 0.0) out.n = -out.n;
    out.alb = t.alb.rgb;
    if (t.alb.w < 0.5) {
        float2 uv = (out.p.xy + 3000.0) / 6000.0;
        out.alb = srgb_to_lin(galb.sample(clamp_s, uv, level(2.0)).rgb);
    }
    return out;
}
bool occluded(instance_acceleration_structure as, float3 o, float3 d) {
    Isect is; is.accept_any_intersection(true);
    ray r(o, d, 0.03, 6000.0);
    return is.intersect(r, as, 0xFF).type != intersection_type::none;
}
float3 sun_dir_jit(constant FrameU& U, float2 rnd) {
    float3 s = U.sun.xyz;
    float3 t = normalize(cross(s, abs(s.z) < 0.9 ? float3(0, 0, 1) : float3(1, 0, 0)));
    float3 b = cross(s, t);
    float r = 0.006 * sqrt(rnd.x); float a = rnd.y * 6.2831;
    return normalize(s + (t * cos(a) + b * sin(a)) * r);
}
float3 hit_light(constant FrameU& U, instance_acceleration_structure as, Hit h, float2 rnd) {
    float3 E = sh_irradiance(U, h.n) * 0.85;
    float3 sd = sun_dir_jit(U, rnd);
    float ndl = dot(h.n, sd);
    if (ndl > 0.0 && U.sun.z > 0.0 && !occluded(as, h.p + h.n * 0.05, sd)) E += U.sun_col.rgb * ndl * cloud_shadow(U, h.p);
    return h.alb / PI * E;
}
float3 miss_light(constant FrameU& U, texture2d<float> lut, float3 d, float rough, float height) {
    return env_radiance(U, lut, d, rough, height);
}
float2 rnd2(uint2 p, uint f, uint k) {
    return float2(hash12(float2(p) + float(f % 64u) * 17.13 + float(k) * 3.7), hash12(float2(p.yx) * 1.37 + float(f % 64u) * 7.31 + float(k) * 11.1));
}
kernel void trace(uint2 gid [[thread_position_in_grid]], constant FrameU& U [[buffer(0)]],
                  instance_acceleration_structure as [[buffer(1)]], device const Tri* st [[buffer(2)]], device const Tri* at [[buffer(3)]],
                  texture2d<float> c0 [[texture(0)]], texture2d<float> c1 [[texture(1)]], texture2d<float> c2 [[texture(2)]],
                  texture2d<float> c3 [[texture(3)]], texture2d<float> c4 [[texture(4)]], texture2d<float> c5 [[texture(5)]],
                  depth2d<float> dep [[texture(6)]], texture2d<float> sky_lut [[texture(7)]], texture2d<float> galb [[texture(8)]],
                  texture2d<float, access::write> out_c [[texture(9)]], texture2d<float, access::write> out_spec [[texture(10)]],
                  texture2d<float, access::write> out_rough [[texture(11)]],
                  texture2d<float, access::write> out_gi [[texture(12)]], texture2d<float, access::write> out_refl [[texture(13)]]) {
    if (gid.x >= uint(U.screen.x) || gid.y >= uint(U.screen.y)) return;
    float4 col = c0.read(gid);
    float d = dep.read(gid);
    float4 nr = c5.read(gid);
    float4 e = c3.read(gid);
    float4 s2 = c2.read(gid);
    out_spec.write(float4(float3(s2.w), 1.0), gid);
    out_rough.write(float4(e.w), gid);
    out_gi.write(float4(0.0, 0.0, 0.0, 1.0), gid);
    out_refl.write(float4(0.0), gid);
    if (d <= 0.0 || nr.w < 0.5) { out_c.write(col, gid); return; }
    float2 uv = (float2(gid) + 0.5) * U.screen.zw;
    float4 q = U.inv_viewproj * float4(uv.x * 2.0 - 1.0, 1.0 - uv.y * 2.0, d, 1.0);
    float3 p = q.xyz / q.w;
    float3 n = normalize(nr.xyz);
    float3 v = normalize(U.cam.xyz - p);
    if (dot(n, v) < 0.0) n = -n;
    float3 o = p + n * max(0.03, length(p - U.cam.xyz) * 2e-4);
    uint f = uint(U.post5.z);
    float vis = 1.0;
    if (U.sun.z > 0.0 && dot(n, U.sun.xyz) > -0.05) vis = occluded(as, o, sun_dir_jit(U, rnd2(gid, f, 0))) ? 0.0 : 1.0;
    float2 r1 = rnd2(gid, f, 1);
    float3 t = normalize(cross(n, abs(n.z) < 0.9 ? float3(0, 0, 1) : float3(1, 0, 0)));
    float3 b = cross(n, t);
    float rr = sqrt(r1.x); float ph = r1.y * 6.2831;
    float3 gd = normalize(t * rr * cos(ph) + b * rr * sin(ph) + n * sqrt(max(1.0 - r1.x, 0.0)));
    Hit gh = cast(as, st, at, galb, o, gd, 3000.0);
    float3 Lgi = gh.hit ? hit_light(U, as, gh, rnd2(gid, f, 2)) : miss_light(U, sky_lut, gd, 1.0, p.z);
    float w = s2.w;
    float3 Lr = 0.0;
    if (w > 0.01) {
        float rough = e.w;
        float2 r3 = rnd2(gid, f, 3);
        float a = rough * rough;
        float phi = r3.x * 6.2831;
        float ct = sqrt((1.0 - r3.y) / (1.0 + (a * a - 1.0) * r3.y));
        float st2 = sqrt(1.0 - ct * ct);
        float3 hvec = normalize(t * st2 * cos(phi) + b * st2 * sin(phi) + n * ct);
        float3 rd = reflect(-v, hvec);
        if (dot(rd, n) < 0.0) rd = reflect(-v, n);
        Hit rh = cast(as, st, at, galb, o, rd, 4000.0);
        Lr = rh.hit ? hit_light(U, as, rh, rnd2(gid, f, 4)) : miss_light(U, sky_lut, rd, rough, p.z);
    }
    float3 tr;
    aerial(U, float3(0.0), p, tr);
    out_gi.write(float4(Lgi * tr, vis), gid);
    out_refl.write(float4(Lr * tr, w), gid);
    float3 c = col.rgb - c1.read(gid).rgb - e.rgb - s2.rgb * (1.0 - vis) + (c4.read(gid).rgb * Lgi + w * Lr) * tr;
    out_c.write(float4(max(c, 0.0), 1.0), gid);
}
kernel void compose(uint2 gid [[thread_position_in_grid]], constant FrameU& U [[buffer(0)]],
                    texture2d<float> c0 [[texture(0)]], texture2d<float> c1 [[texture(1)]], texture2d<float> c2 [[texture(2)]],
                    texture2d<float> c3 [[texture(3)]], texture2d<float> c4 [[texture(4)]], texture2d<float> c5 [[texture(5)]],
                    depth2d<float> dep [[texture(6)]], texture2d<float> gi [[texture(7)]], texture2d<float> rf [[texture(8)]],
                    texture2d<float, access::write> out_c [[texture(9)]]) {
    if (gid.x >= uint(U.screen.x) || gid.y >= uint(U.screen.y)) return;
    float4 col = c0.read(gid);
    float d0 = dep.read(gid);
    float4 n0 = c5.read(gid);
    if (d0 <= 0.0 || n0.w < 0.5) { out_c.write(col, gid); return; }
    float rough = c3.read(gid).w;
    float3 g = 0.0; float3 r = 0.0; float vis = 0.0; float wg = 0.0, wr = 0.0, wv = 0.0;
    int2 sz = int2(U.screen.xy);
    for (int dy = -2; dy <= 2; dy++) {
        for (int dx = -2; dx <= 2; dx++) {
            int2 q = clamp(int2(gid) + int2(dx, dy) * 2, int2(0), sz - 1);
            float d = dep.read(uint2(q));
            float4 n = c5.read(uint2(q));
            float wd = exp(-abs(d - d0) / (0.02 * d0 + 1e-7)) * pow(saturate(dot(n.xyz, n0.xyz)), 24.0) * n.w;
            float k = exp(-float(dx * dx + dy * dy) * 0.25);
            float4 a = gi.read(uint2(q));
            float4 b = rf.read(uint2(q));
            g += a.rgb * wd * k; wg += wd * k;
            float kr = exp(-float(dx * dx + dy * dy) / max(rough * rough * 12.0, 0.05));
            r += b.rgb * wd * kr; wr += wd * kr;
            float kv = (abs(dx) <= 1 && abs(dy) <= 1) ? 1.0 : 0.0;
            vis += a.a * wd * kv; wv += wd * kv;
        }
    }
    float4 gc = gi.read(gid); float4 rc = rf.read(gid);
    g = wg > 1e-4 ? g / wg : gc.rgb;
    r = wr > 1e-4 ? r / wr : rc.rgb;
    vis = wv > 1e-4 ? vis / wv : gc.a;
    float3 c = col.rgb - c1.read(gid).rgb - c3.read(gid).rgb - c2.read(gid).rgb * (1.0 - vis) + c4.read(gid).rgb * g + rc.a * r;
    out_c.write(float4(max(c, 0.0), 1.0), gid);
}
"#;

const COMBINE: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
float3 world_at(constant FrameU& U, float2 uv, float d) {
    float4 q = U.inv_viewproj * float4(uv.x * 2.0 - 1.0, 1.0 - uv.y * 2.0, max(d, 1e-7), 1.0);
    return q.xyz / q.w;
}
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], texture2d<float> hdr [[texture(0)]],
                               texture2d<float> amb [[texture(1)]], texture2d<float> aot [[texture(2)]], depth2d<float> dep [[texture(3)]],
                               texture2d<float> vol [[texture(4)]]) {
    uint2 px = uint2(i.p.xy);
    float2 uv = i.p.xy * U.post4.zw;
    uint2 ipx = uint2(min(uv * U.screen.xy, U.screen.xy - 1.0));
    float d0 = dep.read(ipx);
    float ao = 0.0; float wsum = 0.0; float4 vl = 0.0;
    for (int k = 0; k < 4; k++) {
        float2 o = float2(k & 1, k >> 1) * 2.0 - 1.0;
        float2 suv = uv + o * U.screen.zw * 1.5;
        float dd = dep.read(uint2(clamp(suv * U.screen.xy, float2(0.0), U.screen.xy - 1.0)));
        float w = 1.0 / (1e-6 + abs(dd - d0) / max(d0, 1e-7));
        ao += aot.sample(clamp_s, suv).r * w; vl += vol.sample(clamp_s, suv) * w; wsum += w;
    }
    ao = ao / wsum; vl = vl / wsum;
    float3 c = ((hdr.read(px).rgb - amb.read(ipx).rgb * (1.0 - ao) * (1.0 - U.post5.y)) * vl.a + vl.rgb) * U.sun.w;
    float z = d0 <= 0.0 ? 1e5 : length(world_at(U, uv, d0) - U.cam.xyz);
    float zf = U.post0.x, f = U.post0.y, A = U.post0.z;
    float coc = A * f * (z - zf) / (z * max(zf - f, 1e-3)) / U.post0.w * U.screen.y;
    if (U.post1.y > 0.5) coc = max(0.0, abs(uv.y - 0.52) - 0.06) * U.screen.y * 0.09;
    coc = clamp(coc * U.post4.y / U.screen.y, -U.post3.w, U.post3.w);
    return float4(min(c, float3(30000.0)), coc);
}
"#;

const DOF: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], texture2d<float> comb [[texture(0)]]) {
    float2 hpx = U.post4.zw * 2.0;
    float2 uv = i.p.xy * hpx;
    float4 c0 = comb.sample(clamp_s, uv);
    float r0 = abs(c0.a) * 0.25;
    float R = U.post3.w * 0.25;
    if (R < 0.5) return float4(c0.rgb, r0);
    const int RINGS = 5;
    float w0 = 1.0 / max(r0 * r0, 1.0);
    float3 acc = c0.rgb * w0; float wsum = w0;
    float2 cpos = (uv - 0.5) * 2.0;
    bool hex = U.post1.w > 0.5;
    float rot = 0.26;
    for (int r = 1; r <= RINGS; r++) {
        int n = 6 * r;
        for (int j = 0; j < n; j++) {
            float2 o;
            if (hex) {
                int side = j / r; float t = float(j % r) / float(r);
                float a0 = float(side) * PI / 3.0 + rot, a1 = float(side + 1) * PI / 3.0 + rot;
                o = mix(float2(cos(a0), sin(a0)), float2(cos(a1), sin(a1)), t) * float(r) / float(RINGS);
            } else {
                float a = (float(j) + 0.5 * float(r & 1)) / float(n) * 2.0 * PI;
                o = float2(cos(a), sin(a)) * float(r) / float(RINGS);
            }
            if (U.post1.z > 0.0 && length(o - cpos * U.post1.z) > 1.0) continue;
            float dist = length(o) * R;
            float4 s = comb.sample(clamp_s, uv + o * R * hpx * float2(1.0, U.post4.x * U.post4.w));
            float rs = abs(s.a) * 0.25;
            if (s.a > c0.a) rs = min(rs, r0);
            float w = saturate(rs - dist + 1.0) / max(rs * rs, 1.0);
            acc += s.rgb * w; wsum += w;
        }
    }
    return float4(acc / wsum, r0);
}
"#;

const DOWN: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], texture2d<float> src [[texture(0)]]) {
    float2 ts = U.params.zw;
    float2 uv = (floor(i.p.xy) * 2.0 + 1.0) * ts;
    float3 a = src.sample(clamp_s, uv + float2(-1, -1) * ts).rgb, b = src.sample(clamp_s, uv + float2(1, -1) * ts).rgb;
    float3 c = src.sample(clamp_s, uv + float2(-1, 1) * ts).rgb, d = src.sample(clamp_s, uv + float2(1, 1) * ts).rgb;
    float3 e = src.sample(clamp_s, uv).rgb;
    float4 w = 1.0 / (1.0 + float4(dot(a, 0.33), dot(b, 0.33), dot(c, 0.33), dot(d, 0.33)) * U.params.y);
    float3 o = (a * w.x + b * w.y + c * w.z + d * w.w) / (w.x + w.y + w.z + w.w);
    return float4(mix(o, e, 0.25), 1.0);
}
"#;

const UP: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], texture2d<float> src [[texture(0)]]) {
    float2 ts = U.params.zw;
    float2 uv = (i.p.xy * 0.5) * ts;
    float3 c = src.sample(clamp_s, uv).rgb * 4.0;
    c += (src.sample(clamp_s, uv + float2(ts.x, 0)).rgb + src.sample(clamp_s, uv - float2(ts.x, 0)).rgb + src.sample(clamp_s, uv + float2(0, ts.y)).rgb + src.sample(clamp_s, uv - float2(0, ts.y)).rgb) * 2.0;
    c += src.sample(clamp_s, uv + ts).rgb + src.sample(clamp_s, uv - ts).rgb + src.sample(clamp_s, uv + float2(ts.x, -ts.y)).rgb + src.sample(clamp_s, uv + float2(-ts.x, ts.y)).rgb;
    return float4(c / 16.0, 1.0);
}
"#;

const FINAL: &str = r#"
vertex FsOut vertexShader(FsIn v [[stage_in]]) { FsOut o; o.p = float4(v.pos, 0.0, 1.0); o.ndc = v.pos; return o; }
float3 lensed(texture2d<float> comb, texture2d<float> dof, float2 uv) {
    float4 s = comb.sample(clamp_s, uv);
    float4 b = dof.sample(clamp_s, uv);
    return mix(s.rgb, b.rgb, smoothstep(0.35, 1.2, b.a));
}
fragment float4 fragmentShader(FsOut i [[stage_in]], constant FrameU& U [[buffer(0)]], texture2d<float> comb [[texture(0)]],
                               texture2d<float> dof [[texture(1)]], texture2d<float> bloom [[texture(2)]],
                               depth2d<float> dep [[texture(3)]], texture2d<float> amb [[texture(4)]]) {
    float2 uv = i.p.xy * U.post6.zw;
    bool footage = U.post1.x > 0.5;
    float aspect = U.post6.x * U.post6.w;
    float2 c = (uv - 0.5) * float2(aspect, 1.0);
    float k = U.post2.w;
    float r2 = dot(c, c);
    float norm = 1.0 + k * (0.25 * aspect * aspect + 0.25);
    float2 uvd = 0.5 + c * (1.0 + k * r2) / norm / float2(aspect, 1.0);
    float3 col;
    float ca = footage ? U.post3.y : 0.0;
    if (ca > 0.0) {
        float2 dvec = (uvd - 0.5);
        col = float3(lensed(comb, dof, 0.5 + dvec * (1.0 + ca)).r, lensed(comb, dof, uvd).g, lensed(comb, dof, 0.5 + dvec * (1.0 - ca)).b);
    } else {
        col = lensed(comb, dof, uvd);
    }
    if (footage && U.post2.x > 0.0) {
        uint2 dp = uint2(clamp(uvd * U.screen.xy, float2(0.0), U.screen.xy - 1.0));
        float d = dep.read(dp);
        bool moving = amb.read(dp).a < 0.5 && d > 0.0;
        if (!moving) {
            float4 q = U.inv_viewproj * float4(uvd.x * 2.0 - 1.0, 1.0 - uvd.y * 2.0, max(d, 1e-7), 1.0);
            float3 wp = q.xyz / q.w;
            if (d <= 0.0) wp = U.cam.xyz + normalize(wp - U.cam.xyz) * 1e5;
            float4 pc = U.prev_viewproj * float4(wp, 1.0);
            float2 puv = float2(pc.x / pc.w * 0.5 + 0.5, 0.5 - pc.y / pc.w * 0.5);
            float2 vel = (uvd - puv) * (U.post2.x / max(U.post2.y, 1e-3));
            float vl = length(vel * U.post4.xy);
            if (vl > 0.5) {
                vel *= min(1.0, 60.0 / vl);
                float3 acc = col; float n = 1.0;
                for (int s = 0; s < 10; s++) {
                    float t = (float(s) + hash12(i.p.xy + float(s))) / 10.0 - 0.5;
                    float2 su = uvd + vel * t;
                    uint2 sp = uint2(clamp(su * U.screen.xy, float2(0.0), U.screen.xy - 1.0));
                    if (amb.read(sp).a < 0.5 && dep.read(sp) > 0.0) continue;
                    acc += lensed(comb, dof, su); n += 1.0;
                }
                col = acc / n;
            }
        }
    }
    col += bloom.sample(clamp_s, uvd).rgb * U.post2.z;
    float3 m = aces(col);
    if (footage) {
        float l = dot(m, float3(0.2126, 0.7152, 0.0722));
        m = mix(float3(l), m, 0.82);
        m = m * float3(1.02, 1.0, 0.95) + float3(0.012, 0.016, 0.02) * (1.0 - m);
        m = m * m * (3.0 - 2.0 * m) * 0.35 + m * 0.65;
    }
    if (U.post1.y > 0.5) {
        float l = dot(m, float3(0.2126, 0.7152, 0.0722));
        m = saturate(mix(float3(l), m, 1.35));
    }
    float2 vc = (uv - 0.5) * float2(aspect, 1.0);
    float vig = pow(cos(clamp(length(vc) * U.post3.z, 0.0, 1.5)), 4.0);
    m *= vig;
    float3 o = lin_to_srgb(saturate(m));
    if (footage) {
        float g = hash12(i.p.xy * 0.73 + fract(U.post3.x) * 517.0) + hash12(i.p.xy * 1.31 + fract(U.post3.x * 1.7) * 311.0) - 1.0;
        o += g * U.post3.y * 4.0 * (0.35 + 0.65 * sqrt(dot(o, float3(0.33))));
    }
    return float4(o, 1.0);
}
"#;

fn with_prelude(body: &str) -> String {
    format!("{PRELUDE}{body}")
}

pub fn terrain() -> String {
    format!("{PRELUDE}{PBR}{TERRAIN}")
}
pub fn building(meta: &[(&str, f32, f32, bool)]) -> String {
    let m: Vec<String> = meta.iter().map(|f| format!("float4({:.1}, {:.1}, {:.1}, 0.0)", f.1, f.2, if f.3 { 1.0 } else { 0.0 })).collect();
    format!("{PRELUDE}{PBR}{BUILDING}").replace("FACADE_META", &m.join(", "))
}
const SHADOW_PV: &str = r#"
struct VIn { float3 pos [[attribute(0)]]; };
struct SOut { float4 p [[position]]; };
vertex SOut vertexShader(VIn v [[stage_in]], constant FrameU& U [[buffer(0)]]) {
    SOut o; o.p = U.shadow[int(U.params.y)] * float4(v.pos, 1.0); return o;
}
fragment void fragmentShader() {}
"#;
pub fn shadow_pv() -> String {
    format!("{PRELUDE}{SHADOW_PV}")
}
pub fn shadow_dv() -> String {
    format!("{PRELUDE}{SHADOW_PV}")
}
pub fn dynamic() -> String {
    format!("{PRELUDE}{PBR}{DYNAMIC}")
}
pub fn sky() -> String {
    with_prelude(SKY)
}
pub const SKY_LUT_W: u32 = 256;
pub const SKY_LUT_H: u32 = 128;
pub fn sky_lut() -> String {
    with_prelude(SKY_LUT).replace("SKY_LUT_W", &format!("{SKY_LUT_W}.0")).replace("SKY_LUT_H", &format!("{SKY_LUT_H}.0"))
}
pub fn ssao() -> String {
    format!("{PRELUDE}{PBR}{SSAO}")
}
pub fn volume() -> String {
    format!("{PRELUDE}{PBR}{VOLUME}")
}
pub fn trace() -> String {
    format!("{PRELUDE}{PBR}{TRACE}")
}
pub fn combine() -> String {
    format!("{PRELUDE}{PBR}{COMBINE}")
}
pub fn dof() -> String {
    format!("{PRELUDE}{PBR}{DOF}")
}
pub fn down() -> String {
    format!("{PRELUDE}{PBR}{DOWN}")
}
pub fn up() -> String {
    format!("{PRELUDE}{PBR}{UP}")
}
pub fn final_pass() -> String {
    format!("{PRELUDE}{PBR}{FINAL}")
}
