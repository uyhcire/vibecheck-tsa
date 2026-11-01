//! Point-mass 3D aircraft: a 3D Dubins-style kinematic core (after Molnar et
//! al.) with speed dynamics (thrust, drag), lift limited by airspeed (so stall
//! emerges on its own), and first-order lags on load factor, roll rate and
//! throttle. The same equations drive the simulated aircraft and the escape
//! predictor.
//!
//! State: x, y, z [m], v airspeed [m/s], gamma flight-path angle, psi heading
//! (unwrapped, CCW from +x), phi bank (+ = left wing down = left turn), p roll
//! rate, n load-factor demand (lagged), thr throttle (lagged).
//! Command: n_c load factor, p_c roll rate [rad/s], thr_c throttle 0..1.

pub const G: f64 = 9.81;
pub const DT: f64 = 0.01;
pub const DT_F: f64 = 0.02;
pub const STEPS_PER_TICK: u64 = 2;

pub type State = [f64; 10];
pub type Cmd = [f64; 3];

pub const X: usize = 0;
pub const Y: usize = 1;
pub const Z: usize = 2;
pub const V: usize = 3;
pub const GAM: usize = 4;
pub const PSI: usize = 5;
pub const PHI: usize = 6;
pub const P: usize = 7;
pub const N: usize = 8;
pub const THR: usize = 9;

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub m: f64,
    pub s: f64,
    pub rho: f64,
    pub clmax: f64,
    pub cd0: f64,
    pub k: f64,
    /// Effective propeller power [W]; thrust = thr * power / sqrt(v^2 + v0^2).
    pub power: f64,
    pub t_static: f64,
    pub tau_n: f64,
    pub tau_p: f64,
    pub tau_thr: f64,
    pub p_max: f64,
    pub n_max: f64,
    pub n_min: f64,
}

pub const V_STALL: f64 = 25.0;

impl Params {
    /// Light-sport numbers: stall 25 m/s (1 g), cruise 50 m/s at ~64 %
    /// throttle, top speed ~60 m/s, ~4 m/s climb in a 45 deg bank at 35 m/s.
    pub fn nominal() -> Params {
        let (m, s, rho) = (600.0, 12.0, 1.225);
        Params {
            m,
            s,
            rho,
            clmax: 2.0 * m * G / (rho * s * V_STALL * V_STALL),
            cd0: 0.03,
            k: 0.055,
            power: 55_000.0,
            t_static: 2700.0,
            tau_n: 0.2,
            tau_p: 0.12,
            tau_thr: 0.6,
            p_max: 60f64.to_radians(),
            n_max: 3.8,
            n_min: -1.5,
        }
    }
    /// "Weaker, slower aircraft" used by the mismatch toggle.
    pub fn mismatch() -> Params {
        let mut p = Params::nominal();
        p.power *= 0.8;
        p.t_static *= 0.8;
        p.cd0 *= 1.12;
        p.tau_n *= 1.5;
        p.tau_p *= 1.5;
        p.tau_thr *= 1.5;
        p.p_max *= 0.8;
        p.clmax *= 0.93;
        p
    }
}

#[inline]
pub fn n_lift(p: &Params, v: f64) -> f64 {
    0.5 * p.rho * v * v * p.s * p.clmax / (p.m * G)
}

/// Load factor actually produced: the demand, limited by available lift.
#[inline]
pub fn n_act(p: &Params, s: &State) -> f64 {
    let nl = n_lift(p, s[V].max(1.0));
    s[N].clamp(-0.5 * nl, nl)
}

#[inline]
pub fn thrust_drag(p: &Params, v: f64, n: f64, thr: f64) -> (f64, f64) {
    let v = v.max(5.0);
    let q = 0.5 * p.rho * v * v;
    let cl = n * p.m * G / (q * p.s);
    let d = q * p.s * (p.cd0 + p.k * cl * cl);
    let v0 = p.power / p.t_static;
    let t = thr * p.power / (v * v + v0 * v0).sqrt();
    (t, d)
}

#[inline]
pub fn deriv(p: &Params, s: &State, u: &Cmd, wind: &[f64; 3]) -> State {
    let v = s[V].max(5.0);
    let n = n_act(p, s);
    let (t, d) = thrust_drag(p, v, n, s[THR]);
    let (sg, cg) = s[GAM].sin_cos();
    let cg = cg.max(0.1);
    let (sps, cps) = s[PSI].sin_cos();
    let (sph, cph) = s[PHI].sin_cos();
    let pc = u[1].clamp(-p.p_max, p.p_max);
    let nc = u[0].clamp(p.n_min, p.n_max);
    let tc = u[2].clamp(0.0, 1.0);
    [
        v * cg * cps + wind[0],
        v * cg * sps + wind[1],
        v * sg + wind[2],
        (t - d) / p.m - G * sg,
        G / v * (n * cph - cg),
        G / v * n * sph / cg,
        s[P],
        (pc - s[P]) / p.tau_p,
        (nc - s[N]) / p.tau_n,
        (tc - s[THR]) / p.tau_thr,
    ]
}

/// One RK4 step. `cmd(stage_state, time_offset)` is evaluated at every stage,
/// so feedback laws act in continuous time and a constant command is exact
/// zero-order hold.
#[inline]
pub fn rk4<F: FnMut(&State, f64) -> Cmd>(p: &Params, s: &mut State, dt: f64, wind: &[f64; 3], mut cmd: F) {
    let add = |a: &State, k: &State, h: f64| -> State {
        let mut o = *a;
        for i in 0..10 {
            o[i] += k[i] * h;
        }
        o
    };
    let u1 = cmd(s, 0.0);
    let k1 = deriv(p, s, &u1, wind);
    let s2 = add(s, &k1, 0.5 * dt);
    let u2 = cmd(&s2, 0.5 * dt);
    let k2 = deriv(p, &s2, &u2, wind);
    let s3 = add(s, &k2, 0.5 * dt);
    let u3 = cmd(&s3, 0.5 * dt);
    let k3 = deriv(p, &s3, &u3, wind);
    let s4 = add(s, &k3, dt);
    let u4 = cmd(&s4, dt);
    let k4 = deriv(p, &s4, &u4, wind);
    for i in 0..10 {
        s[i] += dt / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]);
    }
}

pub fn lerp_cmd(a: &Cmd, b: &Cmd, t: f64) -> Cmd {
    [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]
}

/// A trimmed level-flight state at speed `v`.
pub fn trimmed(x: f64, y: f64, z: f64, v: f64, gam: f64, psi: f64, thr: f64) -> State {
    [x, y, z, v, gam, psi, 0.0, 0.0, gam.cos(), thr]
}

// ---------------------------------------------------------------- airframe geometry

/// Wing line of the drawn Cessna (`c172.rs`), body axes x forward, y left, z up from the CG; the `WING_R`
/// capsule holds every wing vertex outboard of 4 m span, and inboard of that the `R_BODY` sphere does.
pub const WING_X: f64 = -0.17;
pub const WING_Z: f64 = 1.065;
pub const WING_TIP: f64 = 5.5;
pub const WING_R: f64 = 0.8;

/// Angle of attack the renderer draws: the point-mass lift curve at this load factor and airspeed.
pub fn drawn_alpha(p: &Params, s: &State) -> f64 {
    let q = 0.5 * p.rho * s[V].max(15.0).powi(2);
    ((s[N] * p.m * G / (q * p.s) - 0.3) / 5.2).clamp(-0.12, 0.28)
}

/// Body axes (forward, left, up) of the drawn aircraft: flight path rolled by the bank, nose up by `alpha`.
pub fn airframe_axes(s: &State, alpha: f64) -> [[f64; 3]; 3] {
    let (sg, cg) = s[GAM].sin_cos();
    let (sp, cp) = s[PSI].sin_cos();
    let (sb, cb) = s[PHI].sin_cos();
    let f = [cg * cp, cg * sp, sg];
    let l0 = [-sp, cp, 0.0];
    let u0 = [f[1] * l0[2] - f[2] * l0[1], f[2] * l0[0] - f[0] * l0[2], f[0] * l0[1] - f[1] * l0[0]];
    let l: [f64; 3] = std::array::from_fn(|i| l0[i] * cb - u0[i] * sb);
    let u: [f64; 3] = std::array::from_fn(|i| u0[i] * cb + l0[i] * sb);
    let (sa, ca) = alpha.sin_cos();
    [std::array::from_fn(|i| f[i] * ca + u[i] * sa), l, std::array::from_fn(|i| u[i] * ca - f[i] * sa)]
}

/// The wing line's two tips in world coordinates (left tip first), for the nominal aircraft as drawn.
pub fn wing_tips(s: &State) -> [[f64; 3]; 2] {
    let [f, l, u] = airframe_axes(s, drawn_alpha(&Params::nominal(), s));
    let tip = |side: f64| std::array::from_fn(|i| s[i] + f[i] * WING_X + l[i] * side * WING_TIP + u[i] * WING_Z);
    [tip(1.0), tip(-1.0)]
}
