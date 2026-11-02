//! Boundary regimes of the gate filter (`--safety-filter exact-rollout`) under the contact objective (`docs/safety-objective.md`):
//! slices through the state space near one obstacle, and markers along each slice, all drawn at actual contact.
//!
//! - **Proven safe** (`contact_verdict`): one of the gate's six escapes, flown by exact rollout on a fork of the
//!   JSBSim aircraft, keeps positive airframe clearance at every frame and reaches a terminal set (zero vertical
//!   margin). The rollout is exact; the terminal sets are checked numerically on the settled rollout.
//! - **Best escape found** (`best_found`): some program in a much richer family avoids contact the same way.
//!   Empirical: a failed search proves nothing.
//! - **Proven unsafe** (`outer_bound`): no point mass inside a stated envelope (`env`) avoids the city geometry.
//! - **Gate accepts** (`gate_verdict`): the deployed filter's own acceptance, with its 4 m margin: a property of
//!   the filter, not of safety.

use crate::envfilter::*;
use crate::jsb::*;
use crate::model::*;
use crate::world::{Rng, World, CELL, MAP_HALF, NC, TN, TSP};
use std::f64::consts::PI;

pub const G0: f64 = 9.80665;

// ------------------------------------------------------------------------------------------------ causes

/// Why one escape's check failed, or `Ok`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Cause {
    Ok,
    HitGround,
    HitTerrainAhead,
    HitRoof,
    HitWallSide,
    HitWallAhead,
    TermNotTurning,
    TermUnsettled,
    TermRayBuilding,
    TermRayTerrain,
    TermHelix,
    NoStreet,
}

impl Cause {
    pub fn label(self) -> &'static str {
        match self {
            Cause::Ok => "verified",
            Cause::HitGround => "hit: ground below",
            Cause::HitTerrainAhead => "hit: terrain ahead",
            Cause::HitRoof => "hit: roof below",
            Cause::HitWallSide => "hit: wall beside",
            Cause::HitWallAhead => "hit: wall ahead",
            Cause::TermNotTurning => "terminal: still pulling up",
            Cause::TermUnsettled => "terminal: climb not settled",
            Cause::TermRayBuilding => "terminal: ray blocked by building",
            Cause::TermRayTerrain => "terminal: ray blocked by terrain",
            Cause::TermHelix => "terminal: helix blocked",
            Cause::NoStreet => "no street axis",
        }
    }
    pub fn short(self) -> &'static str {
        match self {
            Cause::Ok => "ok",
            Cause::HitGround => "ground",
            Cause::HitTerrainAhead => "terrain-ahead",
            Cause::HitRoof => "roof",
            Cause::HitWallSide => "wall-side",
            Cause::HitWallAhead => "wall-ahead",
            Cause::TermNotTurning => "not-turning",
            Cause::TermUnsettled => "unsettled",
            Cause::TermRayBuilding => "ray-bldg",
            Cause::TermRayTerrain => "ray-terrain",
            Cause::TermHelix => "helix",
            Cause::NoStreet => "no-street",
        }
    }
    pub fn color(self) -> &'static str {
        match self {
            Cause::Ok => "#2e9e5b",
            Cause::HitGround => "#8c5a2b",
            Cause::HitTerrainAhead => "#c48a3a",
            Cause::HitRoof => "#7a4fb0",
            Cause::HitWallSide => "#2f6fd0",
            Cause::HitWallAhead => "#d03a2f",
            Cause::TermNotTurning => "#9aa3ad",
            Cause::TermUnsettled => "#e0b400",
            Cause::TermRayBuilding => "#e07b39",
            Cause::TermRayTerrain => "#a3c23a",
            Cause::TermHelix => "#3fb8c4",
            Cause::NoStreet => "#dddddd",
        }
    }
    pub fn all() -> [Cause; 12] {
        use Cause::*;
        [Ok, HitGround, HitTerrainAhead, HitRoof, HitWallSide, HitWallAhead, TermNotTurning, TermUnsettled, TermRayBuilding, TermRayTerrain, TermHelix, NoStreet]
    }
}

/// Which escape-law cap bound on more than 15% of frames: load factor (`n`), α (`alpha`), both, or neither.
pub fn envelope_tag(r: &Roll) -> &'static str {
    let f = r.frames.max(1) as f64;
    let (n, a) = (r.lim[0] as f64 / f > 0.15, r.lim[1] as f64 / f > 0.15);
    match (n, a) {
        (true, true) => "n+alpha",
        (true, false) => "n",
        (false, true) => "alpha",
        _ => "",
    }
}

/// Classify a failed rollout.
pub fn classify(world: &World, r: &Roll) -> Cause {
    match r.outcome {
        Outcome::Ok => Cause::Ok,
        Outcome::Hit => classify_hit(world, &r.end),
        Outcome::Horizon | Outcome::Budget => {
            if r.path.is_empty() {
                return Cause::NoStreet;
            }
            match r.why {
                None | Some(TermFail::NotTurning) => Cause::TermNotTurning,
                Some(TermFail::Unsettled) | Some(TermFail::Wobble) | Some(TermFail::Shallow) | Some(TermFail::RayLong) | Some(TermFail::Slow) => Cause::TermUnsettled,
                Some(TermFail::RayBlocked { x, y, h }) => {
                    let i = (((x + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
                    let j = (((y + MAP_HALF) / CELL).floor().max(0.0) as usize).min(NC - 1);
                    if h > world.raw_terr[j * NC + i] as f64 + 0.5 {
                        Cause::TermRayBuilding
                    } else {
                        Cause::TermRayTerrain
                    }
                }
                Some(TermFail::HelixBlocked { .. }) | Some(TermFail::HelixOffMap) => Cause::TermHelix,
            }
        }
    }
}

/// What the airframe was closest to when its clearance fell below the margin.
pub fn classify_hit(world: &World, s: &State) -> Cause {
    let p = [s[X], s[Y], s[Z]];
    let terr = p[2] - world.terrain(p[0], p[1]);
    let mut best: Option<(f64, [f64; 3])> = None;
    for b in &world.boxes {
        let q = [p[0].clamp(b.x0, b.x1), p[1].clamp(b.y0, b.y1), p[2].clamp(b.z0, b.z1)];
        let d = ((q[0] - p[0]).powi(2) + (q[1] - p[1]).powi(2) + (q[2] - p[2]).powi(2)).sqrt();
        if best.map_or(true, |(bd, _)| d < bd) {
            best = Some((d, q));
        }
    }
    let (bd, q) = best.unwrap_or((f64::INFINITY, p));
    if terr <= bd {
        // Terrain: below unless the ground rises steeply ahead.
        let (c, sn) = (s[PSI].cos(), s[PSI].sin());
        let ahead = world.terrain(p[0] + 20.0 * c, p[1] + 20.0 * sn) - world.terrain(p[0], p[1]);
        return if ahead > 6.0 { Cause::HitTerrainAhead } else { Cause::HitGround };
    }
    let d = [q[0] - p[0], q[1] - p[1], q[2] - p[2]];
    let hor = (d[0] * d[0] + d[1] * d[1]).sqrt();
    if -d[2] >= hor {
        return Cause::HitRoof;
    }
    let ang = (d[1].atan2(d[0]) - s[PSI] + PI).rem_euclid(2.0 * PI) - PI;
    if ang.abs() < PI / 4.0 {
        Cause::HitWallAhead
    } else {
        Cause::HitWallSide
    }
}

// ------------------------------------------------------------------------------------------------ filter

#[derive(Clone, Debug)]
pub struct EscOut {
    pub outcome: Outcome,
    pub cause: Cause,
    pub env: &'static str,
    pub t: f64,
    pub min_clear: f64,
    pub nz_max: f64,
}

#[derive(Clone, Debug)]
pub struct Verdict {
    pub ok: bool,
    pub per_esc: Vec<EscOut>,
}

/// The gate filter's own verdict at a start state (`Gate::new`'s search: every escape, no budget, its margin).
pub fn gate_verdict(world: &World, s: &State) -> Verdict {
    verdict_cfg(world, &JsbPlant::new(s), &RollCfg::filter())
}

/// The gate's escapes judged at contact: positive airframe clearance at every frame, zero-margin terminal sets.
pub fn contact_verdict(world: &World, s: &State) -> Verdict {
    verdict_cfg(world, &JsbPlant::new(s), &CONTACT)
}

pub const CONTACT: RollCfg<'static> = RollCfg { margin: 0.0, term_margin: 0.0, horizon: HORIZON, prefix: &[], check_every: 1, swept: false };

pub fn filter_verdict_plant(world: &World, p: &JsbPlant) -> Verdict {
    verdict_cfg(world, p, &RollCfg::filter())
}

pub fn verdict_cfg(world: &World, p: &JsbPlant, cfg: &RollCfg) -> Verdict {
    let per_esc: Vec<EscOut> = (0..n_esc())
        .map(|e| {
            let r = rollout_cfg(world, p, Law::new(e), usize::MAX, None, cfg);
            EscOut { outcome: r.outcome, cause: classify(world, &r), env: envelope_tag(&r), t: r.t, min_clear: r.min_clear, nz_max: r.nz_max }
        })
        .collect();
    Verdict { ok: per_esc.iter().any(|e| e.outcome == Outcome::Ok), per_esc }
}

// ------------------------------------------------------------------------------------------------ richer search

/// One program of the richer search: a fly-by-wire prefix, then an escape law with its own bank and gains.
#[derive(Clone, Debug)]
pub struct Prog {
    pub prefix: Vec<(f64, f64, f64)>,
    pub esc: usize,
    pub dir: f64,
    pub bank: f64,
    pub t_pull: f64,
    /// 0: the filter's gains; 1: n ≤ 3.8, α ≤ 0.26, stiffer flight-path loop; 2: n ≤ 6, α ≤ 0.27.
    pub aggr: u8,
    pub v_ref: f64,
}

impl Prog {
    pub fn law(&self) -> Law {
        let base = law_params();
        let mut p = LawP { t_pull_min: [self.t_pull; N_ESC], v_ref: [self.v_ref; N_ESC], keep_bank: true, ..base };
        if self.aggr >= 1 {
            p = LawP { nmax: 3.8, amax: 0.26, kg: 3.5, ..p };
        }
        if self.aggr >= 2 {
            p = LawP { nmax: 6.0, amax: 0.27, kg: 4.5, ..p };
        }
        if self.esc == STREET {
            Law::with(STREET, p)
        } else {
            Law::with_turn(if self.dir == 0.0 { 0 } else { 1 }, p, self.dir, self.bank)
        }
    }
    pub fn text(&self) -> String {
        let pre: Vec<String> = self.prefix.iter().map(|(d, n, ph)| format!("{d:.2}s@{n:.2}g/{:.0}°", -ph.to_degrees())).collect();
        let tail = if self.esc == STREET { "street".to_string() } else if self.dir == 0.0 { "straight".to_string() } else { format!("{}{:.0}°", if self.dir > 0.0 { "R" } else { "L" }, self.bank.to_degrees()) };
        format!("[{}] {tail} pull≥{:.2}s v_ref {:.0}{}", pre.join(" "), self.t_pull, self.v_ref, ["", " aggr", " aggr2"][self.aggr as usize])
    }
}

#[derive(Clone, Debug)]
pub struct Found {
    pub ok: bool,
    pub prog: Option<Prog>,
    pub min_clear: f64,
    pub evals: usize,
    /// Highest load factor of the program found (or of any program tried, if none was found).
    pub nz_max: f64,
}

/// Horizon of the richer search (s): longer than the filter's 16 s.
pub const BEST_HORIZON: f64 = 24.0;

fn grid_progs() -> Vec<Prog> {
    let mut v = Vec::new();
    for aggr in [2u8, 1, 0] {
        for v_ref in [34.0, 40.0] {
            for t_pull in [0.0, 0.75, 1.5, 3.0] {
                v.push(Prog { prefix: vec![], esc: 0, dir: 0.0, bank: 0.0, t_pull, aggr, v_ref });
                for dir in [-1.0, 1.0] {
                    for bank_deg in [15.0, 25.0, 35.0, 45.0, 55.0, 62.0] {
                        v.push(Prog { prefix: vec![], esc: 1, dir, bank: f64::to_radians(bank_deg), t_pull, aggr, v_ref });
                    }
                }
            }
            v.push(Prog { prefix: vec![], esc: STREET, dir: 0.0, bank: 0.7, t_pull: 1.5, aggr, v_ref });
        }
    }
    v
}

/// Score of a failed rollout for the local search: later failures and wider clearance score higher.
fn score(r: &Roll) -> f64 {
    match r.outcome {
        Outcome::Ok => 1e9,
        Outcome::Hit => r.t,
        _ => BEST_HORIZON + r.min_clear.min(30.0) / 30.0,
    }
}

/// Whether some program avoids contact from `s` (positive clearance at every frame, zero-margin terminal sets):
/// the grid first, then `local` local-search iterations from the best grid programs.
pub fn best_found(world: &World, s: &State, local: usize, seed: u64) -> Found {
    let p = JsbPlant::new(s);
    fn cfg(pre: &[(f64, f64, f64)]) -> RollCfg<'_> {
        RollCfg { prefix: pre, horizon: BEST_HORIZON, ..CONTACT }
    }
    let mut evals = 0;
    let mut nz_max: f64 = 0.0;
    let mut scored: Vec<(f64, Prog)> = Vec::new();
    let run = |prog: &Prog, evals: &mut usize, nz_max: &mut f64| -> Roll {
        *evals += 1;
        let r = rollout_cfg(world, &p, prog.law(), usize::MAX, None, &cfg(&prog.prefix));
        *nz_max = nz_max.max(r.nz_max);
        r
    };
    for prog in grid_progs() {
        let r = run(&prog, &mut evals, &mut nz_max);
        if r.ok() {
            return Found { ok: true, prog: Some(prog), min_clear: r.min_clear, evals, nz_max: r.nz_max };
        }
        scored.push((score(&r), prog));
    }
    scored.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
    scored.truncate(6);
    let mut rng = Rng::new(seed ^ 0xB357);
    let mut best = scored.clone();
    for it in 0..local {
        let k = it % best.len();
        let mut q = best[k].1.clone();
        if q.prefix.is_empty() || rng.chance(0.3) {
            let nseg = 1 + (rng.f() * 3.0) as usize;
            q.prefix = (0..nseg).map(|_| (rng.range(0.15, 1.6), rng.range(0.0, 6.0), rng.range(-1.4, 1.4))).collect();
        } else {
            for seg in &mut q.prefix {
                seg.0 = (seg.0 * rng.range(0.7, 1.4)).clamp(0.05, 3.0);
                seg.1 = (seg.1 + rng.range(-0.5, 0.5)).clamp(-0.5, 6.0);
                seg.2 = (seg.2 + rng.range(-0.3, 0.3)).clamp(-1.4, 1.4);
            }
        }
        if rng.chance(0.3) {
            q.bank = (q.bank + rng.range(-0.15, 0.15)).clamp(0.1, 1.1);
            q.t_pull = (q.t_pull + rng.range(-0.5, 0.5)).clamp(0.0, 4.0);
        }
        let r = run(&q, &mut evals, &mut nz_max);
        if r.ok() {
            return Found { ok: true, prog: Some(q), min_clear: r.min_clear, evals, nz_max: r.nz_max };
        }
        let sc = score(&r);
        if sc > best[k].0 {
            best[k] = (sc, q);
        }
    }
    Found { ok: false, prog: None, min_clear: f64::NEG_INFINITY, evals, nz_max }
}

/// Fly a program (no checks) for `secs`: path samples and the minimum airframe clearance.
pub fn fly_prog(world: &World, s: &State, prog: &Prog, secs: f64) -> (Vec<[f64; 3]>, f64) {
    let p = JsbPlant::new(s);
    let r = rollout_cfg(world, &p, prog.law(), (secs / DT_JSB) as usize, None, &RollCfg { margin: f64::NEG_INFINITY, horizon: secs, prefix: &prog.prefix, ..CONTACT });
    (r.path, r.min_clear)
}

// ------------------------------------------------------------------------------------------------ outer bound

/// The optimistic point-mass envelope of the outer bound. Lift is perpendicular to the velocity with magnitude
/// at most `KAPPA qbar g` (the plant's stall, with no structural limit), thrust is along the velocity and at most
/// `A_T` (specific), drag is against it and at most `CD_MAX qbar S / M_MIN`, and there are no other forces
/// besides gravity. Controls act instantly (no pitch or roll transients); the aircraft is a point (no wings).
pub mod env {
    /// 1 / Pa.
    pub const KAPPA: f64 = 0.0036;
    /// Thrust per unit mass (m/s²): an ideal actuator disk of the c172p's 1.9 m propeller at 200 hp gives at
    /// most 5.4 kN static, over the lightest possible mass (empty weight plus pilot, 762 kg): 7.1 m/s².
    pub const A_T: f64 = 7.1;
    /// Drag: coefficient bound and wing area over the lightest mass (m² / kg).
    pub const CD_MAX: f64 = 0.4;
    pub const S_OVER_M: f64 = 16.17 / 762.0;
    pub const RHO: f64 = 1.225;
}

/// What the outer bound proved: time of the certain collision (s) and which test proved it.
#[derive(Clone, Debug)]
pub struct Bound {
    pub t: f64,
    pub test: &'static str,
}

/// Lowest height of the solid (terrain, or a box covering the whole footprint) over the square
/// `[x0,x1]×[y0,y1]`: every point below it is inside the solid. Terrain is piecewise linear on its 20 m grid,
/// so its minimum over the square is at least the lowest grid vertex of every triangle touching it.
fn solid_floor(world: &World, x0: f64, x1: f64, y0: f64, y1: f64) -> f64 {
    let gi = |v: f64| ((v + MAP_HALF) / TSP).floor().clamp(0.0, (TN - 2) as f64) as usize;
    let mut tmin = f64::INFINITY;
    for j in gi(y0)..=gi(y1) + 1 {
        for i in gi(x0)..=gi(x1) + 1 {
            tmin = tmin.min(world.terr[j.min(TN - 1) * TN + i.min(TN - 1)] as f64);
        }
    }
    let mut h = tmin;
    for b in &world.boxes {
        if b.x0 <= x0 && b.x1 >= x1 && b.y0 <= y0 && b.y1 >= y1 && b.z0 <= tmin {
            h = h.max(b.z1);
        }
    }
    h
}

/// Whether every point `p` with `inside(p)` in the bounding box `lo..hi` lies in the solid. Conservative: the
/// box is tiled by `CUBE` cubes; every cube that might meet the set must lie below `solid_floor` of its
/// footprint (`inside` is tested at the cube centre with the cube's half-diagonal as slack).
const CUBE: f64 = 1.5;
fn region_solid(world: &World, lo: [f64; 3], hi: [f64; 3], inside: &dyn Fn([f64; 3], f64) -> bool) -> bool {
    if lo[0] < -MAP_HALF || lo[1] < -MAP_HALF || hi[0] > MAP_HALF || hi[1] > MAP_HALF {
        return false;
    }
    let slack = CUBE * 3f64.sqrt() / 2.0;
    let n = |a: f64, b: f64| ((b - a) / CUBE).ceil().max(1.0) as usize;
    let (nx, ny, nz) = (n(lo[0], hi[0]), n(lo[1], hi[1]), n(lo[2], hi[2]));
    if nx * ny * nz > 4_000_000 {
        return false;
    }
    for i in 0..nx {
        let x = lo[0] + (i as f64 + 0.5) * CUBE;
        for j in 0..ny {
            let y = lo[1] + (j as f64 + 0.5) * CUBE;
            let mut floor = f64::NAN;
            for k in 0..nz {
                let z = lo[2] + (k as f64 + 0.5) * CUBE;
                if !inside([x, y, z], slack) {
                    continue;
                }
                if floor.is_nan() {
                    floor = solid_floor(world, x - CUBE / 2.0, x + CUBE / 2.0, y - CUBE / 2.0, y + CUBE / 2.0);
                }
                if z + CUBE / 2.0 >= floor {
                    return false;
                }
            }
        }
    }
    true
}

/// Sound outer bound: `Some` if no trajectory of the `env` point mass from `s` avoids the solid.
///
/// Along the initial velocity direction `e`, every trajectory's position at time t lies in the tube
/// `p0 + s e + w` with `s ∈ [s_lo, s_hi]`, `w ⊥ e`, `|w| ≤ r_perp`, and below the altitude ceiling `z_hi`:
/// speed stays in `[v_lo, v_hi]` (thrust, drag and gravity along the path), the angle between velocity and
/// `e` grows at most at the turn rate lift and gravity allow at those speeds, and the climb rate grows at
/// most at lift plus thrust minus gravity. Two tests:
/// - tube: at some t the whole tube below the ceiling is inside the solid;
/// - crossing: every trajectory crosses the plane `s = D` by the time `s_lo` reaches D, within `r_perp` of
///   the axis and below the ceiling's maximum so far; if that disk is inside the solid, it crashes there.
pub fn outer_bound(world: &World, s: &State) -> Option<Bound> {
    use env::*;
    let v0 = s[V];
    let (sg, cg) = s[GAM].sin_cos();
    let (sp, cp) = s[PSI].sin_cos();
    let e = [cg * cp, cg * sp, sg];
    let p0 = [s[X], s[Y], s[Z]];
    let dt = 0.01;
    let (mut vlo, mut vhi, mut th, mut slo, mut shi, mut rp) = (v0, v0, 0.0f64, 0.0, 0.0, 0.0);
    let (mut vz, mut z_hi, mut z_max) = (v0 * sg, p0[2], p0[2]);
    let lift = |v: f64| KAPPA * 0.5 * RHO * v * v * G0;
    let mut next_tube = 0.0;
    let mut next_disk = 0.0;
    let mut t = 0.0;
    while t < 8.0 {
        let om = lift(vhi) / vhi.max(1e-3) + G0 / vlo.max(1e-3);
        let a_d = CD_MAX * 0.5 * RHO * vhi * vhi * S_OVER_M;
        th = (th + om * dt).min(PI);
        let c = th.cos();
        slo += if c >= 0.0 { vlo * c } else { vhi * c } * dt;
        shi += vhi * dt;
        rp += vhi * th.min(PI / 2.0).sin() * dt;
        vz += (lift(vhi) + A_T - G0) * dt;
        vz = vz.min(vhi);
        z_hi += vz * dt;
        z_max = z_max.max(z_hi);
        vlo = (vlo - (a_d + G0) * dt).max(0.0);
        vhi += (A_T + G0) * dt;
        t += dt;
        if vlo <= 1.0 || th >= PI {
            break;
        }
        let in_tube = |q: [f64; 3], sl: f64, zc: f64, s_a: f64, s_b: f64, r: f64| -> bool {
            if q[2] - sl > zc {
                return false;
            }
            let d = [q[0] - p0[0], q[1] - p0[1], q[2] - p0[2]];
            let along = d[0] * e[0] + d[1] * e[1] + d[2] * e[2];
            if along < s_a - sl || along > s_b + sl {
                return false;
            }
            let perp2 = (d[0] * d[0] + d[1] * d[1] + d[2] * d[2]) - along * along;
            perp2.max(0.0).sqrt() <= r + sl
        };
        let bbox = |s_a: f64, s_b: f64, r: f64, zc: f64| -> ([f64; 3], [f64; 3]) {
            let mut lo = [f64::INFINITY; 3];
            let mut hi = [f64::NEG_INFINITY; 3];
            for sv in [s_a, s_b] {
                for k in 0..3 {
                    let ext = r * (1.0 - e[k] * e[k]).max(0.0).sqrt();
                    let c = p0[k] + sv * e[k];
                    lo[k] = lo[k].min(c - ext);
                    hi[k] = hi[k].max(c + ext);
                }
            }
            hi[2] = hi[2].min(zc);
            (lo, hi)
        };
        if t >= next_tube {
            next_tube = t + 0.05;
            let (lo, hi) = bbox(slo, shi, rp, z_hi);
            if lo[2] <= hi[2] && region_solid(world, lo, hi, &|q, sl| in_tube(q, sl, z_hi, slo, shi, rp)) {
                return Some(Bound { t, test: "tube" });
            }
        }
        if t >= next_disk && slo > 0.0 {
            next_disk = t + 0.05;
            let (lo, hi) = bbox(slo, slo, rp, z_max);
            let thin = |q: [f64; 3], sl: f64| in_tube(q, sl, z_max, slo, slo, rp);
            if lo[2] <= hi[2] && region_solid(world, lo, hi, &thin) {
                return Some(Bound { t, test: "crossing" });
            }
        }
    }
    None
}

// ------------------------------------------------------------------------------------------------ calibration

/// Specific force along and across the velocity, from finite differences of the plant's velocity: for
/// checking the outer bound's envelope against the plant.
pub fn calib() {
    let mut worst = (0.0f64, 0.0f64, 0.0f64, 0.0f64, 0.0f64);
    for v0 in [24.0, 30.0, 36.0, 42.0, 50.0, 58.0, 66.0] {
        for (name, elev, ail, thr) in [("full aft", -1.0, 0.0, 1.0), ("full aft idle", -1.0, 0.0, 0.0), ("aft+roll", -1.0, 0.6, 1.0), ("half aft", -0.5, 0.0, 1.0), ("forward", 0.4, 0.0, 1.0), ("neutral full", 0.0, 0.0, 1.0)] {
            for gam in [-0.5, 0.0, 0.3] {
                let mut p = JsbPlant::new(&trimmed(0.0, 0.0, 800.0, v0, gam, 0.0, 0.6));
                let mut prev = p.obs.vned;
                for k in 0..(4.0 / DT_JSB) as usize {
                    p.frame_raw(elev, ail, 0.0, thr);
                    let o = p.obs;
                    let a = [(o.vned[0] - prev[0]) / DT_JSB, (o.vned[1] - prev[1]) / DT_JSB, (o.vned[2] - prev[2]) / DT_JSB - G0];
                    prev = o.vned;
                    let vv = (o.vned[0].powi(2) + o.vned[1].powi(2) + o.vned[2].powi(2)).sqrt().max(1.0);
                    let along = (a[0] * o.vned[0] + a[1] * o.vned[1] + a[2] * o.vned[2]) / vv;
                    let perp = ((a[0] * a[0] + a[1] * a[1] + a[2] * a[2]) - along * along).max(0.0).sqrt();
                    let q = o.qbar.max(1.0);
                    if perp / G0 / q > worst.0 && std::env::var("CALIB_V").is_ok() {
                        println!("  new max perp/(g q) {:.5} at v0 {v0} {name} gam {gam} t {:.3} V {:.1} alpha {:.3} nz {:.2} q {:.0}", perp / G0 / q, k as f64 * DT_JSB, o.vt, o.alpha, o.nz, q);
                    }
                    worst.0 = worst.0.max(perp / G0 / q);
                    worst.1 = worst.1.max(perp / G0);
                    worst.2 = worst.2.max(along);
                    worst.3 = worst.3.max(-along / (q * env::S_OVER_M));
                    worst.4 = worst.4.max(o.nz / q);
                }
                let _ = name;
            }
        }
    }
    println!("plant maxima over the calibration manoeuvres:");
    println!("  perpendicular specific force / (g qbar): {:.5} 1/Pa (bound KAPPA {:.5}); nz/qbar {:.5}", worst.0, env::KAPPA, worst.4);
    println!("  perpendicular specific force: {:.2} g (no load-factor cap in the bound)", worst.1);
    println!("  along-path thrust minus drag: {:.2} m/s² (bound A_T {:.1})", worst.2, env::A_T);
    println!("  along-path deceleration / (qbar S/m): {:.3} (bound CD_MAX {:.2})", worst.3, env::CD_MAX);
}

// ------------------------------------------------------------------------------------------------ slices

/// A one-dimensional slice through the state space: `make(world, d)` is the state at parameter `d`; larger
/// `d` is farther from the obstacle (safer).
pub struct SliceDef {
    pub key: &'static str,
    pub title: &'static str,
    pub param: &'static str,
    pub unit: &'static str,
    pub lo: f64,
    pub hi: f64,
    pub n: usize,
    pub tol: f64,
    pub make: fn(&World, f64) -> State,
    /// Seconds of pilot lead-in for the demo of the proven-safe call (the start moved back along the velocity).
    pub lead: f64,
    /// The displayed parameter is `-d` (for slices where a larger displayed value is less safe, e.g. speed).
    pub flip: bool,
    /// GUI camera flags for the demos.
    pub cam: &'static str,
}

impl SliceDef {
    pub fn show(&self, d: f64) -> f64 {
        if self.flip { -d } else { d }
    }
}

#[derive(Clone, Debug)]
pub struct Point {
    pub d: f64,
    /// The gate's own acceptance (its 4 m margin), the gate's escapes at contact, the richer search, the bound.
    pub gate: Verdict,
    pub lib: Verdict,
    pub best: Found,
    pub bound: Option<Bound>,
}

/// The markers: gate acceptance, proven safe (gate escapes at contact), best found, proven unsafe.
#[derive(Clone, Debug, Default)]
pub struct Markers {
    pub gate: Option<f64>,
    pub safe: Option<f64>,
    pub best: Option<f64>,
    pub unsafe_: Option<f64>,
    pub best_prog: Option<String>,
    /// Highest load factor of any program found on the slice.
    pub nz_max: f64,
}

pub const LOCAL_ITERS: usize = 160;

/// Best found, counting the gate's own escapes at contact as part of the search family.
fn best_or_lib(world: &World, s: &State, lib_ok: bool, d: f64) -> Found {
    if lib_ok {
        return Found { ok: true, prog: None, min_clear: f64::NAN, evals: 0, nz_max: 0.0 };
    }
    best_found(world, s, LOCAL_ITERS, (d * 1000.0) as u64)
}

pub fn eval_point(world: &World, def: &SliceDef, d: f64) -> Point {
    let s = (def.make)(world, d);
    let gate = gate_verdict(world, &s);
    let lib = contact_verdict(world, &s);
    let best = best_or_lib(world, &s, lib.ok, d);
    let bound = outer_bound(world, &s);
    Point { d, gate, lib, best, bound }
}

/// Smallest grid `d` where `pred` holds, refined by bisection against the grid point below it to `tol`.
fn closest_true(grid: &[(f64, bool)], tol: f64, pred: &dyn Fn(f64) -> bool) -> Option<f64> {
    let k = grid.iter().position(|g| g.1)?;
    if k == 0 {
        return Some(grid[0].0);
    }
    let (mut bad, mut good) = (grid[k - 1].0, grid[k].0);
    while good - bad > tol {
        let m = 0.5 * (bad + good);
        if pred(m) { good = m } else { bad = m }
    }
    Some(good)
}

/// Largest grid `d` where `pred` holds, refined by bisection against the grid point above it to `tol`.
fn farthest_true(grid: &[(f64, bool)], tol: f64, pred: &dyn Fn(f64) -> bool) -> Option<f64> {
    let k = grid.iter().rposition(|g| g.1)?;
    if k + 1 == grid.len() {
        return Some(grid[k].0);
    }
    let (mut good, mut bad) = (grid[k].0, grid[k + 1].0);
    while bad - good > tol {
        let m = 0.5 * (bad + good);
        if pred(m) { good = m } else { bad = m }
    }
    Some(good)
}

pub fn grid_ds(def: &SliceDef) -> Vec<f64> {
    (0..def.n).map(|i| def.lo + (def.hi - def.lo) * i as f64 / (def.n - 1) as f64).collect()
}

pub fn markers(world: &World, def: &SliceDef, pts: &[Point], threads: usize) -> Markers {
    let g = |f: &dyn Fn(&Point) -> bool| -> Vec<(f64, bool)> { pts.iter().map(|p| (p.d, f(p))).collect() };
    let (gg, gl, gb, gu) = (g(&|p| p.gate.ok), g(&|p| p.lib.ok), g(&|p| p.best.ok), g(&|p| p.bound.is_some()));
    let tol = def.tol;
    let mk = |d: f64| (def.make)(world, d);
    let res: Vec<Option<f64>> = crate::harness::par_map(
        (0..4).collect::<Vec<usize>>(),
        threads.min(4),
        |&k| match k {
            0 => closest_true(&gg, tol, &|d| gate_verdict(world, &mk(d)).ok),
            1 => closest_true(&gl, tol, &|d| contact_verdict(world, &mk(d)).ok),
            2 => closest_true(&gb, tol, &|d| {
                let s = mk(d);
                best_or_lib(world, &s, contact_verdict(world, &s).ok, d).ok
            }),
            _ => farthest_true(&gu, tol, &|d| outer_bound(world, &mk(d)).is_some()),
        },
        |_, _| {},
    );
    let best_prog = res[2].map(|d| {
        let s = mk(d);
        if contact_verdict(world, &s).ok { "one of the gate's own escapes".to_string() } else { best_found(world, &s, LOCAL_ITERS, (d * 1000.0) as u64).prog.map_or("-".into(), |p| p.text()) }
    });
    Markers {
        gate: res[0],
        safe: res[1],
        best: res[2],
        unsafe_: res[3],
        best_prog,
        nz_max: pts.iter().filter(|p| p.best.ok && p.best.prog.is_some()).map(|p| p.best.nz_max).fold(0.0, f64::max),
    }
}

// ------------------------------------------------------------------------------------------------ demos

/// `s` moved back along its velocity by `lead` seconds of flight (the pilot's lead-in to the slice state).
pub fn lead_state(s: &State, lead: f64) -> State {
    let mut q = *s;
    let (sg, cg) = s[GAM].sin_cos();
    q[X] -= s[V] * lead * cg * s[PSI].cos();
    q[Y] -= s[V] * lead * cg * s[PSI].sin();
    q[Z] -= s[V] * lead * sg;
    q
}

/// A start as the GUI's `--start` flag spells it: `x,y,z,v,gamma°,heading°,bank°,throttle` (point-mass
/// conventions: heading counter-clockwise from east, bank positive left wing down).
pub fn start_arg(s: &State) -> String {
    format!("{:.2},{:.2},{:.2},{:.2},{:.3},{:.3},{:.3},{:.2}", s[X], s[Y], s[Z], s[V], s[GAM].to_degrees(), s[PSI].to_degrees(), s[PHI].to_degrees(), s[THR])
}

pub fn parse_start(a: &str) -> Option<State> {
    let v: Vec<f64> = a.split(',').filter_map(|x| x.trim().parse().ok()).collect();
    if v.len() != 8 {
        return None;
    }
    let (gam, psi, phi) = (v[4].to_radians(), v[5].to_radians(), v[6].to_radians());
    Some([v[0], v[1], v[2], v[3], gam, psi, phi, 0.0, gam.cos() / phi.cos().max(0.3), v[7]])
}

#[derive(Clone, Debug, Default)]
pub struct DemoRun {
    pub crashed: bool,
    pub t_end: f64,
    pub min_clear: f64,
    pub t_min: f64,
    pub first_commit: Option<f64>,
    pub release: Option<f64>,
    pub commit_ticks: u64,
    pub ticks: u64,
    pub first_accept: bool,
    /// Lowest clearance within 8 s of the first takeover (the save itself), and when.
    pub save_min: f64,
    pub t_save_min: f64,
    pub commit_runs: u32,
}

/// Fly the GUI's demo headless: the manual pilot with the sticks released (fly-by-wire holds flight path and
/// bank), gate filter on or off, for `secs`. Needs `JSB_PLANT` and `ENV_FILTER = gate` set.
pub fn demo_run(world: &World, s0: &State, filter_on: bool, secs: f64) -> DemoRun {
    use crate::filter::Mode;
    use crate::pilot::Fbw;
    use crate::sim::{Sim, SimCfg};
    let mut sim = Sim::new(world, *s0, SimCfg { filter_on, ..SimCfg::default() });
    let mut fbw = Fbw::from_state(&sim.s);
    let mut r = DemoRun { min_clear: sim.true_clear, save_min: f64::INFINITY, ..Default::default() };
    let mut was = Mode::Free;
    for _ in 0..(secs / DT_F).round() as usize {
        fbw.sticks(0.0, 0.0, DT_F);
        let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
        sim.tick(u);
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        let t = sim.time();
        if sim.true_clear < r.min_clear {
            r.min_clear = sim.true_clear;
            r.t_min = t;
        }
        if sim.fs.mode == Mode::Commit && was != Mode::Commit {
            r.commit_runs += 1;
            if r.first_commit.is_none() {
                r.first_commit = Some(t);
            }
        }
        if r.first_commit.is_some_and(|t0| t <= t0 + 8.0) && sim.true_clear < r.save_min {
            r.save_min = sim.true_clear;
            r.t_save_min = t;
        }
        if sim.fs.mode != Mode::Commit && was == Mode::Commit && r.release.is_none() {
            r.release = Some(t);
        }
        was = sim.fs.mode;
        r.t_end = t;
        if sim.crashed {
            r.crashed = true;
            break;
        }
    }
    r.commit_ticks = sim.commit_ticks;
    r.ticks = sim.ticks;
    r.first_accept = sim.env_gate.as_ref().and_then(|g| g.first_accept).unwrap_or(false);
    r
}

// ------------------------------------------------------------------------------------------------ in the wild

pub const REGIMES: [&str; 5] = ["01-terrain-roof-below", "02-wall-beside", "03-canyon", "04-wall-ahead", "05-rising-terrain"];

/// The regime of a takeover, from the cause of the escape that got farthest (latest failure): index into
/// `REGIMES`, or `None` when an escape verified (the filter fell back for lack of budget, not geometry).
pub fn regime_of(v: &Verdict) -> Option<usize> {
    let e = v.per_esc.iter().filter(|e| e.cause != Cause::NoStreet).max_by(|a, b| a.t.partial_cmp(&b.t).unwrap())?;
    match e.cause {
        Cause::HitGround | Cause::HitRoof => Some(0),
        Cause::HitWallSide => Some(1),
        Cause::TermRayBuilding | Cause::TermHelix | Cause::TermUnsettled | Cause::TermNotTurning => Some(2),
        Cause::HitWallAhead => Some(3),
        Cause::HitTerrainAhead | Cause::TermRayTerrain => Some(4),
        Cause::Ok | Cause::NoStreet => None,
    }
}

#[derive(Clone, Debug)]
pub struct WildEvent {
    pub episode: u64,
    pub t: f64,
    pub regime: Option<usize>,
    pub cause: Cause,
    pub v: f64,
    /// Lowest airframe clearance from the commit until the pilot is accepted again (m).
    pub min_clear: f64,
    pub crashed: bool,
}

/// The harness's hostile-pilot episode `e` (random start, every fourth a kamikaze pilot) under the gate filter:
/// each commit run, classified by the binding cause from the state where the filter rejected the pilot.
pub fn wild_episode(world: &World, e: u64, secs: f64) -> Vec<WildEvent> {
    use crate::filter::Mode;
    use crate::pilot::{Fbw, Hostile, Kamikaze};
    use crate::sim::{random_start, Sim, SimCfg};
    let mut rng = Rng::new(e.wrapping_mul(7919) ^ 0xE915);
    let s0 = random_start(world, &mut rng);
    let kami = e % 4 == 3;
    let mut sim = Sim::new(world, s0, SimCfg { seed: e, ..SimCfg::default() });
    let mut fbw = Fbw::from_state(&s0);
    let mut hostile = Hostile::new(e);
    let mut kk = Kamikaze::new(e);
    let mut out: Vec<WildEvent> = Vec::new();
    let mut was = Mode::Free;
    for _ in 0..(secs / DT_F).round() as usize {
        if kami {
            kk.update(world, &sim.s, &mut fbw, DT_F);
        } else {
            hostile.update(&mut fbw, DT_F);
        }
        let u = fbw.cmd(&sim.prm_ctrl, &sim.s);
        let pre = sim.jsb.as_ref().map(|p| {
            let mut c = p.fork();
            c.advance(&u, DT_F);
            c
        });
        sim.tick(u);
        fbw.resync(&sim.s, sim.fs.lam, DT_F);
        if sim.fs.mode == Mode::Commit {
            if was != Mode::Commit {
                if let Some(c) = pre {
                    let v = filter_verdict_plant(world, &c);
                    let st = c.state();
                    let reg = regime_of(&v);
                    let cause = v.per_esc.iter().filter(|x| x.cause != Cause::NoStreet).max_by(|a, b| a.t.partial_cmp(&b.t).unwrap()).map_or(Cause::Ok, |x| x.cause);
                    out.push(WildEvent { episode: e, t: sim.time(), regime: reg, cause, v: st[V], min_clear: sim.true_clear, crashed: false });
                }
            } else if let Some(ev) = out.last_mut() {
                ev.min_clear = ev.min_clear.min(sim.true_clear);
            }
        }
        was = sim.fs.mode;
        if sim.crashed {
            if let Some(ev) = out.last_mut() {
                ev.crashed = true;
            }
            break;
        }
    }
    out
}
