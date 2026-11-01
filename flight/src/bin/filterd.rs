//! Headless bridge: the fly-by-wire pilot and the backup-CBF filter as a line protocol, so an
//! external plant (JSBSim in `sidecar/`) can be guarded. One line in per filter tick, one line out.
//!
//! in : x y z v gam psi phi p n thr   pitch roll throttle   on [kamikaze]   (model State, sticks in -1..1 / 0..1, flags 0|1)
//!      kamikaze = 1 ignores the sticks and flies the crate's kamikaze autopilot at the nearest tall building.
//! out: nc pc thrc  mode lam h inv_ok clear                           (command to apply, Mode 0..3, barrier, true clearance m)
//!
//! usage: filterd [--map sf|grid] [--nominal] [--pmax DEG] [--nmax G] [--tau-n S] [--tau-p S] [--tau-thr S] [--t-static N] [--power W]
//!        (default: San Francisco, Phase 3 robust margins; the overrides make the predictor model a weaker aircraft)
//!        field 16 of the input line = hostile: the crate's random nose-down pilot replaces the sticks (tests).
use cityflight::escape::{esc_law, Pred};
use cityflight::filter::{CmdSrc, FilterCfg, FilterState, Mode, Phase};
use cityflight::model::*;
use cityflight::pilot::{Fbw, Hostile, Kamikaze};
use cityflight::world::{MapId, World};
use std::io::{self, BufRead, Write};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let map = args.iter().position(|a| a == "--map").and_then(|i| args.get(i + 1)).map(|s| s.as_str()).unwrap_or("sf");
    let map = MapId::parse(map).expect("--map sf|grid");
    let robust = !args.iter().any(|a| a == "--nominal");
    let world = World::load(map);
    let cfg = FilterCfg { phase: Phase::P1, robust };
    let mut prm = if robust { Params::mismatch() } else { Params::nominal() };
    let arg = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).and_then(|v| v.parse::<f64>().ok());
    if let Some(v) = arg("--pmax") { prm.p_max = v.to_radians(); }
    if let Some(v) = arg("--nmax") { prm.n_max = v; }
    if let Some(v) = arg("--tau-n") { prm.tau_n = v; }
    if let Some(v) = arg("--tau-p") { prm.tau_p = v; }
    if let Some(v) = arg("--tau-thr") { prm.tau_thr = v; }
    if let Some(v) = arg("--t-static") { prm.t_static = v; }
    if let Some(v) = arg("--power") { prm.power = v; }
    let pred = Pred { world: &world, prm, wind: [0.0; 3], robust, swept: true, accept: true, gust: 0.0, gust_z: 0.0 };
    let mut fs = FilterState::new(cfg);
    let mut fbw: Option<Fbw> = None;
    let mut on = false;
    let mut kami: Option<Kamikaze> = None;
    let mut hostile: Option<Hostile> = None;
    let mut k: u64 = 0;
    let stdin = io::stdin();
    let mut out = io::stdout().lock();
    eprintln!("filterd ready: map {:?}, robust {}, predictor p_max {:.0} deg/s n_max {} tau_n {} tau_p {} t_static {} power {}",
              map, robust, prm.p_max.to_degrees(), prm.n_max, prm.tau_n, prm.tau_p, prm.t_static, prm.power);
    for line in stdin.lock().lines() {
        let f: Vec<f64> = line.unwrap().split_whitespace().filter_map(|t| t.parse().ok()).collect();
        if f.len() < 14 {
            continue;
        }
        let s: State = [f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7], f[8], f[9]];
        let want_on = f[13] > 0.5;
        let fbw = fbw.get_or_insert_with(|| Fbw::from_state(&s));
        if f.get(14).map_or(false, |&v| v > 0.5) {
            kami.get_or_insert_with(|| Kamikaze::new(7)).update(&world, &s, fbw, DT_F);
        } else if f.get(15).map_or(false, |&v| v > 0.5) {
            hostile.get_or_insert_with(|| Hostile::new(11)).update(fbw, DT_F);
        } else {
            kami = None;
            fbw.thr = f[12];
            fbw.sticks(f[10], f[11], DT_F);
        }
        let u_p = fbw.cmd(&prm, &s);
        if want_on != on {
            on = want_on;
            fs = FilterState::new(cfg);
            if on && !fs.init(&pred, &s, k) {
                eprintln!("filter on: state outside the safe set, flying best escape");
            }
        }
        let src = if on {
            fs.tick(&pred, &s, k, u_p)
        } else {
            fs.mode = Mode::Off;
            fs.lam = 0.0;
            CmdSrc::Const(u_p)
        };
        let applied = match src {
            CmdSrc::Const(u) => u,
            CmdSrc::FollowPlan => match fs.plan {
                Some(pl) if k < pl.hold_end => pl.hold,
                Some(pl) => {
                    let e = pl.eref.unwrap_or_else(|| pred.esc_ref(&s, pl.esc));
                    esc_law(&prm, &s, pl.esc, (k - pl.hold_end) as f64 * DT, &e, &[0.0; 3]).cmd
                }
                None => u_p,
            },
        };
        fbw.resync(&s, fs.lam, DT_F);
        k += STEPS_PER_TICK;
        let mode = match fs.mode { Mode::Off => 0, Mode::Free => 1, Mode::Blend => 2, Mode::Commit => 3 };
        let clear = world.true_clearance([s[X], s[Y], s[Z]]);
        writeln!(out, "{:.4} {:.4} {:.3} {} {:.3} {:.1} {} {:.1}", applied[0], applied[1], applied[2], mode, fs.lam, fs.h, fs.inv_ok as u8, clear).unwrap();
        out.flush().unwrap();
    }
}
