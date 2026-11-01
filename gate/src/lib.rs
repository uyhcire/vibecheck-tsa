//! The gatekeeper filter (`cityflight::envfilter::Gate`) for a host that runs JSBSim itself; C ABI in `capi`.

pub mod capi;

use cityflight::envfilter::{Gate, BUDGET, ESCAPES, TIME_CAP_MS};
use cityflight::jsb::{JsbPlant, MapFrame, Pilot, DT_JSB};
use cityflight::model::{X, Y, Z};
use cityflight::world::{World, MAP_HALF};
use std::sync::atomic::Ordering;

pub const MAX_TICK_FRAMES: usize = 16;
pub const DEFAULT_TICK_FRAMES: usize = 3;
pub const DEFAULT_SEED: u64 = 1337;

#[derive(Clone, Copy, Debug)]
pub enum PilotKind {
    Surfaces,
    Fbw,
}

#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub seed: u64,
    pub origin: [f64; 3],
    pub pilot: PilotKind,
    pub tick_frames: usize,
    pub budget_frames: Option<usize>,
    pub time_cap_ms: Option<u32>,
    /// The host's JSBSim burns fuel (`propulsion/fuel_freeze` 0). Default false: the host sets it to 1, which is the
    /// plant the safety theorem is about, and imported states roll out with it.
    pub fuel_drain: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            seed: DEFAULT_SEED,
            origin: [0.0; 3],
            pilot: PilotKind::Surfaces,
            tick_frames: DEFAULT_TICK_FRAMES,
            budget_frames: None,
            time_cap_ms: None,
            fuel_drain: false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Tick {
    pub accept: bool,
    pub escape: Option<usize>,
    pub verified: bool,
    /// Elevator, aileron, rudder, throttle for each frame of the tick.
    pub surfaces: Vec<[f64; 4]>,
    /// The escape's verified path (map metres).
    pub path: Vec<[f64; 3]>,
    pub check_frames: u32,
    pub cpu_ms: f64,
    pub wall_ms: f64,
    pub map_pos: [f64; 3],
    pub clearance: f64,
    pub replay_exact: bool,
}

pub struct Filter {
    pub world: World,
    pub cfg: Config,
    frame: MapFrame,
    gate: Option<Gate>,
    prev: Option<JsbPlant>,
}

impl Filter {
    pub fn new(cfg: Config) -> Filter {
        if let Some(b) = cfg.budget_frames {
            BUDGET.store(b, Ordering::Relaxed);
        }
        if let Some(ms) = cfg.time_cap_ms {
            TIME_CAP_MS.store(ms, Ordering::Relaxed);
        }
        Filter {
            world: World::new(cfg.seed),
            frame: MapFrame::new(cfg.origin[0], cfg.origin[1], cfg.origin[2]),
            cfg,
            gate: None,
            prev: None,
        }
    }

    /// Move the map origin (and start a new flight); the map itself stays.
    pub fn set_origin(&mut self, lat_deg: f64, lon_deg: f64, alt0: f64) {
        self.cfg.origin = [lat_deg, lon_deg, alt0];
        self.frame = MapFrame::new(lat_deg, lon_deg, alt0);
        self.reset();
    }

    pub fn reset(&mut self) {
        self.gate = None;
        self.prev = None;
    }

    /// Latitude, longitude (degrees) and altitude (m) of a map point.
    pub fn map_to_geodetic(&self, x: f64, y: f64, z: f64) -> [f64; 3] {
        self.frame.geodetic(x, y, z)
    }

    pub fn import_len(&self) -> usize {
        cityflight::jsb::dump_len()
    }

    pub fn import(&self, dump: &[f64]) -> Option<JsbPlant> {
        JsbPlant::from_dump_ff(dump, self.frame, !self.cfg.fuel_drain)
    }

    pub fn tick(&mut self, mut plant: JsbPlant, pilot: Pilot) -> Tick {
        if let (Some(prev), Pilot::Fbw(_)) = (&self.prev, &pilot) {
            plant.carry_fbw(prev);
        }
        plant.lag = 0.0;
        let pre = plant.fork();
        let world = &self.world;
        let gate = self.gate.get_or_insert_with(|| Gate::new(world, &plant));
        let blind_pre = gate.blind_ticks;
        let n = self.cfg.tick_frames;
        let accept = gate.tick_pilot(world, &mut plant, &pilot, n as f64 * DT_JSB, true);
        // Per-frame surfaces as the gate applied them; replaying them on the state before the tick must
        // reproduce the gate's aircraft exactly.
        let surfaces = gate.tick_surfaces.clone();
        let mut q = pre.fork();
        for s in &surfaces {
            q.frame_raw(s[0], s[1], s[2], s[3]);
        }
        let replay_exact = surfaces.len() == n && q.obs.ecef == plant.obs.ecef && q.obs.vned == plant.obs.vned && q.obs.pqr == plant.obs.pqr;
        let escape = if accept { gate.witness } else { gate.law }.map(|l| l.esc);
        let path = if accept { gate.witness_path.clone() } else { gate.committed_path.clone() };
        let s = pre.state();
        let out = Tick {
            accept,
            escape,
            verified: accept || gate.blind_ticks == blind_pre,
            surfaces,
            path,
            check_frames: *gate.frames.last().unwrap_or(&0),
            cpu_ms: *gate.cpu_ms.last().unwrap_or(&0.0) as f64,
            wall_ms: *gate.wall_ms.last().unwrap_or(&0.0) as f64,
            map_pos: [s[X], s[Y], s[Z]],
            clearance: if s[X].abs() < MAP_HALF && s[Y].abs() < MAP_HALF { world.airframe_clearance(&s, 200.0) } else { f64::INFINITY },
            replay_exact,
        };
        self.prev = Some(plant);
        out
    }
}

pub fn escape_name(i: usize) -> Option<&'static str> {
    ESCAPES.get(i).map(|e| e.name)
}
