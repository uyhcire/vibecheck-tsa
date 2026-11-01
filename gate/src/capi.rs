//! C ABI (`gate.h`).

use crate::{Config, Filter, PilotKind, Tick, DEFAULT_SEED, DEFAULT_TICK_FRAMES, MAX_TICK_FRAMES};
use cityflight::jsb::{dump_len, Pilot};
use std::ffi::{c_char, c_int};
use std::panic::{catch_unwind, AssertUnwindSafe};

pub const GATE_ABI_VERSION: u32 = 1;
pub const GATE_OK: c_int = 0;
pub const GATE_ERR_VERSION: c_int = -1;
pub const GATE_ERR_BAD_CONFIG: c_int = -2;
pub const GATE_ERR_BAD_STATE: c_int = -3;
pub const GATE_ERR_BAD_INPUT: c_int = -4;
pub const GATE_ERR_UNSUPPORTED: c_int = -5;
pub const GATE_ERR_INTERNAL: c_int = -6;
pub const GATE_PILOT_SURFACES: u32 = 1;
pub const GATE_PILOT_FBW: u32 = 2;
pub const GATE_MODE_ERROR: i32 = -1;
pub const GATE_MODE_PILOT: i32 = 0;
pub const GATE_MODE_ESCAPE: i32 = 1;

#[repr(C)]
pub struct GateConfig {
    pub abi_version: u32,
    pub size: u32,
    pub map_seed: u64,
    pub map_path: *const c_char,
    pub origin_lat_deg: f64,
    pub origin_lon_deg: f64,
    pub origin_alt_m: f64,
    pub pilot_kind: u32,
    pub tick_frames: u32,
    pub budget_frames: u32,
    pub time_cap_ms: u32,
    /// Appended after the first release: absent (0) in a shorter `size`.
    pub fuel_drain: u32,
}

/// Bytes of `gate_config` in the first release (before `fuel_drain`); the smallest accepted `size`.
const CONFIG_V1_SIZE: usize = std::mem::offset_of!(GateConfig, fuel_drain);

/// The config at `p`, with the fields beyond its `size` zeroed, so an older, shorter `gate_config` is accepted.
///
/// Safety: `p` points to at least `size` bytes, the `size` it states.
unsafe fn read_config(p: *const GateConfig) -> Result<GateConfig, c_int> {
    let head = p as *const u32;
    let (abi, size) = (head.read_unaligned(), head.add(1).read_unaligned() as usize);
    if abi != GATE_ABI_VERSION || size < CONFIG_V1_SIZE {
        return Err(GATE_ERR_VERSION);
    }
    let mut c: GateConfig = std::mem::zeroed();
    std::ptr::copy_nonoverlapping(p as *const u8, &mut c as *mut GateConfig as *mut u8, size.min(std::mem::size_of::<GateConfig>()));
    Ok(c)
}

#[repr(C)]
pub struct GatePilot {
    pub abi_version: u32,
    pub size: u32,
    pub kind: u32,
    pub reserved: u32,
    pub elevator: f64,
    pub aileron: f64,
    pub rudder: f64,
    pub throttle: f64,
    pub nz: f64,
    pub roll_rate: f64,
}

#[repr(C)]
pub struct GateResult {
    pub abi_version: u32,
    pub size: u32,
    pub mode: i32,
    pub escape: i32,
    pub verified: u32,
    pub frames: u32,
    pub surfaces: [[f64; 4]; MAX_TICK_FRAMES],
    pub path: *const f64,
    pub path_len: u32,
    pub check_frames: u32,
    pub cpu_ms: f64,
    pub wall_ms: f64,
    pub map_pos: [f64; 3],
    pub clearance: f64,
}

pub struct Gate {
    filter: Filter,
    path: Vec<f64>,
}

fn guard<T>(fallback: T, f: impl FnOnce() -> T) -> T {
    catch_unwind(AssertUnwindSafe(f)).unwrap_or(fallback)
}

fn config(c: &GateConfig) -> Result<Config, c_int> {
    if !c.map_path.is_null() {
        return Err(GATE_ERR_UNSUPPORTED);
    }
    let pilot = match c.pilot_kind {
        GATE_PILOT_SURFACES => PilotKind::Surfaces,
        GATE_PILOT_FBW => PilotKind::Fbw,
        _ => return Err(GATE_ERR_BAD_CONFIG),
    };
    let tick_frames = if c.tick_frames == 0 { DEFAULT_TICK_FRAMES } else { c.tick_frames as usize };
    let origin = [c.origin_lat_deg, c.origin_lon_deg, c.origin_alt_m];
    if tick_frames > MAX_TICK_FRAMES || origin.iter().any(|x| !x.is_finite()) || origin[0].abs() > 89.0 {
        return Err(GATE_ERR_BAD_CONFIG);
    }
    Ok(Config {
        seed: if c.map_seed == 0 { DEFAULT_SEED } else { c.map_seed },
        origin,
        pilot,
        tick_frames,
        budget_frames: (c.budget_frames > 0).then_some(c.budget_frames as usize),
        time_cap_ms: (c.time_cap_ms > 0).then_some(c.time_cap_ms),
        fuel_drain: c.fuel_drain != 0,
    })
}

fn pilot(p: &GatePilot, kind: PilotKind) -> Result<Pilot, c_int> {
    if p.abi_version != GATE_ABI_VERSION || (p.size as usize) < std::mem::size_of::<GatePilot>() {
        return Err(GATE_ERR_VERSION);
    }
    let unit = |x: f64| (-1.0..=1.0).contains(&x);
    let thr_ok = (0.0..=1.0).contains(&p.throttle);
    match (kind, p.kind) {
        (PilotKind::Surfaces, GATE_PILOT_SURFACES) if unit(p.elevator) && unit(p.aileron) && unit(p.rudder) && thr_ok => {
            Ok(Pilot::Surfaces([p.elevator, p.aileron, p.rudder, p.throttle]))
        }
        (PilotKind::Fbw, GATE_PILOT_FBW) if p.nz.is_finite() && p.roll_rate.is_finite() && thr_ok => {
            Ok(Pilot::Fbw([p.nz, p.roll_rate, p.throttle]))
        }
        _ => Err(GATE_ERR_BAD_INPUT),
    }
}

fn blank(out: &mut GateResult) {
    // SAFETY: GateResult is plain old data; all-zero is a valid value (null path).
    *out = unsafe { std::mem::zeroed() };
    out.abi_version = GATE_ABI_VERSION;
    out.size = std::mem::size_of::<GateResult>() as u32;
    out.mode = GATE_MODE_ERROR;
    out.escape = -1;
}

fn fill(out: &mut GateResult, t: &Tick, path: &mut Vec<f64>) {
    out.mode = if t.accept { GATE_MODE_PILOT } else { GATE_MODE_ESCAPE };
    out.escape = t.escape.map_or(-1, |e| e as i32);
    out.verified = t.verified as u32;
    out.frames = t.surfaces.len() as u32;
    for (row, s) in out.surfaces.iter_mut().zip(&t.surfaces) {
        *row = *s;
    }
    path.clear();
    path.extend(t.path.iter().flatten());
    out.path = if path.is_empty() { std::ptr::null() } else { path.as_ptr() };
    out.path_len = t.path.len() as u32;
    out.check_frames = t.check_frames;
    out.cpu_ms = t.cpu_ms;
    out.wall_ms = t.wall_ms;
    out.map_pos = t.map_pos;
    out.clearance = t.clearance;
}

/// Safety: `cfg` must point to a `gate_config`; `err` may be null.
#[no_mangle]
pub unsafe extern "C" fn gate_new(cfg: *const GateConfig, err: *mut c_int) -> *mut Gate {
    let (g, e) = guard((std::ptr::null_mut(), GATE_ERR_INTERNAL), || match (!cfg.is_null()).then(|| read_config(cfg).and_then(|c| config(&c))) {
        None => (std::ptr::null_mut(), GATE_ERR_BAD_CONFIG),
        Some(Err(e)) => (std::ptr::null_mut(), e),
        Some(Ok(c)) => (Box::into_raw(Box::new(Gate { filter: Filter::new(c), path: Vec::new() })), GATE_OK),
    });
    if let Some(e2) = err.as_mut() {
        *e2 = e;
    }
    g
}

/// Safety: `g` from `gate_new`; `dump` points to `n` doubles; `pilot` and `out` to their structs.
#[no_mangle]
pub unsafe extern "C" fn gate_tick(g: *mut Gate, dump: *const f64, n: usize, pilot_in: *const GatePilot, out: *mut GateResult) -> c_int {
    let Some(out) = out.as_mut() else { return GATE_ERR_BAD_INPUT };
    blank(out);
    let (Some(g), Some(p)) = (g.as_mut(), pilot_in.as_ref()) else { return GATE_ERR_BAD_INPUT };
    if dump.is_null() || n != dump_len() {
        return GATE_ERR_BAD_STATE;
    }
    let dump = std::slice::from_raw_parts(dump, n);
    guard(GATE_ERR_INTERNAL, || {
        let pilot = match pilot(p, g.filter.cfg.pilot) {
            Ok(p) => p,
            Err(e) => return e,
        };
        let Some(plant) = g.filter.import(dump) else { return GATE_ERR_BAD_STATE };
        let t = g.filter.tick(plant, pilot);
        fill(out, &t, &mut g.path);
        GATE_OK
    })
}

/// Safety: `g` from `gate_new` or null.
#[no_mangle]
pub unsafe extern "C" fn gate_reset(g: *mut Gate) {
    if let Some(g) = g.as_mut() {
        g.filter.reset();
    }
}

/// Safety: `g` from `gate_new` or null; not used afterwards.
#[no_mangle]
pub unsafe extern "C" fn gate_free(g: *mut Gate) {
    if !g.is_null() {
        drop(Box::from_raw(g));
    }
}

#[no_mangle]
pub extern "C" fn gate_dump_len() -> usize {
    dump_len()
}

#[no_mangle]
pub extern "C" fn gate_escape_name(escape: i32) -> *const c_char {
    const NAMES: [&[u8]; 6] = [b"straight\0", b"left\0", b"right\0", b"left40\0", b"right40\0", b"street\0"];
    let name: &[u8] = usize::try_from(escape).ok().and_then(|i| NAMES.get(i).copied()).unwrap_or(b"none\0");
    debug_assert!(usize::try_from(escape).map_or(true, |i| crate::escape_name(i).map_or(true, |n| n.as_bytes() == &name[..name.len() - 1])));
    name.as_ptr() as *const c_char
}

/// Safety: `g` from `gate_new`; the outputs point to doubles.
#[no_mangle]
pub unsafe extern "C" fn gate_map_to_geodetic(g: *const Gate, x: f64, y: f64, z: f64, lat_deg: *mut f64, lon_deg: *mut f64, alt_m: *mut f64) -> c_int {
    let (Some(g), Some(lat), Some(lon), Some(alt)) = (g.as_ref(), lat_deg.as_mut(), lon_deg.as_mut(), alt_m.as_mut()) else {
        return GATE_ERR_BAD_INPUT;
    };
    [*lat, *lon, *alt] = g.filter.map_to_geodetic(x, y, z);
    GATE_OK
}

/// Safety: `g` from `gate_new`.
#[no_mangle]
pub unsafe extern "C" fn gate_map_surface(g: *const Gate, x: f64, y: f64) -> f64 {
    g.as_ref().map_or(f64::NAN, |g| g.filter.world.surface(x, y))
}
