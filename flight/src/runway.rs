//! The runway, the landing funnel and the low-fuel start (shared by the world, the escapes and the gate; the same
//! numbers are in `CityGate/Landing.lean`). Map metres: x east, y north, z altitude.
//!
//! The world floor is the runway surface: terrain below `RWY_Z` is raised to it, and map altitude is JSBSim's
//! altitude above sea level plus `MAP_DATUM`, so JSBSim's ground plane (0 ft) is exactly that floor.

/// Runway: `[RWY_X0, RWY_X1] × [RWY_Y0, RWY_Y1]`, surface at `RWY_Z`; landing eastbound, threshold at `RWY_X0`.
pub const RWY_X0: f64 = -100.0;
pub const RWY_X1: f64 = 1100.0;
pub const RWY_Y0: f64 = -1360.0;
pub const RWY_Y1: f64 = -1320.0;
pub const RWY_YC: f64 = -1340.0;
pub const RWY_Z: f64 = 9.0;
/// Map altitude = JSBSim altitude above sea level + `MAP_DATUM`.
pub const MAP_DATUM: f64 = 9.0;
/// Glideslope aim: threshold crossing height above the runway (m).
pub const TCH: f64 = 15.0;

/// Landing funnel (the escapes' end): on final, `d = RWY_X0 - x` in `[FUN_D0, FUN_D1]` m before the threshold;
/// `|y - RWY_YC| <= max(FUN_LAT_FLOOR, tan(FUN_LAT_DEG) d)`; height above the runway minus `TCH` in
/// `[tan(FUN_GS_LO_DEG) d, tan(FUN_GS_HI_DEG) d]`; true airspeed in `[FUN_V_LO, FUN_V_HI]`; track within
/// `FUN_TRACK_DEG` of east; `|bank| <= FUN_BANK_DEG`; vertical speed in `[FUN_VZ_LO, FUN_VZ_HI]`; engine running with
/// at least `FUN_FUEL_LB` of fuel in all.
pub const FUN_D0: f64 = 400.0;
pub const FUN_D1: f64 = 2000.0;
pub const FUN_LAT_DEG: f64 = 3.0;
pub const FUN_LAT_FLOOR: f64 = 5.0;
pub const FUN_GS_LO_DEG: f64 = 2.0;
pub const FUN_GS_HI_DEG: f64 = 4.0;
pub const FUN_V_LO: f64 = 36.0;
pub const FUN_V_HI: f64 = 46.0;
pub const FUN_TRACK_DEG: f64 = 10.0;
pub const FUN_BANK_DEG: f64 = 10.0;
pub const FUN_VZ_LO: f64 = -4.0;
pub const FUN_VZ_HI: f64 = 0.5;
pub const FUN_FUEL_LB: f64 = 2.0;

/// Landing contact rule: only the three wheel contact points may touch, only the runway, at most `GEAR_PEN_MAX` m
/// below its surface (strut compression), sinking at most `TD_SINK_MAX` m/s. Landed: on the runway, wheels only,
/// ground speed below `LANDED_V`; the flight ends there.
pub const TD_SINK_MAX: f64 = 3.0;
pub const GEAR_PEN_MAX: f64 = 0.5;
pub const LANDED_V: f64 = 0.5;

/// Fuel per tank (lb) for low-fuel starts (the template carries 100 lb per tank).
pub const LOW_FUEL_LB: f64 = 8.0;
