// libgate: the gatekeeper safety filter for a JSBSim 1.3.3 c172p, as a C library. Usage: docs/xplane-integration.md.
#ifndef GATE_H
#define GATE_H
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define GATE_ABI_VERSION 1u

enum { GATE_OK = 0, GATE_ERR_VERSION = -1, GATE_ERR_BAD_CONFIG = -2, GATE_ERR_BAD_STATE = -3,
       GATE_ERR_BAD_INPUT = -4, GATE_ERR_UNSUPPORTED = -5, GATE_ERR_INTERNAL = -6 };

enum { GATE_PILOT_SURFACES = 1, GATE_PILOT_FBW = 2 };

enum { GATE_MODE_ERROR = -1, GATE_MODE_PILOT = 0, GATE_MODE_ESCAPE = 1 };

enum { GATE_MAX_TICK_FRAMES = 16 };

typedef struct gate gate;

typedef struct {
  uint32_t abi_version, size;   // GATE_ABI_VERSION, sizeof(gate_config)
  uint64_t map_seed;            // Luis's procedural city; 1337 is the demo's map
  const char *map_path;         // reserved for loading a map from files; must be NULL
  double origin_lat_deg;        // WGS84 point that is map (0, 0)
  double origin_lon_deg;
  double origin_alt_m;          // altitude above sea level that is map height 0
  uint32_t pilot_kind;          // GATE_PILOT_SURFACES or GATE_PILOT_FBW
  uint32_t tick_frames;         // JSBSim frames (1/128 s) per tick, 1..GATE_MAX_TICK_FRAMES; 0 = 3
  uint32_t budget_frames;       // JsbExact frames simulated per tick at most; 0 = 2200 (process-wide)
  uint32_t time_cap_ms;         // wall-clock cap on a tick's checks; 0 = none (process-wide)
} gate_config;

typedef struct {
  uint32_t abi_version, size;   // GATE_ABI_VERSION, sizeof(gate_pilot)
  uint32_t kind;                // must equal the gate's pilot_kind
  uint32_t reserved;
  // GATE_PILOT_SURFACES: JSBSim fcs/elevator-cmd-norm (+ = nose down), aileron-cmd-norm, rudder-cmd-norm in
  // [-1, 1], throttle-cmd-norm in [0, 1]. GATE_PILOT_FBW: throttle only.
  double elevator, aileron, rudder, throttle;
  double nz;                    // GATE_PILOT_FBW: load factor demand (g)
  double roll_rate;             // GATE_PILOT_FBW: roll rate demand (rad/s, + = left wing down)
} gate_pilot;

typedef struct {
  uint32_t abi_version, size;
  int32_t mode;                 // GATE_MODE_PILOT: the pilot's command flies; GATE_MODE_ESCAPE: an escape flies
  int32_t escape;               // escape verified (pilot mode) or flying (escape mode), -1 if none; gate_escape_name
  uint32_t verified;            // 1 if `escape` was verified by a full rollout from the state it starts at
  uint32_t frames;              // rows of `surfaces`: the gate's tick_frames
  double surfaces[GATE_MAX_TICK_FRAMES][4];  // elevator, aileron, rudder, throttle cmd-norm, one row per frame
  const double *path;           // the escape's verified path, x y z triples (map metres); valid until the next call
  uint32_t path_len;            // number of points in `path`
  uint32_t check_frames;        // JsbExact frames simulated this tick
  double cpu_ms, wall_ms;       // this tick's cost: thread CPU and wall clock
  double map_pos[3];            // the aircraft in map coordinates (x east, y north, z above origin_alt_m)
  double clearance;             // airframe clearance from terrain and buildings now (m); infinite off the map
} gate_result;

// Returns NULL and sets *err on failure. Builds the map (about a second).
gate *gate_new(const gate_config *cfg, int *err);

// One tick. `dump` is the JSBSim state now (jsbx::export_state, gate_dump_len() doubles). Apply out->surfaces[i]
// to JSBSim's frame i of the next out->frames frames, then call again with the new state. The first tick after
// gate_new or gate_reset also searches every escape from scratch and takes longer.
int gate_tick(gate *g, const double *dump, size_t n, const gate_pilot *pilot, gate_result *out);

// Forget the escape state (a new flight); the map stays.
void gate_reset(gate *g);
void gate_free(gate *g);

size_t gate_dump_len(void);
const char *gate_escape_name(int32_t escape);
// Map height of terrain and roofs under (x, y) in map metres (the 2.5 m raster of map.json).
double gate_map_surface(const gate *g, double x, double y);
// WGS84 latitude, longitude (degrees) and altitude (m) of map point (x, y, z), for placing scenery.
int gate_map_to_geodetic(const gate *g, double x, double y, double z, double *lat_deg, double *lon_deg, double *alt_m);

#ifdef __cplusplus
}
#endif
#endif
