#ifndef VCFILTER_H
#define VCFILTER_H
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define VC_ABI_VERSION 1u

enum { VC_FILTER_ENVELOPE = 1, VC_FILTER_TUBE = 2, VC_FILTER_ROLLOUT = 3 };

enum { VC_OK = 0, VC_ERR_BAD_OBS = -1, VC_ERR_NOT_INIT = -2, VC_ERR_INTERNAL = -3,
       VC_ERR_BAD_CONFIG = -4, VC_ERR_VERSION = -5, VC_ERR_UNSUPPORTED = -6 };

enum { VC_PASS = 0, VC_ADJUSTED = 1, VC_ESCAPE = 2, VC_MONITOR_FAIL = 3 };

// VC_CMD_ESCAPE: fly the filter's escape (wings level, pull to climb, full throttle) with the host's autopilot.
enum { VC_CMD_SURFACES = 1, VC_CMD_DEMAND = 2, VC_CMD_ESCAPE = 3 };

enum {
  VC_OBS_T = 1u << 0, VC_OBS_POS = 1u << 1, VC_OBS_VEL = 1u << 2, VC_OBS_ATT = 1u << 3,
  VC_OBS_RATES = 1u << 4, VC_OBS_ELEV = 1u << 5, VC_OBS_THROTTLE = 1u << 6, VC_OBS_FUEL = 1u << 7,
  VC_OBS_GROUND = 1u << 8, VC_OBS_AIRSPEED = 1u << 9
};

// Envelope monitor_flags: bits 0-8 failed this tick, the same bits << 16 latched since reset.
enum {
  VC_MON_VX_MIN = 1u << 0, VC_MON_VX_MAX = 1u << 1, VC_MON_X_LO = 1u << 2, VC_MON_X_HI = 1u << 3,
  VC_MON_H_GAIN = 1u << 4, VC_MON_VZ_FLOOR = 1u << 5, VC_MON_V_FLOOR = 1u << 6,
  VC_MON_INIT = 1u << 7, VC_MON_BAD_OBS = 1u << 8, VC_MON_LATCH_SHIFT = 16
};

typedef struct vc_filter vc_filter;

typedef struct {
  uint32_t abi_version, size;
  uint32_t kind;
  uint32_t reserved;
  uint64_t seed;
  const char *params_path;  // JSON overriding Envelope.Checks.P0 field by field; NULL for P0
} vc_config;

// SI units; x forward along the track, z up (altitude over the terrain datum).
typedef struct {
  uint32_t abi_version, size;
  double t;
  double pos[3];
  double vel[3];
  double pitch, roll, yaw;
  double rates[3];
  double elev_pos, throttle_pos;
  double fuel;
  uint32_t on_ground;
  uint32_t valid_mask;
  double airspeed;  // true airspeed (m/s)
} vc_obs;

// Surfaces normalised; elevator + is nose down (JSBSim fcs/elevator-cmd-norm sign).
typedef struct {
  uint32_t abi_version, size;
  uint32_t kind;
  uint32_t reserved;
  double elevator, aileron, rudder, throttle, brake;
  double nz, roll_rate;
} vc_cmd;

typedef struct {
  uint32_t abi_version, size;
  int32_t verdict;
  uint32_t monitor_flags;
  double margin;  // envelope: worst-case terrain slack (m) of the escape relied on now
  uint64_t escape_id;
  uint64_t tick_index;
  double us_total, us_lean;
  uint32_t escape_phase, reserved;
  double escape_pull, escape_climb, escape_vmin;  // what the guarantee assumes the escape achieves (m/s^2, m/s, m/s)
} vc_info;

vc_filter *vc_filter_new(const vc_config *cfg, int *err);
int vc_filter_tick(vc_filter *f, const vc_obs *obs, const vc_cmd *pilot, vc_cmd *applied, vc_info *info);
void vc_filter_reset(vc_filter *f);
void vc_filter_free(vc_filter *f);
const char *vc_filter_guarantee(const vc_filter *f);
uint32_t vc_filter_command_kind(const vc_filter *f);
uint32_t vc_filter_required_obs(const vc_filter *f);
int64_t vc_filter_live_objects(void);

#ifdef __cplusplus
}
#endif
#endif
