// C ABI over the Lean city gate (CityGate/Ffi.lean), in libcityjsb: the gated closed loop of CityGate.city_safe,
// one JSBSim frame (1/128 s) per call. Units SI; map axes x east, y north, z up (altitude above sea level).
#ifndef CITYGATE_H
#define CITYGATE_H
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct citygate citygate;

// Output of citygate_frame: applied elevator, aileron, rudder, throttle (JSBSim commands); 1 if the gate took a
// candidate this frame, else 0; the observation (cityjsb.h layout, CITYJSB_NOBS = 22); map position x, y, z.
enum { CITYGATE_APPLIED = 0, CITYGATE_ACCEPTED = 4, CITYGATE_OBS = 5, CITYGATE_POS = 27, CITYGATE_NOUT = 30 };

// The closed loop at its start: an aircraft at map point (x, y), altitude z, airspeed v, flight-path angle gam,
// heading psi (counter-clockwise from east), bank phi (positive left wing down), load factor n, throttle thr
// (the point-mass conventions of JsbPlant::new). NULL if the Lean runtime failed to initialise.
citygate *citygate_new(double x, double y, double z, double v, double gam, double psi, double phi, double n,
                       double thr);

// 1 if the start is allowed (CityGate.Init: the gate's initial escape checks out), else 0.
int citygate_start_ok(const citygate *g);

// One frame under the pilot's input (JSBSim commands: elevator positive nose down, aileron, rudder in [-1, 1],
// throttle in [0, 1]); writes CITYGATE_NOUT doubles to out. See citygate_set_parallel for where the candidate
// checks run.
void citygate_frame(citygate *g, double elev, double ail, double rud, double thr, double out[CITYGATE_NOUT]);

// How citygate_frame checks candidates: 0 one after another on the calling thread, stopping at the first that
// verifies (the default); par >= 1 in rounds of `round` frames (0: 64), up to par candidates at once on Lean's
// task manager. The frame computed is the same either way (CityGate.frameOut_fst).
void citygate_set_parallel(citygate *g, unsigned par, unsigned round);

// Display only: up to max_points points (x, y, z triples) of the held controller's predicted path into xyz;
// returns the number of points available (which may exceed max_points).
size_t citygate_path(const citygate *g, double *xyz, size_t max_points);

// The current observation (cityjsb.h layout) and map position: CITYJSB_NOBS + 3 doubles, without stepping.
void citygate_obs(const citygate *g, double out[25]);

// Filter off: one frame of the aircraft alone under the pilot's input, outside the gate (nothing is proved about
// such frames). Output as citygate_frame, with CITYGATE_ACCEPTED 0.
void citygate_bypass(citygate *g, double elev, double ail, double rud, double thr, double out[CITYGATE_NOUT]);

// Filter back on: start the closed loop afresh from the current aircraft, a new start. Returns citygate_start_ok.
int citygate_restart(citygate *g);

// Tooling only: the proposal memory and held controller as numbers (CityGate.traceE); returns how many.
size_t citygate_trace(const citygate *g, double *out, size_t max);

// Tooling only: plant frames citygate_frame would step under this input, checking one candidate after another.
unsigned long long citygate_frames(const citygate *g, double elev, double ail, double rud, double thr);

void citygate_free(citygate *g);

#ifdef __cplusplus
}
#endif
#endif
