// C ABI over JsbExact as a flight-sim plant (CityJsb/Plant.lean). Units SI unless noted.
#ifndef CITYJSB_H
#define CITYJSB_H
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct cityjsb cityjsb;

// Observation layout written by cityjsb_step: north, east (m from the start point), altitude above sea level,
// NED velocity (3), airspeed, roll, pitch, heading (rad, heading clockwise from north), body rates p q r,
// alpha, beta, normal load factor, height above JSBSim terrain, dynamic pressure (Pa), engine rpm,
// ECEF position x, y, z (m). North and east are ECEF z and y, so they are map axes only for a start at lat/lon 0.
enum { CITYJSB_NOBS = 22 };

// In-flight c172p at altitude h_m, airspeed v, flight-path angle gam, heading psi, bank phi, angle of attack alpha.
// Returns NULL if the Lean runtime failed to initialise.
cityjsb *cityjsb_new(double h_m, double v, double gam, double psi, double phi, double alpha);

// The exact state of a running JSBSim c172p from a state dump (jsbx/export_state.hpp): n doubles in the order
// cityjsb_dump_field lists. Returns NULL if n != cityjsb_dump_len() or the Lean runtime failed to initialise.
cityjsb *cityjsb_from_dump(const double *dump, size_t n);

// The observation (layout above) at the state a dump was taken at; returns 0, or -1 if n != cityjsb_dump_len().
int cityjsb_obs_from_dump(const double *dump, size_t n, double obs[CITYJSB_NOBS]);

// Number of fields in a state dump, and the name of field i ("" past the end); fixed for the c172p.
size_t cityjsb_dump_len(void);
const char *cityjsb_dump_field(size_t i);

// One JSBSim frame (1/128 s). Controls are JSBSim's normalised commands: elevator positive = nose down,
// aileron, rudder in [-1, 1], throttle in [0, 1].
void cityjsb_step(cityjsb *p, double elev, double ail, double rud, double thr, double obs[CITYJSB_NOBS]);

// An independent copy (for look-ahead rollouts); the state itself is shared until either copy steps.
cityjsb *cityjsb_clone(const cityjsb *p);

void cityjsb_free(cityjsb *p);

#ifdef __cplusplus
}
#endif
#endif
