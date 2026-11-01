// C ABI over JsbExact as a flight-sim plant (CityJsb/Plant.lean). Units SI unless noted.
#ifndef CITYJSB_H
#define CITYJSB_H
#ifdef __cplusplus
extern "C" {
#endif

typedef struct cityjsb cityjsb;

// Observation layout written by cityjsb_step: north, east (m from the start point), altitude above sea level,
// NED velocity (3), airspeed, roll, pitch, heading (rad, heading clockwise from north), body rates p q r,
// alpha, beta, normal load factor, height above JSBSim terrain, dynamic pressure (Pa), engine rpm.
enum { CITYJSB_NOBS = 19 };

// In-flight c172p at altitude h_m, airspeed v, flight-path angle gam, heading psi, bank phi, angle of attack alpha.
// Returns NULL if the Lean runtime failed to initialise.
cityjsb *cityjsb_new(double h_m, double v, double gam, double psi, double phi, double alpha);

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
