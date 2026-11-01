// usage: gate_example [DUMP_FILE [LAT LON ALT]]; DUMP_FILE holds gate_dump_len() little-endian doubles.
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include "cityjsb.h"
#include "gate.h"

static const double A = 6378137.0, E2 = 6.69437999014e-3, DEG = 180.0 / M_PI;

int main(int argc, char **argv) {
  size_t n = gate_dump_len();
  double *dump = malloc(n * sizeof *dump);
  gate_config cfg = {GATE_ABI_VERSION, sizeof cfg, 1337, NULL, 0, 0, 0, GATE_PILOT_SURFACES, 3, 0, 0};
  cityjsb *host;
  if (argc > 1) {
    FILE *f = fopen(argv[1], "rb");
    if (!f || fread(dump, sizeof *dump, n, f) != n) { fprintf(stderr, "need %zu doubles in %s\n", n, argv[1]); return 1; }
    fclose(f);
    if (argc > 4) { cfg.origin_lat_deg = atof(argv[2]); cfg.origin_lon_deg = atof(argv[3]); cfg.origin_alt_m = atof(argv[4]); }
    host = cityjsb_from_dump(dump, n);
  } else {
    // cityjsb_new starts at latitude and longitude 0; put the map origin where that point is map (-120, -60).
    cfg.origin_lat_deg = 60.0 / (A * (1 - E2)) * DEG;
    cfg.origin_lon_deg = 120.0 / A * DEG;
  }
  int err;
  gate *g = gate_new(&cfg, &err);
  if (!g) { fprintf(stderr, "gate_new: %d\n", err); return 1; }
  if (argc == 1) {
    double h = gate_map_surface(g, -120, -60) + 88.0;
    host = cityjsb_new(h, 45.0, 0.0, 0.0, 0.0, 0.06);
    cityjsb_set_fuel_freeze(host, 1);
    cityjsb_step_dump(host, 0.0, 0.0, 0.0, 0.75, dump);
  }
  if (!host) { fprintf(stderr, "bad state dump\n"); return 1; }
  // gate_config.fuel_drain is 0, so the gate assumes infinite fuel: the stand-in host steps with fuel freeze, as a
  // JSBSim host with propulsion/fuel_freeze = 1 does.
  cityjsb_set_fuel_freeze(host, 1);
  // The pilot holds a little right aileron: the bank grows until the aircraft turns into the towers.
  gate_pilot pilot = {GATE_ABI_VERSION, sizeof pilot, GATE_PILOT_SURFACES, 0, -0.02, 0.06, 0.0, 0.75, 0, 0};
  gate_result r;
  int last_mode = -2;
  double t = 0, min_clear = INFINITY;
  for (int k = 0; k < 1700; k++) {
    int rc = gate_tick(g, dump, n, &pilot, &r);
    if (rc != GATE_OK) { fprintf(stderr, "gate_tick: %d\n", rc); return 1; }
    if (r.mode != last_mode || k % 43 == 0) {
      printf("t=%5.2f s  map (%7.1f, %7.1f, %5.1f)  clear %6.1f m  %-6s escape %-8s %s  elev %+.2f ail %+.2f rud %+.2f thr %.2f"
             "  path %3u pts  %.1f ms\n",
             t, r.map_pos[0], r.map_pos[1], r.map_pos[2], r.clearance, r.mode == GATE_MODE_PILOT ? "pilot" : "ESCAPE",
             gate_escape_name(r.escape), r.verified ? "verified" : "UNVERIFIED", r.surfaces[0][0], r.surfaces[0][1],
             r.surfaces[0][2], r.surfaces[0][3], r.path_len, r.cpu_ms);
      last_mode = r.mode;
    }
    if (r.clearance < min_clear) min_clear = r.clearance;
    if (r.clearance < 0) { printf("CRASHED\n"); return 2; }
    if (fabs(r.map_pos[0]) > 3000 || fabs(r.map_pos[1]) > 3000) break;
    // A JSBSim host sets fcs/*-cmd-norm to each row, calls FGFDMExec::Run(), and exports the state after the last.
    for (uint32_t i = 0; i < r.frames; i++)
      cityjsb_step_dump(host, r.surfaces[i][0], r.surfaces[i][1], r.surfaces[i][2], r.surfaces[i][3], dump);
    t += r.frames / 128.0;
  }
  printf("flew %.1f s, minimum clearance %.1f m\n", t, min_clear);
  cityjsb_free(host);
  gate_free(g);
  free(dump);
  return 0;
}
