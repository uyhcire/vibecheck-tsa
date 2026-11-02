// C ABI over CityJsb/Plant.lean (cityjsb.h) and the Lean city gate, CityGate/Ffi.lean (citygate.h); no `main` here.
// The runtime starts from CityGate.Ffi, which imports CityJsb.Plant; lean_runtime.h also starts Lean's task manager,
// on which the gate's candidate checks can run in parallel (citygate_set_parallel), and registers every calling thread.
#include <stdlib.h>
#include <string.h>
#include "cityjsb.h"
#include "citygate.h"
#define LEAN_RT_MODULE_INIT initialize_vibecheck_CityGate_Ffi
#include "lean_runtime.h"

#define API __attribute__((visibility("default")))

lean_object *cityjsb_init(double h, double v, double gam, double psi, double phi, double alpha);
lean_object *cityjsb_step_lean(lean_obj_arg s, double elev, double ail, double rud, double thr);
lean_object *cityjsb_from_dump_lean(lean_obj_arg a);
lean_object *cityjsb_obs_from_dump_lean(lean_obj_arg a);
lean_object *cityjsb_step_dump_lean(lean_obj_arg s, double elev, double ail, double rud, double thr);
lean_object *cityjsb_step_ff_lean(lean_obj_arg s, uint8_t ff, double elev, double ail, double rud, double thr);
lean_object *cityjsb_step_dump_ff_lean(lean_obj_arg s, uint8_t ff, double elev, double ail, double rud, double thr);
size_t cityjsb_dump_len_lean(lean_object *unit);
lean_object *cityjsb_dump_field_lean(size_t i);

struct cityjsb { lean_object *st; int fuel_freeze; };

API cityjsb *cityjsb_new(double h_m, double v, double gam, double psi, double phi, double alpha) {
  if (!lean_rt_ensure()) return NULL;
  cityjsb *p = malloc(sizeof *p);
  if (!p) return NULL;
  p->st = cityjsb_init(h_m, v, gam, psi, phi, alpha);
  p->fuel_freeze = 0;
  return p;
}

API size_t cityjsb_dump_len(void) {
  if (!lean_rt_ensure()) return 0;
  return cityjsb_dump_len_lean(lean_box(0));
}

static lean_object **field_names;
static pthread_once_t field_once = PTHREAD_ONCE_INIT;

static void field_init(void) {
  size_t n = cityjsb_dump_len_lean(lean_box(0));
  lean_object **names = malloc(n * sizeof *names);
  if (!names) return;
  for (size_t i = 0; i < n; i++) {
    names[i] = cityjsb_dump_field_lean(i);
    lean_mark_persistent(names[i]);
  }
  field_names = names;
}

API const char *cityjsb_dump_field(size_t i) {
  if (!lean_rt_ensure()) return "";
  pthread_once(&field_once, field_init);
  if (!field_names || i >= cityjsb_dump_len_lean(lean_box(0))) return "";
  return lean_string_cstr(field_names[i]);
}

API cityjsb *cityjsb_from_dump(const double *dump, size_t n) {
  if (!dump || !lean_rt_ensure() || n != cityjsb_dump_len_lean(lean_box(0))) return NULL;
  lean_object *arr = lean_alloc_sarray(sizeof(double), n, n);
  memcpy(lean_float_array_cptr(arr), dump, n * sizeof(double));
  lean_object *r = cityjsb_from_dump_lean(arr);
  if (lean_obj_tag(r) == 0) { lean_dec(r); return NULL; }
  cityjsb *p = malloc(sizeof *p);
  if (!p) { lean_dec(r); return NULL; }
  p->fuel_freeze = 0;
  p->st = lean_ctor_get(r, 0);
  lean_inc(p->st);
  lean_dec(r);
  return p;
}

API int cityjsb_obs_from_dump(const double *dump, size_t n, double obs[CITYJSB_NOBS]) {
  if (!dump || !obs || !lean_rt_ensure() || n != cityjsb_dump_len_lean(lean_box(0))) return -1;
  lean_object *arr = lean_alloc_sarray(sizeof(double), n, n);
  memcpy(lean_float_array_cptr(arr), dump, n * sizeof(double));
  lean_object *r = cityjsb_obs_from_dump_lean(arr);
  if (lean_obj_tag(r) == 0) { lean_dec(r); return -1; }
  memcpy(obs, lean_float_array_cptr(lean_ctor_get(r, 0)), sizeof(double) * CITYJSB_NOBS);
  lean_dec(r);
  return 0;
}

API void cityjsb_step(cityjsb *p, double elev, double ail, double rud, double thr, double obs[CITYJSB_NOBS]) {
  lean_rt_ensure();
  lean_object *res = p->fuel_freeze ? cityjsb_step_ff_lean(p->st, 1, elev, ail, rud, thr)
                                    : cityjsb_step_lean(p->st, elev, ail, rud, thr);
  lean_object *st = lean_ctor_get(res, 0);
  lean_object *fa = lean_ctor_get(res, 1);
  lean_inc(st);
  memcpy(obs, lean_float_array_cptr(fa), sizeof(double) * CITYJSB_NOBS);
  lean_dec_ref(res);
  p->st = st;
}

API void cityjsb_step_dump(cityjsb *p, double elev, double ail, double rud, double thr, double *dump) {
  lean_rt_ensure();
  lean_object *res = p->fuel_freeze ? cityjsb_step_dump_ff_lean(p->st, 1, elev, ail, rud, thr)
                                    : cityjsb_step_dump_lean(p->st, elev, ail, rud, thr);
  lean_object *st = lean_ctor_get(res, 0);
  lean_object *fa = lean_ctor_get(res, 1);
  lean_inc(st);
  memcpy(dump, lean_float_array_cptr(fa), sizeof(double) * lean_sarray_size(fa));
  lean_dec_ref(res);
  p->st = st;
}

API void cityjsb_set_fuel_freeze(cityjsb *p, int on) { p->fuel_freeze = on != 0; }

API int cityjsb_fuel_freeze(const cityjsb *p) { return p->fuel_freeze; }

API cityjsb *cityjsb_clone(const cityjsb *p) {
  lean_rt_ensure();
  cityjsb *c = malloc(sizeof *c);
  if (!c) return NULL;
  lean_inc(p->st);
  c->st = p->st;
  c->fuel_freeze = p->fuel_freeze;
  return c;
}

API void cityjsb_free(cityjsb *p) {
  if (!p) return;
  lean_rt_ensure();
  lean_dec(p->st);
  free(p);
}

lean_object *citygate_grid_site_lean(lean_obj_arg unit);
lean_object *citygate_site_new_lean(double x0, double y0, double x1, double y1, uint32_t tnx, uint32_t tny,
                                    lean_obj_arg terr, lean_obj_arg boxes, uint32_t rnx, uint32_t rny,
                                    lean_obj_arg raster, double top);
lean_object *citygate_new_lean(lean_obj_arg s, double x, double y, double z, double v, double gam, double psi, double phi,
                               double n, double thr);
uint8_t citygate_start_ok_lean(lean_obj_arg s, lean_obj_arg g);
lean_object *citygate_frame_lean(lean_obj_arg s, lean_obj_arg g, uint32_t par, uint32_t round, double elev, double ail,
                                 double rud, double thr);
lean_object *citygate_path_lean(lean_obj_arg s, lean_obj_arg g);
lean_object *citygate_obs_lean(lean_obj_arg g);
lean_object *citygate_bypass_lean(lean_obj_arg g, double elev, double ail, double rud, double thr);
lean_object *citygate_restart_lean(lean_obj_arg s, lean_obj_arg g);
lean_object *citygate_trace_lean(lean_obj_arg g);
lean_object *citygate_probe_lean(lean_obj_arg s, lean_obj_arg g, double elev, double ail, double rud, double thr,
                                 lean_obj_arg w);
uint64_t citygate_frames_lean(lean_obj_arg s, lean_obj_arg g, double elev, double ail, double rud, double thr);
lean_object *citygate_rollout_lean(lean_obj_arg s, lean_obj_arg g, uint32_t esc, uint32_t max_frames);

/* A map (CityGate.Site), persistent: shared by every gate and thread, never freed. */
struct citygate_map { lean_object *s; };
struct citygate { lean_object *g; lean_object *s; uint32_t par, round; };

static lean_object *float_array(const double *v, size_t n) {
  lean_object *a = lean_alloc_sarray(sizeof(double), n, n);
  if (n) memcpy(lean_float_array_cptr(a), v, sizeof(double) * n);
  return a;
}

API citygate_map *citygate_map_new(double x0, double y0, double x1, double y1, size_t tnx, size_t tny,
                                   const double *terr, size_t nboxes, const double *boxes, size_t rnx, size_t rny,
                                   const double *raster, double top) {
  if (!lean_rt_ensure()) return NULL;
  lean_object *r = citygate_site_new_lean(x0, y0, x1, y1, (uint32_t)tnx, (uint32_t)tny, float_array(terr, tnx * tny),
                                          float_array(boxes, 6 * nboxes), (uint32_t)rnx, (uint32_t)rny,
                                          float_array(raster, rnx * rny), top);
  if (lean_is_scalar(r)) return NULL; /* none */
  lean_object *s = lean_ctor_get(r, 0);
  lean_inc(s);
  lean_dec(r);
  lean_mark_persistent(s);
  citygate_map *m = malloc(sizeof *m);
  if (!m) return NULL;
  m->s = s;
  return m;
}

static lean_object *grid_site(void) {
  static lean_object *s = NULL;
  if (!s) s = citygate_grid_site_lean(lean_box(0));
  return s;
}

/* The gate's map as an owned argument for a Lean call. */
static lean_object *site_arg(const citygate *h) {
  lean_inc(h->s);
  return h->s;
}

API citygate *citygate_new_on(const citygate_map *m, double x, double y, double z, double v, double gam, double psi,
                              double phi, double n, double thr) {
  if (!lean_rt_ensure()) return NULL;
  citygate *h = malloc(sizeof *h);
  if (!h) return NULL;
  h->s = m ? m->s : grid_site();
  h->g = citygate_new_lean(site_arg(h), x, y, z, v, gam, psi, phi, n, thr);
  h->par = 0;
  h->round = 64;
  return h;
}

API citygate *citygate_new(double x, double y, double z, double v, double gam, double psi, double phi, double n,
                           double thr) {
  return citygate_new_on(NULL, x, y, z, v, gam, psi, phi, n, thr);
}

API int citygate_start_ok(const citygate *h) {
  lean_rt_ensure();
  lean_inc(h->g); /* the Lean function consumes its argument */
  return citygate_start_ok_lean(site_arg(h), h->g) ? 1 : 0;
}

/* Replace h->g by the first component of a (GateState, FloatArray) result and copy the array to out. */
static void citygate_take(citygate *h, lean_object *res, double out[CITYGATE_NOUT]) {
  lean_object *g = lean_ctor_get(res, 0);
  lean_object *fa = lean_ctor_get(res, 1);
  lean_inc(g);
  size_t n = lean_sarray_size(fa);
  memset(out, 0, sizeof(double) * CITYGATE_NOUT);
  memcpy(out, lean_float_array_cptr(fa), sizeof(double) * (n < CITYGATE_NOUT ? n : CITYGATE_NOUT));
  lean_dec_ref(res);
  h->g = g;
}

API void citygate_frame(citygate *h, double elev, double ail, double rud, double thr, double out[CITYGATE_NOUT]) {
  lean_rt_ensure();
  citygate_take(h, citygate_frame_lean(site_arg(h), h->g, h->par, h->round, elev, ail, rud, thr), out); /* consumes the old h->g */
}

API void citygate_bypass(citygate *h, double elev, double ail, double rud, double thr, double out[CITYGATE_NOUT]) {
  lean_rt_ensure();
  citygate_take(h, citygate_bypass_lean(h->g, elev, ail, rud, thr), out);
}

API int citygate_restart(citygate *h) {
  lean_rt_ensure();
  h->g = citygate_restart_lean(site_arg(h), h->g);
  return citygate_start_ok(h);
}

API void citygate_obs(const citygate *h, double out[25]) {
  lean_rt_ensure();
  lean_inc(h->g);
  lean_object *fa = citygate_obs_lean(h->g);
  size_t n = lean_sarray_size(fa);
  memcpy(out, lean_float_array_cptr(fa), sizeof(double) * (n < 25 ? n : 25));
  lean_dec(fa);
}

API size_t citygate_path(const citygate *h, double *xyz, size_t max_points) {
  lean_rt_ensure();
  lean_inc(h->g);
  lean_object *fa = citygate_path_lean(site_arg(h), h->g);
  size_t n = lean_sarray_size(fa) / 3;
  if (xyz) memcpy(xyz, lean_float_array_cptr(fa), sizeof(double) * 3 * (n < max_points ? n : max_points));
  lean_dec(fa);
  return n;
}

API uint64_t citygate_frames(const citygate *h, double elev, double ail, double rud, double thr) {
  lean_rt_ensure();
  lean_inc(h->g);
  return citygate_frames_lean(site_arg(h), h->g, elev, ail, rud, thr);
}

API size_t citygate_probe(const citygate *h, double elev, double ail, double rud, double thr, double *out, size_t max) {
  lean_rt_ensure();
  lean_inc(h->g);
  lean_object *res = citygate_probe_lean(site_arg(h), h->g, elev, ail, rud, thr, lean_io_mk_world());
  if (!lean_io_result_is_ok(res)) { lean_dec_ref(res); return 0; }
  lean_object *fa = lean_io_result_get_value(res);
  size_t n = lean_sarray_size(fa);
  memcpy(out, lean_float_array_cptr(fa), sizeof(double) * (n < max ? n : max));
  lean_dec_ref(res);
  return n;
}

API void citygate_set_parallel(citygate *h, unsigned par, unsigned round) {
  h->par = par;
  h->round = round ? round : 64;
}

API size_t citygate_trace(const citygate *h, double *out, size_t max) {
  lean_rt_ensure();
  lean_inc(h->g);
  lean_object *fa = citygate_trace_lean(h->g);
  size_t n = lean_sarray_size(fa);
  memcpy(out, lean_float_array_cptr(fa), sizeof(double) * (n < max ? n : max));
  lean_dec(fa);
  return n;
}

API size_t citygate_rollout(const citygate *h, unsigned esc, unsigned max_frames, double *out, size_t max) {
  lean_rt_ensure();
  lean_inc(h->g);
  lean_object *fa = citygate_rollout_lean(site_arg(h), h->g, esc, max_frames);
  size_t n = lean_sarray_size(fa);
  if (out) memcpy(out, lean_float_array_cptr(fa), sizeof(double) * (n < max ? n : max));
  lean_dec(fa);
  return n;
}

API void citygate_free(citygate *h) {
  if (!h) return;
  lean_rt_ensure();
  lean_dec(h->g);
  free(h);
}
