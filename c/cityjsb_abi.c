// C ABI over CityJsb/Plant.lean (cityjsb.h) and the Lean city gate, CityGate/Ffi.lean (citygate.h); no `main` here.
// The runtime starts from CityGate.Ffi, which imports CityJsb.Plant; lean_runtime.h also starts Lean's task manager,
// on which the gate's candidate checks run in parallel (Task.spawn), and registers every calling thread.
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

lean_object *citygate_new_lean(double x, double y, double z, double v, double gam, double psi, double phi, double n,
                               double thr);
uint8_t citygate_start_ok_lean(lean_obj_arg g);
lean_object *citygate_frame_lean(lean_obj_arg g, double elev, double ail, double rud, double thr);
lean_object *citygate_path_lean(lean_obj_arg g);
lean_object *citygate_obs_lean(lean_obj_arg g);
lean_object *citygate_bypass_lean(lean_obj_arg g, double elev, double ail, double rud, double thr);
lean_object *citygate_restart_lean(lean_obj_arg g);

struct citygate { lean_object *g; };

API citygate *citygate_new(double x, double y, double z, double v, double gam, double psi, double phi, double n,
                           double thr) {
  if (!lean_rt_ensure()) return NULL;
  citygate *h = malloc(sizeof *h);
  if (!h) return NULL;
  h->g = citygate_new_lean(x, y, z, v, gam, psi, phi, n, thr);
  return h;
}

API int citygate_start_ok(const citygate *h) {
  lean_rt_ensure();
  lean_inc(h->g); /* the Lean function consumes its argument */
  return citygate_start_ok_lean(h->g) ? 1 : 0;
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
  citygate_take(h, citygate_frame_lean(h->g, elev, ail, rud, thr), out); /* consumes the old h->g */
}

API void citygate_bypass(citygate *h, double elev, double ail, double rud, double thr, double out[CITYGATE_NOUT]) {
  lean_rt_ensure();
  citygate_take(h, citygate_bypass_lean(h->g, elev, ail, rud, thr), out);
}

API int citygate_restart(citygate *h) {
  lean_rt_ensure();
  h->g = citygate_restart_lean(h->g);
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
  lean_object *fa = citygate_path_lean(h->g);
  size_t n = lean_sarray_size(fa) / 3;
  if (xyz) memcpy(xyz, lean_float_array_cptr(fa), sizeof(double) * 3 * (n < max_points ? n : max_points));
  lean_dec(fa);
  return n;
}

API void citygate_free(citygate *h) {
  if (!h) return;
  lean_rt_ensure();
  lean_dec(h->g);
  free(h);
}
