// C ABI over CityJsb/Plant.lean; no `main` here.
#include <stdlib.h>
#include <string.h>
#include "cityjsb.h"
#define LEAN_RT_MODULE_INIT initialize_vibecheck_CityJsb_Plant
#include "lean_runtime.h"

#define API __attribute__((visibility("default")))

lean_object *cityjsb_init(double h, double v, double gam, double psi, double phi, double alpha);
lean_object *cityjsb_step_lean(lean_obj_arg s, double elev, double ail, double rud, double thr);
lean_object *cityjsb_from_dump_lean(lean_obj_arg a);
lean_object *cityjsb_obs_from_dump_lean(lean_obj_arg a);
size_t cityjsb_dump_len_lean(lean_object *unit);
lean_object *cityjsb_dump_field_lean(size_t i);

struct cityjsb { lean_object *st; };

API cityjsb *cityjsb_new(double h_m, double v, double gam, double psi, double phi, double alpha) {
  if (!lean_rt_ensure()) return NULL;
  cityjsb *p = malloc(sizeof *p);
  if (!p) return NULL;
  p->st = cityjsb_init(h_m, v, gam, psi, phi, alpha);
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
  lean_object *res = cityjsb_step_lean(p->st, elev, ail, rud, thr);
  lean_object *st = lean_ctor_get(res, 0);
  lean_object *fa = lean_ctor_get(res, 1);
  lean_inc(st);
  memcpy(obs, lean_float_array_cptr(fa), sizeof(double) * CITYJSB_NOBS);
  lean_dec_ref(res);
  p->st = st;
}

API cityjsb *cityjsb_clone(const cityjsb *p) {
  lean_rt_ensure();
  cityjsb *c = malloc(sizeof *c);
  if (!c) return NULL;
  lean_inc(p->st);
  c->st = p->st;
  return c;
}

API void cityjsb_free(cityjsb *p) {
  if (!p) return;
  lean_rt_ensure();
  lean_dec(p->st);
  free(p);
}
