// C ABI over CityJsb/Plant.lean; no `main` here.
#include <stdlib.h>
#include <string.h>
#include "cityjsb.h"
#define LEAN_RT_MODULE_INIT initialize_vibecheck_CityJsb_Plant
#include "lean_runtime.h"

#define API __attribute__((visibility("default")))

lean_object *cityjsb_init(double h, double v, double gam, double psi, double phi, double alpha);
lean_object *cityjsb_step_lean(lean_obj_arg s, double elev, double ail, double rud, double thr);

struct cityjsb { lean_object *st; };

API cityjsb *cityjsb_new(double h_m, double v, double gam, double psi, double phi, double alpha) {
  if (!lean_rt_ensure()) return NULL;
  cityjsb *p = malloc(sizeof *p);
  if (!p) return NULL;
  p->st = cityjsb_init(h_m, v, gam, psi, phi, alpha);
  return p;
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
