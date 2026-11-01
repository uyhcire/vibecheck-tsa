// C ABI over the Lean envelope filter (VcFilter/EnvelopeFilter.lean); no `main` here.
#include <lean/lean.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "vcfilter.h"

#define VC_API __attribute__((visibility("default")))

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void lean_init_task_manager(void);
lean_object *initialize_vibecheck_VcFilter(uint8_t builtin);
lean_object *vcf_env_config(lean_obj_arg json);
lean_object *vcf_env_init(lean_object *unit);
lean_object *vcf_env_tick(lean_obj_arg cfg, lean_obj_arg st, lean_obj_arg obs, uint8_t present, double elev,
                          lean_obj_arg subs);

struct vc_filter { lean_object *cfg; lean_object *st; };

static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static int init_ok;
static pthread_t init_thread;
static pthread_key_t thread_key;
static _Thread_local int thread_ready;
static atomic_llong live_handles;

static const uint32_t REQUIRED_OBS = VC_OBS_POS | VC_OBS_VEL | VC_OBS_AIRSPEED;

static void thread_exit(void *p) { (void)p; lean_finalize_thread(); }

static void runtime_init(void) {
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  lean_object *res = initialize_vibecheck_VcFilter(1);
  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); lean_dec_ref(res); return; }
  lean_dec_ref(res);
  lean_init_task_manager();
  pthread_key_create(&thread_key, thread_exit);
  init_thread = pthread_self();
  thread_ready = 1;
  init_ok = 1;
}

// Lean needs per-thread allocator state on threads it did not create.
static int ensure_runtime(void) {
  pthread_once(&init_once, runtime_init);
  if (!init_ok) return 0;
  if (!thread_ready) {
    if (!pthread_equal(pthread_self(), init_thread)) {
      lean_initialize_thread();
      pthread_setspecific(thread_key, (void *)1);
    }
    thread_ready = 1;
  }
  return 1;
}

static double now_us(void) {
#ifdef __APPLE__
  return clock_gettime_nsec_np(CLOCK_UPTIME_RAW) / 1e3;
#else
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
#endif
}

static char *read_file(const char *path) {
  FILE *fp = fopen(path, "rb");
  if (!fp) return NULL;
  size_t cap = 4096, n = 0;
  char *buf = malloc(cap);
  size_t k;
  while (buf && (k = fread(buf + n, 1, cap - n - 1, fp)) > 0) {
    n += k;
    if (n + 1 == cap) { cap *= 2; char *b = realloc(buf, cap); if (!b) { free(buf); buf = NULL; } else buf = b; }
  }
  fclose(fp);
  if (buf) buf[n] = 0;
  return buf;
}

VC_API vc_filter *vc_filter_new(const vc_config *cfg, int *err) {
  int e = VC_OK;
  vc_filter *f = NULL;
  if (!cfg || cfg->abi_version != VC_ABI_VERSION || cfg->size < sizeof(vc_config)) { e = VC_ERR_VERSION; goto out; }
  if (cfg->kind != VC_FILTER_ENVELOPE) { e = VC_ERR_UNSUPPORTED; goto out; }
  if (!ensure_runtime()) { e = VC_ERR_INTERNAL; goto out; }
  char *text = cfg->params_path ? read_file(cfg->params_path) : NULL;
  if (cfg->params_path && !text) { e = VC_ERR_BAD_CONFIG; goto out; }
  lean_object *s = lean_mk_string(text ? text : "");
  free(text);
  lean_object *r = vcf_env_config(s);
  if (lean_obj_tag(r) == 0) {
    fprintf(stderr, "vc_filter_new: %s\n", lean_string_cstr(lean_ctor_get(r, 0)));
    lean_dec(r);
    e = VC_ERR_BAD_CONFIG;
    goto out;
  }
  f = malloc(sizeof *f);
  if (!f) { lean_dec(r); e = VC_ERR_INTERNAL; goto out; }
  f->cfg = lean_ctor_get(r, 0);
  lean_inc(f->cfg);
  lean_dec(r);
  lean_mark_mt(f->cfg);
  f->st = vcf_env_init(lean_box(0));
  atomic_fetch_add(&live_handles, 1);
out:
  if (err) *err = e;
  return f;
}

static void escape_cmd(vc_cmd *c) {
  memset(c, 0, sizeof *c);
  c->abi_version = VC_ABI_VERSION;
  c->size = sizeof *c;
  c->kind = VC_CMD_ESCAPE;
  c->throttle = 1.0;
}

static int obs_ok(const vc_obs *o) {
  return o && o->abi_version == VC_ABI_VERSION && o->size >= sizeof(vc_obs) &&
         (o->valid_mask & REQUIRED_OBS) == REQUIRED_OBS;
}

static int cmd_ok(const vc_cmd *c) {
  return c && c->abi_version == VC_ABI_VERSION && c->size >= sizeof(vc_cmd) && c->kind == VC_CMD_SURFACES;
}

VC_API int vc_filter_tick_substeps(vc_filter *f, const vc_obs *obs, const vc_cmd *pilot, vc_cmd *applied,
                                   vc_info *info, const vc_obs *subs, uint32_t nsubs) {
  double t0 = now_us();
  vc_info tmp;
  vc_info *in = info ? info : &tmp;
  if (!applied) return VC_ERR_INTERNAL;
  memset(in, 0, sizeof *in);
  in->abi_version = VC_ABI_VERSION;
  in->size = sizeof *in;
  if (!f || !ensure_runtime()) {
    escape_cmd(applied);
    in->verdict = VC_MONITOR_FAIL;
    in->monitor_flags = VC_MON_BAD_OBS | (VC_MON_BAD_OBS << VC_MON_LATCH_SHIFT);
    in->us_total = now_us() - t0;
    return VC_ERR_NOT_INIT;
  }
  uint8_t present = obs_ok(obs) && cmd_ok(pilot);
  lean_object *arr = lean_alloc_sarray(sizeof(double), 5, 5);
  double *a = lean_float_array_cptr(arr);
  if (present) { a[0] = obs->pos[0]; a[1] = obs->pos[2]; a[2] = obs->vel[0]; a[3] = obs->vel[2]; a[4] = obs->airspeed; }
  else memset(a, 0, 5 * sizeof(double));
  double elev = present ? pilot->elevator : 0.0;
  lean_object *sarr = lean_alloc_sarray(sizeof(double), 5 * (size_t)nsubs, 5 * (size_t)nsubs);
  double *sa = lean_float_array_cptr(sarr);
  for (uint32_t i = 0; i < nsubs; i++) {
    const vc_obs *p = &subs[i];
    double nan = __builtin_nan("");
    int ok = obs_ok(p);
    sa[5 * i] = ok ? p->pos[0] : nan; sa[5 * i + 1] = ok ? p->pos[2] : nan; sa[5 * i + 2] = ok ? p->vel[0] : nan;
    sa[5 * i + 3] = ok ? p->vel[2] : nan; sa[5 * i + 4] = ok ? p->airspeed : nan;
  }
  lean_inc(f->cfg);
  double t1 = now_us();
  lean_object *res = vcf_env_tick(f->cfg, f->st, arr, present, elev, sarr);
  double t2 = now_us();
  f->st = lean_ctor_get(res, 0);
  lean_inc(f->st);
  const double *o = lean_float_array_cptr(lean_ctor_get(res, 1));
  int ret = (int)o[0];
  int use_escape = o[2] != 0;
  in->verdict = (int32_t)o[1];
  in->monitor_flags = (uint32_t)o[3];
  in->margin = o[4];
  in->escape_id = (uint64_t)o[5];
  in->escape_phase = (uint32_t)o[6];
  in->escape_pull = o[7];
  in->escape_climb = o[8];
  in->escape_vmin = o[9];
  in->tick_index = (uint64_t)o[10];
  lean_dec(res);
  if (use_escape) escape_cmd(applied);
  else memcpy(applied, pilot, sizeof *applied);
  in->us_lean = t2 - t1;
  in->us_total = now_us() - t0;
  return ret;
}

VC_API int vc_filter_tick(vc_filter *f, const vc_obs *obs, const vc_cmd *pilot, vc_cmd *applied, vc_info *info) {
  return vc_filter_tick_substeps(f, obs, pilot, applied, info, NULL, 0);
}

VC_API void vc_filter_reset(vc_filter *f) {
  if (!f || !ensure_runtime()) return;
  lean_dec(f->st);
  f->st = vcf_env_init(lean_box(0));
}

VC_API void vc_filter_free(vc_filter *f) {
  if (!f || !ensure_runtime()) return;
  lean_dec(f->st);
  lean_dec(f->cfg);
  free(f);
  atomic_fetch_sub(&live_handles, 1);
}

VC_API const char *vc_filter_guarantee(const vc_filter *f) { (void)f; return "Envelope.never_hit"; }

VC_API uint32_t vc_filter_command_kind(const vc_filter *f) { (void)f; return VC_CMD_SURFACES; }

VC_API uint32_t vc_filter_required_obs(const vc_filter *f) { (void)f; return REQUIRED_OBS; }

VC_API int64_t vc_filter_live_handles(void) { return atomic_load(&live_handles); }
