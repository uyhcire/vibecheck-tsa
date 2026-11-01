// Lean runtime start-up for a C ABI dylib: define LEAN_RT_MODULE_INIT (the root module's initializer), then include.
#ifndef LEAN_RUNTIME_H
#define LEAN_RUNTIME_H
#include <lean/lean.h>
#include <pthread.h>

#ifndef LEAN_RT_MODULE_INIT
#error "define LEAN_RT_MODULE_INIT before including lean_runtime.h"
#endif

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void lean_init_task_manager(void);
lean_object *LEAN_RT_MODULE_INIT(uint8_t builtin);

static pthread_once_t lean_rt_once = PTHREAD_ONCE_INIT;
static int lean_rt_ok;
static pthread_t lean_rt_thread;
static pthread_key_t lean_rt_key;
static _Thread_local int lean_rt_thread_ready;

static void lean_rt_thread_exit(void *p) { (void)p; lean_finalize_thread(); }

static void lean_rt_init(void) {
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  lean_object *res = LEAN_RT_MODULE_INIT(1);
  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); lean_dec_ref(res); return; }
  lean_dec_ref(res);
  lean_init_task_manager();
  pthread_key_create(&lean_rt_key, lean_rt_thread_exit);
  lean_rt_thread = pthread_self();
  lean_rt_thread_ready = 1;
  lean_rt_ok = 1;
}

// 0 if module initialisation failed; also gives threads Lean did not create their allocator state.
static int lean_rt_ensure(void) {
  pthread_once(&lean_rt_once, lean_rt_init);
  if (!lean_rt_ok) return 0;
  if (!lean_rt_thread_ready) {
    if (!pthread_equal(pthread_self(), lean_rt_thread)) {
      lean_initialize_thread();
      pthread_setspecific(lean_rt_key, (void *)1);
    }
    lean_rt_thread_ready = 1;
  }
  return 1;
}

#endif
