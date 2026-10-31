// Lean runs `main` off the main thread but Cocoa requires it, so this file owns `main`.
#include <lean/lean.h>
#include <SDL3/SDL.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int vc_lean_main(int argc, char **argv);

typedef void (*job_fn)(void *);
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cv_req = PTHREAD_COND_INITIALIZER, cv_done = PTHREAD_COND_INITIALIZER;
static job_fn job; static void *job_arg; static int job_ready, job_done, lean_finished, exit_code;

static void run_on_main(job_fn f, void *a) {
  if (pthread_main_np()) { f(a); return; }
  pthread_mutex_lock(&mu);
  job = f; job_arg = a; job_ready = 1; job_done = 0;
  pthread_cond_signal(&cv_req);
  while (!job_done) pthread_cond_wait(&cv_done, &mu);
  pthread_mutex_unlock(&mu);
}

struct lean_args { int argc; char **argv; };

static void *lean_thread(void *p) {
  struct lean_args *a = p;
  int r = vc_lean_main(a->argc, a->argv);
  pthread_mutex_lock(&mu);
  lean_finished = 1; exit_code = r;
  pthread_cond_signal(&cv_req);
  pthread_mutex_unlock(&mu);
  return NULL;
}

int main(int argc, char **argv) {
  static struct lean_args a;
  a.argc = argc; a.argv = argv;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, 64 << 20);
  pthread_t t;
  pthread_create(&t, &attr, lean_thread, &a);
  for (;;) {
    pthread_mutex_lock(&mu);
    while (!job_ready && !lean_finished) pthread_cond_wait(&cv_req, &mu);
    if (!job_ready && lean_finished) { pthread_mutex_unlock(&mu); break; }
    job_fn f = job; void *arg = job_arg; job_ready = 0;
    pthread_mutex_unlock(&mu);
    f(arg);
    pthread_mutex_lock(&mu);
    job_done = 1;
    pthread_cond_signal(&cv_done);
    pthread_mutex_unlock(&mu);
  }
  return exit_code;
}

static SDL_Window *win;
static SDL_Renderer *ren;
static uint32_t pressed;
static int quit_requested;

enum { OP_COLOR, OP_CLEAR, OP_LINE, OP_RECT, OP_FILLRECT, OP_TRI, OP_TEXT };
struct cmd { int op; float f[6]; uint8_t c[4]; char *text; };
static struct cmd *cmds; static size_t ncmds, capcmds;

static struct cmd *push_cmd(int op) {
  if (ncmds == capcmds) {
    capcmds = capcmds ? capcmds * 2 : 4096;
    cmds = realloc(cmds, capcmds * sizeof *cmds);
  }
  struct cmd *c = &cmds[ncmds++];
  c->op = op; c->text = NULL;
  return c;
}

static lean_obj_res io_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

struct init_args { int w, h; const char *title; int ok; };

static void do_init(void *p) {
  struct init_args *a = p;
  a->ok = 0;
  if (!SDL_Init(SDL_INIT_VIDEO)) { fprintf(stderr, "SDL_Init: %s\n", SDL_GetError()); return; }
  if (!SDL_CreateWindowAndRenderer(a->title, a->w, a->h,
        SDL_WINDOW_RESIZABLE | SDL_WINDOW_HIGH_PIXEL_DENSITY, &win, &ren)) {
    fprintf(stderr, "SDL_CreateWindowAndRenderer: %s\n", SDL_GetError());
    return;
  }
  SDL_SetRenderLogicalPresentation(ren, a->w, a->h, SDL_LOGICAL_PRESENTATION_LETTERBOX);
  SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
  SDL_SetRenderVSync(ren, 1);
  SDL_RaiseWindow(win);
  a->ok = 1;
}

lean_obj_res fs_init(uint32_t w, uint32_t h, b_lean_obj_arg title, lean_obj_arg world) {
  struct init_args a = {(int)w, (int)h, lean_string_cstr(title), 0};
  run_on_main(do_init, &a);
  return lean_io_result_mk_ok(lean_box(a.ok));
}

static void do_quit(void *p) { (void)p; SDL_DestroyRenderer(ren); SDL_DestroyWindow(win); SDL_Quit(); }

lean_obj_res fs_quit(lean_obj_arg world) { run_on_main(do_quit, NULL); return io_unit(); }

enum {
  K_UP = 1, K_DOWN = 2, K_THR_UP = 4, K_THR_DN = 8, K_BRAKE = 16,
  P_FILTER = 1 << 16, P_RESTART = 1 << 17, P_PAUSE = 1 << 18, P_GHOST = 1 << 19,
  P_QUIT = 1 << 20, P_HELP = 1 << 21, P_FAST = 1 << 22
};

static void do_poll(void *p) {
  uint32_t *out = p;
  SDL_Event e;
  while (SDL_PollEvent(&e)) {
    if (e.type == SDL_EVENT_QUIT) quit_requested = 1;
    if (e.type == SDL_EVENT_KEY_DOWN && !e.key.repeat) {
      switch (e.key.key) {
        case SDLK_F: pressed |= P_FILTER; break;
        case SDLK_R: pressed |= P_RESTART; break;
        case SDLK_P: pressed |= P_PAUSE; break;
        case SDLK_G: pressed |= P_GHOST; break;
        case SDLK_H: pressed |= P_HELP; break;
        case SDLK_T: pressed |= P_FAST; break;
        case SDLK_ESCAPE: case SDLK_Q: quit_requested = 1; break;
        default: break;
      }
    }
  }
  const bool *ks = SDL_GetKeyboardState(NULL);
  uint32_t held = 0;
  if (ks[SDL_SCANCODE_UP]) held |= K_UP;
  if (ks[SDL_SCANCODE_DOWN]) held |= K_DOWN;
  if (ks[SDL_SCANCODE_W] || ks[SDL_SCANCODE_RIGHT]) held |= K_THR_UP;
  if (ks[SDL_SCANCODE_S] || ks[SDL_SCANCODE_LEFT]) held |= K_THR_DN;
  if (ks[SDL_SCANCODE_SPACE] || ks[SDL_SCANCODE_B]) held |= K_BRAKE;
  *out = held | pressed | (quit_requested ? P_QUIT : 0);
  pressed = 0;
}

// Low 16 bits: keys held now. High bits: keys pressed since the last poll.
lean_obj_res fs_poll(lean_obj_arg world) {
  uint32_t r = 0;
  run_on_main(do_poll, &r);
  return lean_io_result_mk_ok(lean_box_uint32(r));
}

lean_obj_res fs_color(uint8_t r, uint8_t g, uint8_t b, uint8_t a, lean_obj_arg world) {
  struct cmd *c = push_cmd(OP_COLOR);
  c->c[0] = r; c->c[1] = g; c->c[2] = b; c->c[3] = a;
  return io_unit();
}

lean_obj_res fs_clear(lean_obj_arg world) { push_cmd(OP_CLEAR); return io_unit(); }

lean_obj_res fs_line(double x1, double y1, double x2, double y2, lean_obj_arg world) {
  struct cmd *c = push_cmd(OP_LINE);
  c->f[0] = x1; c->f[1] = y1; c->f[2] = x2; c->f[3] = y2;
  return io_unit();
}

lean_obj_res fs_rect(double x, double y, double w, double h, uint8_t fill, lean_obj_arg world) {
  struct cmd *c = push_cmd(fill ? OP_FILLRECT : OP_RECT);
  c->f[0] = x; c->f[1] = y; c->f[2] = w; c->f[3] = h;
  return io_unit();
}

lean_obj_res fs_tri(double x1, double y1, double x2, double y2, double x3, double y3,
                    lean_obj_arg world) {
  struct cmd *c = push_cmd(OP_TRI);
  c->f[0] = x1; c->f[1] = y1; c->f[2] = x2; c->f[3] = y2; c->f[4] = x3; c->f[5] = y3;
  return io_unit();
}

lean_obj_res fs_text(double x, double y, double scale, b_lean_obj_arg s, lean_obj_arg world) {
  struct cmd *c = push_cmd(OP_TEXT);
  c->f[0] = x; c->f[1] = y; c->f[2] = scale;
  c->text = strdup(lean_string_cstr(s));
  return io_unit();
}

static const char *shot_path;

static void do_present(void *p) {
  (void)p;
  Uint8 cr = 0, cg = 0, cb = 0, ca = 255;
  SDL_SetRenderDrawColor(ren, 0, 0, 0, 255);
  SDL_RenderClear(ren);
  for (size_t i = 0; i < ncmds; i++) {
    struct cmd *c = &cmds[i];
    switch (c->op) {
      case OP_COLOR:
        cr = c->c[0]; cg = c->c[1]; cb = c->c[2]; ca = c->c[3];
        SDL_SetRenderDrawColor(ren, cr, cg, cb, ca);
        break;
      case OP_CLEAR: SDL_RenderClear(ren); break;
      case OP_LINE: SDL_RenderLine(ren, c->f[0], c->f[1], c->f[2], c->f[3]); break;
      case OP_RECT: case OP_FILLRECT: {
        SDL_FRect rc = {c->f[0], c->f[1], c->f[2], c->f[3]};
        if (c->op == OP_FILLRECT) SDL_RenderFillRect(ren, &rc); else SDL_RenderRect(ren, &rc);
        break;
      }
      case OP_TRI: {
        SDL_FColor col = {cr / 255.f, cg / 255.f, cb / 255.f, ca / 255.f};
        SDL_Vertex v[3] = {
          {{c->f[0], c->f[1]}, col, {0, 0}},
          {{c->f[2], c->f[3]}, col, {0, 0}},
          {{c->f[4], c->f[5]}, col, {0, 0}}};
        SDL_RenderGeometry(ren, NULL, v, 3, NULL, 0);
        break;
      }
      case OP_TEXT:
        SDL_SetRenderScale(ren, c->f[2], c->f[2]);
        SDL_RenderDebugText(ren, c->f[0] / c->f[2], c->f[1] / c->f[2], c->text);
        SDL_SetRenderScale(ren, 1.f, 1.f);
        free(c->text);
        break;
    }
  }
  ncmds = 0;
  if (shot_path) {
    SDL_Surface *surf = SDL_RenderReadPixels(ren, NULL);
    if (surf) { SDL_SaveBMP(surf, shot_path); SDL_DestroySurface(surf); }
    free((void *)shot_path);
    shot_path = NULL;
  }
  SDL_RenderPresent(ren);
}

lean_obj_res fs_screenshot(b_lean_obj_arg path, lean_obj_arg world) {
  shot_path = strdup(lean_string_cstr(path));
  return io_unit();
}

lean_obj_res fs_present(lean_obj_arg world) { run_on_main(do_present, NULL); return io_unit(); }

lean_obj_res fs_ticks(lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box_uint64(SDL_GetTicksNS()));
}

lean_obj_res fs_delay(uint32_t ms, lean_obj_arg world) { SDL_Delay(ms); return io_unit(); }
