# Starter guide: the city flight demo, for a smart-TV port

This repository contains a desktop flight demo (`flight/`): a Cessna 172 flying through a procedural
city, with a photorealistic renderer and a safety filter that stops the pilot from crashing. The goal of the port
is the equivalent of this desktop command, on a smart TV:

```sh
make fly    # = lake build libcityjsb, then cd flight && cargo run --release --features jsb -- --safety-filter exact-rollout
```

This guide covers what that command runs, how to build it on a Mac, and where the parts that matter for a TV port
live. It describes only what exists today; nothing here has been tried on a TV.

## What runs

Three layers, in one process:
1. **The aircraft dynamics** (`--features jsb`): JSBSim's c172p flight model, through `JsbExact`, a Lean 4 port of
   JSBSim 1.3.3 that is bit-for-bit identical to JSBSim on the platform it was validated on (macOS, Apple silicon).
   Lean compiles it to C; it is linked into the app as a dynamic library, `libcityjsb.dylib`, with a small C API.
2. **The safety filter** (`--safety-filter exact-rollout`): at every 1/50 s control tick it copies the aircraft, flies candidate escape
   manoeuvres on the copy (exact rollouts, about 6 ms per tick on an M4 Max, at most about 15 ms), and only lets the
   pilot's input through if some escape still works. Otherwise it flies the escape and hands control back when safe.
3. **The app** (Rust): window, input, the city, the renderer, and the simulation loop. It uses macroquad on top of
   miniquad (vendored and patched in `flight/vendor/miniquad`).

## Building on a Mac

Prerequisites: Apple silicon Mac, Xcode command-line tools, Rust (stable), and Lean via `elan` (the toolchain version
is pinned in `lean-toolchain`; `elan` installs it automatically).

```sh
git clone https://github.com/uyhcire/vibecheck-tsa.git && cd vibecheck-tsa   # main
make fly                                     # builds the aircraft dynamics library (first build takes a while), then flies
```

Flags go through `ARGS`, e.g. `make fly ARGS="--classic"`; `make help` lists every target.

Useful variants:
- `--classic`: the original, simpler renderer (also available on OpenGL with `--gl`).
- `--rt`: hardware ray tracing (Metal only, needs a recent Apple GPU).
- `--scenario 1..5`: fixed starts (5 is "Tower gap", flying between two towers); `--kamikaze`: an autopilot that tries
  to crash, to watch the filter work; `--episode N`: replay a recorded test episode.
- `--shot out.png --frames N`: render N frames and save a screenshot, printing fps and GPU/CPU time per frame.
- Keys: arrows/WASD to fly, `Q`/`E` throttle, `Space` filter on/off, `B` show escape paths, `C` camera,
  `V` renderer, `P` weather, `O` lens, `H` help. The full list is in `flight/README.md`.

## Where things are

| What | Where | Notes for a TV port |
|---|---|---|
| App entry, window config, input, HUD, renderer choice | `flight/src/main.rs` | `window_conf` picks Metal or OpenGL; `input()` reads the keyboard (a TV needs remote or gamepad input here) |
| Photoreal renderer | `flight/src/photo.rs`, `flight/src/shaders.rs`, `flight/src/atmos.rs`, `flight/src/ground.rs`, `flight/src/assets.rs` | Shaders are Metal Shading Language only; on non-Apple targets only the classic renderer runs today |
| Ray tracing | `flight/src/rt.rs` | Metal hardware ray tracing via raw Objective-C calls; leave it out of a TV build |
| Aircraft model (graphics) | `flight/src/c172.rs` | Procedural mesh, animated surfaces and prop |
| Patched graphics backend | `flight/vendor/miniquad` (used via `[patch.crates-io]` in `flight/Cargo.toml`) | Adds off-screen rendering and other Metal features the photoreal path needs |
| Simulation loop | `flight/src/sim.rs` | Steps the plant and the filter each tick |
| JSBSim plant (Rust side) | `flight/src/jsb.rs`, `flight/build.rs` | FFI to `libcityjsb`; `build.rs` links `../.lake/build/lib/libcityjsb.dylib` |
| Safety filter | `flight/src/envfilter.rs` | Escape law, escapes, exact-rollout checks, time budget (`--time-cap`) |
| City geometry | `flight/src/world.rs` | Procedural from a seed; buildings, streets, terrain |
| Dynamics library (Lean → C) | `CityJsb/` (plant wrapper), `JsbExact/` (the port), `c/cityjsb.h`, `c/cityjsb_abi.c`, `lakefile.lean` target `libcityjsb` | Lean emits C; the library also links the Lean runtime (`leanrt`, `Init`, `Std`, gmp, libuv, libc++) |
| Textures | `flight/assets/textures` (committed; `fetch.py` re-downloads them, needs Pillow; `LICENSES.md`) | About 10 MB, CC0; procedural stand-ins are used if they are missing |
| Docs | `flight/README.md` | Renderer details, filter results, controls, what is assumed |

## What a TV port will run into

These are the known constraints, as starting points for your own plan.

- **Graphics API.** The photoreal and ray-traced renderers are Metal-only (MSL shaders, Metal-specific backend
  patches). Apple TV is Metal, but miniquad's tvOS support is not something this repo has exercised. Android TV and
  Google TV use OpenGL ES, where only the classic renderer's GLSL shaders exist today; the photoreal shaders would
  need a GLSL ES port. Web-based TV platforms (Tizen, webOS) would mean WebGL plus WebAssembly.
- **The Lean library on another target.** `libcityjsb` is C generated by Lean plus the Lean runtime, built here for
  macOS arm64. Another target needs that C and the Lean runtime cross-compiled for it (for example with the Android
  NDK). This has not been tried. `JsbExact`'s bit-exactness against JSBSim was checked only on macOS; on another
  platform the maths library may differ slightly, which changes the dynamics in the last bits but not the demo.
- **Compute budget.** The filter costs about 6 ms per 1/50 s tick (median) on an M4 Max, at most about 15 ms. TV
  processors are much slower. Levers that exist: `--time-cap` (a per-tick budget; an unfinished check counts as
  failed, so the filter falls back to the escape it already verified), fewer escapes (`--escapes 3`), or running
  the simulation and filter on another device and sending the aircraft state to the TV for display only.
- **Input.** Flying uses arrow keys or WASD plus throttle keys; a TV needs the remote or a gamepad mapped in
  `input()` in `main.rs`.
- **Frame rate.** The photoreal renderer takes about 5–9 ms of GPU time per frame at 2880×1800 on an M4 Max; a TV
  GPU at 1080p or 4K will need the quality knobs (or the classic renderer).

## Contact

Questions go to the repo owner. Anything not described here is outside what has been built so far.
