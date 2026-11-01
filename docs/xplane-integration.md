# Running the safety filter next to JSBSim (libgate)

This guide is for running this repository's current-best safety filter, the **gatekeeper filter**, in a host that
flies JSBSim's c172p itself, such as a JSBSim process that drives X-Plane's display. The filter goes where JSBSim
runs: it reads JSBSim's state and returns the control surfaces to apply. It covers building the library, its C API,
the state the host passes in, timing, what exactness requires and how to check it, and the map the filter checks
against (Luis Pabon's procedural city, exported as plain files). The last section lists open questions about the
host. What is and is not proved about the filter is in `docs/gate-proof-status.md`.

## What the filter does

At every tick the filter asks: if the pilot's command is applied for one more tick, can some escape manoeuvre
still get the aircraft out safely from there? It answers by flying the escapes on an exact copy of the aircraft.

- **The copy** is `JsbExact`, a Lean port of JSBSim 1.3.3's `c172p` that produces identical IEEE doubles to
  JSBSim on every compared step (takeoff, landing, level flight and banked turns; macOS arm64 build).
- **The escapes**: a straight climb-out, climbing turns at 30° and 40° bank each way, and a climb along the street
  the aircraft is following. An escape is verified when the body (a 4.5 m sphere) and the wing (a 0.8 m capsule
  through the wingtips) keep 4 m of clearance from terrain and buildings all along it, and it ends in a steady
  climb that stays clear: a climbing line that clears the map, or a climbing circle whose ground ring is clear.
- **The decision**: if the pilot's next tick is followed by a verified escape, the pilot's command flies.
  Otherwise the filter flies the escape it verified on the previous tick, and hands control back as soon as the
  pilot's command verifies again.
- **Results in the reference simulator** (the c172p via `JsbExact`, Luis Pabon's procedural city, `flight/`):
  0 crashes in 200 hostile-pilot episodes (198 of them from verified starts) and in all 5 kamikaze scenarios,
  against 27 crashes for a filter that predicts with a point-mass model. Through the library with raw-surface pilots
  (`gatecheck`), see the numbers in [Checking the library](#checking-the-library).

What is and is not proved: the predictions are exact when the aircraft *is* `JsbExact`. The "clear forever"
endings and the map checks are numerical, not proofs; `docs/gate-proof-status.md` has the details.

## Building

Requires Lean (`elan`; the toolchain is pinned in `lean-toolchain`), Rust (stable) and, on macOS, the Xcode
command-line tools.

```sh
make gate           # dist/libgate.dylib, dist/libcityjsb.dylib, dist/gate.h, dist/cityjsb.h
make gate-example   # builds and runs gate/examples/gate_example.c against dist/
make gate-check     # closed-loop crash check through the library (a few minutes)
```

Packaging: `libgate.dylib` (the filter, Rust) links `libcityjsb.dylib` (`JsbExact` and the Lean runtime, built by
`lake`). Ship both in one directory: `libgate` finds `libcityjsb` next to itself (`@loader_path`). Link a host with
`-Ldist -lgate -lcityjsb` and an rpath to wherever the two dylibs live. The libraries have no other dependencies
beyond the system libraries.

## The API (`gate/gate.h`)

```c
gate_config cfg = {GATE_ABI_VERSION, sizeof cfg,
                   1337,            // map_seed: the demo's map
                   NULL,            // map_path: reserved, must be NULL
                   lat0, lon0,      // origin_lat_deg, origin_lon_deg: the point that is map (0, 0)
                   0.0,             // origin_alt_m: the altitude above sea level that is map height 0
                   GATE_PILOT_SURFACES, 3 /* tick_frames */, 0 /* budget_frames */, 0 /* time_cap_ms */,
                   0);              // fuel_drain: 0 = the host's JSBSim has propulsion/fuel_freeze = 1 (see Exactness)
int err;
gate *g = gate_new(&cfg, &err);          // builds the map (about a second)

for (;;) {
  std::vector<double> dump = jsbx::export_state(fdm);       // the JSBSim state now
  gate_pilot p = {GATE_ABI_VERSION, sizeof p, GATE_PILOT_SURFACES, 0,
                  elevator, aileron, rudder, throttle, 0, 0};
  gate_result r;
  if (gate_tick(g, dump.data(), dump.size(), &p, &r) != GATE_OK) { /* see Errors */ }
  for (uint32_t i = 0; i < r.frames; i++) {                 // r.frames == tick_frames
    fdm.SetPropertyValue("fcs/elevator-cmd-norm", r.surfaces[i][0]);
    fdm.SetPropertyValue("fcs/aileron-cmd-norm",  r.surfaces[i][1]);
    fdm.SetPropertyValue("fcs/rudder-cmd-norm",   r.surfaces[i][2]);
    fdm.SetPropertyValue("fcs/throttle-cmd-norm", r.surfaces[i][3]);
    fdm.Run();
  }
}
gate_free(g);
```

The contract per tick:
1. Export the state after the last `FGFDMExec::Run()` and call `gate_tick` with it and the pilot's command.
2. Apply `surfaces[i]` before JSBSim frame `i`, for `i = 0 .. frames - 1`, then go to 1. The rows are constant
   when the pilot flies (`mode == GATE_MODE_PILOT`) and change frame by frame when an escape flies
   (`GATE_MODE_ESCAPE`): the escape law is closed-loop, and the filter computes its surfaces on `JsbExact`, so they
   are exactly what the law would command on an identical JSBSim.
3. Skipping frames, applying other surfaces, or changing anything else in JSBSim between ticks voids the escape
   the filter is relying on until the next tick re-verifies from the new state.

**Pilot input.** `GATE_PILOT_SURFACES`: JSBSim's `fcs/elevator-cmd-norm` (+1 = nose down), `aileron-cmd-norm`,
`rudder-cmd-norm` in [-1, 1] and `throttle-cmd-norm` in [0, 1], applied directly. `GATE_PILOT_FBW`: the demo's
fly-by-wire demands, `nz` (load factor, g), `roll_rate` (rad/s, + = left wing down) and `throttle`; the filter runs
the fly-by-wire loop itself and returns its surfaces per frame. The kind is fixed at `gate_new`; out-of-range or
NaN values return `GATE_ERR_BAD_INPUT`.

**Result** (`gate_result`):

| field | meaning |
|---|---|
| `mode` | `GATE_MODE_PILOT` (the pilot's command flies) or `GATE_MODE_ESCAPE`; `GATE_MODE_ERROR` with an error code |
| `escape`, `verified` | the escape verified (pilot mode) or flying (escape mode), `gate_escape_name(escape)`; `verified` is 0 only if no escape has ever verified since the start |
| `surfaces[frames][4]` | elevator, aileron, rudder, throttle per frame |
| `path`, `path_len` | the escape's verified path, `path_len` points of x, y, z in map metres; valid until the next call on this handle |
| `check_frames`, `cpu_ms`, `wall_ms` | this tick's cost: `JsbExact` frames simulated, thread CPU and wall time |
| `map_pos`, `clearance` | the aircraft in map coordinates and its airframe clearance from terrain and buildings (m) |

**Other calls.** `gate_reset` starts a new flight on the same map. `gate_dump_len()` is the dump length (289).
`gate_map_surface(g, x, y)` is the height of terrain or roof under a map point; `gate_map_to_geodetic` converts a
map point to latitude, longitude and altitude. `cityjsb.h`'s `cityjsb_dump_field(i)` names dump field `i`, for
checking the host's layout.

**Errors.** `GATE_ERR_BAD_STATE` (dump of the wrong length), `GATE_ERR_BAD_INPUT` (pilot out of range, wrong
kind, null pointers), `GATE_ERR_VERSION` (struct `abi_version`/`size`), `GATE_ERR_BAD_CONFIG`,
`GATE_ERR_UNSUPPORTED` (`map_path` set), `GATE_ERR_INTERNAL`. On an error no surfaces are returned
(`frames == 0`), so the host has no verified command for the coming frames; the filter's state is unchanged, and the
next successful tick re-verifies from the state it is given.

**Threads.** One handle per thread at a time; handles are independent. `budget_frames` and `time_cap_ms` are
process-wide settings.

## The input state: `jsbx/export_state.hpp`

`JsbExact` needs JSBSim's complete step state, including private members no property exposes: the integrator
histories, the friction multipliers of each gear unit, the stall hysteresis, the propeller's acting point. The
header-only C++ helper `jsbx/export_state.hpp` reads them from a live `FGFDMExec`:

```cpp
#include "export_state.hpp"   // before any other JSBSim header in this file
std::vector<double> dump = jsbx::export_state(fdm);   // 289 doubles
```

It compiles JSBSim's headers with `private` and `protected` defined as `public`, so it must come before any other
JSBSim include in its translation unit, and it depends on JSBSim 1.3.3's member layout. `jsbx/harness.cpp` writes
its datasets with the same code. The field order is the interface: `CityJsb.dumpNames` mirrors it, and
`cityjsb_dump_field(i)` lists it at run time.

A Python host using the pip `jsbsim` module cannot reach those members. It needs either a small C++ extension
built against JSBSim 1.3.3 that calls `export_state` on the same `FGFDMExec`, or a C++ host.

## Timing

- A tick is `tick_frames` JSBSim frames (default 3, 23.4 ms at 1/128 s).
- Check cost per tick, thread CPU, on an M4 Max loaded by other jobs: median 8 to 12 ms, p99 22 to 27 ms, at most
  2,200 `JsbExact` frames (`budget_frames`). The first tick after `gate_new` or `gate_reset` also searches every
  escape from scratch.
- The filter must answer before the frames it governs run. A real-time host with a tighter deadline can set
  `time_cap_ms`: a check cut short counts as failed, so the filter keeps flying its verified escape. Safety is
  unchanged; only how often the pilot keeps control is.
- More `tick_frames` means fewer checks per second but a longer stretch of the pilot's command to verify.

## Exactness and the drift check

The filter's predictions are exact only if the host's JSBSim computes what `JsbExact` computes. Requirements:

- JSBSim **1.3.3**, built like the reference (`-ffp-contract=on`, as `jsbx/build.sh on`; on macOS the system
  `libm`, including `__sincos_stret`). The pip `jsbsim==1.3.3` wheel on macOS arm64 matches the source build bit
  for bit (`jsbx/replay_pip.py`).
- The **c172p** files that ship with that version.
- A **1/128 s** frame (`fdm.Setdt(1.0 / 128)`). `JsbExact` steps only at that rate.
- **Infinite fuel**: `propulsion/fuel_freeze` set to 1 after the model is initialised
  (`fdm.SetPropertyValue("propulsion/fuel_freeze", 1)`). The safety theorem is about the aircraft with infinite fuel,
  and `gate_config.fuel_drain = 0` (the default) makes the filter import and roll out with fuel freeze as well. A host
  that keeps fuel burning sets `fuel_drain = 1` instead. The two settings must agree: with a mismatch the rollouts are
  not the host's future (the tank, and so the mass, differ from the first frame on).
- Mixture 0.9 and brakes off (the filter's simulated frames use those).
- Flaps retracted: `JsbExact` has no flap kinematics.
- No gusts or turbulence. A constant wind is carried in the state and predicted; a changing one is not.
- Ground: `JsbExact`'s gear sees flat terrain at one fixed elevation (`Gen.terrain`, from the reference
  configuration). In flight this does not matter; on or near the ground JSBSim's terrain must be at that elevation
  for exactness. The filter's clearance checks use the map's terrain, not this value.

**The drift check** measures how close a host is. The host logs every frame with `jsbx::DriftLog` (the commands
about to be applied, then the state), and `jsbdrift` imports the first record, steps `JsbExact` with the logged
commands alongside, and reports for every field how many frames are bit-identical, the largest absolute and
relative differences, and the first frame they differ:

```sh
lake build jsbdrift && .lake/build/bin/jsbdrift /path/to/log            # log.names + log.bin
.lake/build/bin/jsbdrift /path/to/log --horizon 2048                     # re-import every 16 s, as the filter does
.lake/build/bin/jsbdrift /path/to/log --freeze                           # log from a host with propulsion/fuel_freeze = 1
```

Run the drift check in the mode the host flies: `--freeze` for a host with `propulsion/fuel_freeze` set to 1 (the
setting that matches `fuel_drain = 0`), no flag for a host that burns fuel (`fuel_drain = 1`). `jsbx/drift_host.cpp`
takes `freeze` as its fifth argument to write a log in the first mode. With the mode mismatched, the tank fields
differ on every frame. `jsbx/drift_host.cpp` is an example host. Reference results: the reference build reproduces 120 s of varied flight
bit for bit; a JSBSim built with `-ffp-contract=off` differs from the first frame, by at most 4e-9 ft in position
over the same 120 s.

How to read the result:
- **Bit-identical:** the filter is exact for this host.
- **Small drift** (another platform's maths library, another compiler): the filter still re-imports the true state
  every tick, and the 4 m clearance margin absorbs drift over a 16 s escape, but it is no longer exact. The size of
  the drift over `--horizon 2048` is the number to compare with the margin.
- **Large drift:** a setting differs (version, aircraft files, frame rate, flaps, wind). Compare with the list above.

## The map

The filter checks clearance against Luis's procedural city, built from `map_seed` (1337 is the demo's map),
6 km × 6 km, centred on map (0, 0).

- **Placement.** `origin_lat_deg`, `origin_lon_deg` is the WGS84 point that is map (0, 0); map x and y are east and
  north on the tangent plane there. Map z is altitude above sea level minus `origin_alt_m`. The host flies JSBSim
  at real coordinates; the filter converts the state's ECEF position into map coordinates every tick.
- **Files.** `Tools/city-export` writes the exact geometry: `map.json` (conventions, terrain interpolation rule,
  street axes, clearance), `buildings.csv` (2,145 axis-aligned boxes for seed 1337) and `terrain.csv` (301 × 301
  heights on a 20 m grid). `city-export check` confirms the files rebuild the filter's geometry bit for bit.
  `gate_map_to_geodetic` places any map point at latitude, longitude and altitude, for building matching scenery.
- **Outside the map** there are no obstacles: an escape that leaves the 6 km square counts as clear.
- **Terrain for scenery.** Scenery built from `terrain.csv` shows the ground the filter keeps clear of. JSBSim's
  own ground (for the gear) is a separate setting; see the exactness requirements above.

```sh
cargo run --release --manifest-path Tools/city-export/Cargo.toml -- map city-map
```

## Checking the library

- `make gate-example`: one flight through the C API, `JsbExact` standing in for JSBSim (`cityjsb_step_dump` writes
  the dump JSBSim would export), with a pilot that holds a little right aileron between towers.
- `make gate-check` (`gatecheck`): closed-loop hostile raw-surface pilots from random verified starts and the
  scenario starts, every tick through the dump import. Measured: 0 crashes from 45 of 45 verified starts with
  raw-surface pilots (60 s each, 31% of ticks flying an escape) and from 20 of 20 with fly-by-wire pilots, with
  every replayed tick reproducing the checked frames exactly.
- `cityimporttest`: every record of the harness datasets imports and steps bit for bit.

## Questions for the host

1. **How JSBSim connects, and the state each tick.** Where does the host's `FGFDMExec` live (a C++ program, a
   plugin, or the pip `jsbsim` module in Python), and can the host call `jsbx::export_state` on it every tick and
   apply per-frame surfaces before each `Run()`? From Python this needs a small C++ extension next to the module.
2. **Versions, platform and frame rate.** Which JSBSim version, built how (pip wheel or source, compiler flags),
   on which operating system and CPU? The filter needs a 1/128 s frame; can the host run at that rate? (The sidecar
   on `john/xplane-jsbsim` currently sets 1/120 s.)
3. **Ground.** Where does JSBSim's terrain elevation come from? Exactness on and near the ground needs it at
   `JsbExact`'s fixed elevation; scenery built from `terrain.csv` shows the ground the filter keeps clear of.
4. **Wind.** Will JSBSim have wind or turbulence? Constant wind is predicted exactly; gusts are not.
5. **Controls.** Does the pilot's stick map straight to JSBSim's elevator, aileron and rudder commands
   (`GATE_PILOT_SURFACES`), or is there a trim, dead zone, flap setting or other layer in between that the filter
   should model?
