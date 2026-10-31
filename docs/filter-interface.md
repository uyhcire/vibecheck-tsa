# Swappable safety-filter interface

Status: design, doc-only. Nothing in this file is implemented yet.

## 1. Goals, non-goals, terminology

**Goal.** One interface between verified Lean safety filters and flight-simulation hosts, so a filter can be swapped without changing the host and a host can be swapped without changing the filter. Each filter ships with its own Lean theorem, so swapping the filter swaps the guarantee. The interface states which guarantee is in force; it does not hide the difference.

**Non-goals.** Rendering; the JSBSim port and residual measurement (separate efforts, see `problems/robust-safety/README.md`); a pilot model; a network protocol beyond "the same records over a socket"; changing `Model.lean`, `World.lean`, `Fixed.lean` or `Spec.lean`.

**Terms.**
- *Host*: a program that owns the clock and the aircraft simulation and asks the filter once per tick what command to apply (the SDL game, the JSBSim sidecar, the Rust frontend).
- *Filter*: a Lean program, with a Lean theorem, that maps (observation, pilot command) to an applied command each tick. It may carry state between ticks.
- *Observation*: the host's measurement of the aircraft state, in double precision, in a fixed frame and units.
- *Pilot command / applied command*: what the pilot asked for / what the host must send to the aircraft.
- *Verdict*: the filter's per-tick report of what it did: `PASS` (pilot command applied unchanged), `ADJUSTED` (pilot command modified), `ESCAPE` (committed escape maneuver flying), `MONITOR_FAIL` (the runtime monitor saw a transition outside the filter's assumptions).
- *Monitor*: a per-tick runtime check that the observed transition is one the filter's plant model allows. A monitor firing means the theorem's hypothesis was violated this tick; the theorem says nothing from then on.
- *Guarantee*: the Lean theorem of the filter, read together with its hypotheses and its trusted definitions (README "Trusted surface").
- *Escape*: a committed maneuver that brings the aircraft to a safe terminal condition (today: autoland to a stop on a runway).

## 2. The C ABI

The library is a static (and optionally shared) library exposing a C ABI. It must not define `main`: `c/shim.c` owns `main` today because Cocoa needs the process main thread, and a filter library embedded in a host must not collide with the host's entry point. Lean `@[export]` functions take only scalars and `lean_object*`, so a thin C shim (`c/filter_abi.c`, same pattern as `c/shim.c` for SDL) converts the structs below to and from Lean objects. All structs are plain C, fixed-width, with a leading `uint32_t abi_version` and `uint32_t size`; fields are only appended.

```c
typedef struct vc_filter vc_filter;                 // opaque

typedef struct { uint32_t abi_version, size;
                 uint32_t kind;                     // VC_FILTER_ENVELOPE | _TUBE | _ROLLOUT
                 uint64_t seed;                     // filter-internal tie-breaking only
                 const char *params_path; } vc_config;   // optional tuning file, may be NULL

vc_filter *vc_filter_new(const vc_config *cfg, int *err);   // NULL on failure, *err set
int  vc_filter_tick(vc_filter *f, const vc_obs *obs, const vc_cmd *pilot,
                    vc_cmd *applied, vc_info *info);
void vc_filter_reset(vc_filter *f);                 // forget plan and monitor state; next tick re-initialises
void vc_filter_free(vc_filter *f);
```

**Observation (`vc_obs`).** Doubles, SI units, right-handed frame with x forward along the runway axis, z up (the 2D model's `x, h` map to `x, z`):
`t` (s), `pos[3]` (m), `vel[3]` (m/s), `pitch, roll, yaw` (rad), `rates[3]` (rad/s), `elev_pos, throttle_pos` (actuator positions, normalised), `fuel` (s of full throttle, or `NaN` if unknown), `on_ground` flag, `valid_mask` bitfield naming the fields that were measured.
Required fields per filter: *rollout* (2D Lean model): `pos` (x, z), `vel` (x, z), `pitch`, `rates[pitch]`, `elev_pos`, `fuel`, `on_ground`. *Tube*: same, plus the previous tick's applied command so the one-step residual can be computed. *Envelope*: `pos`, `vel`, `pitch`, `rates`, `throttle_pos` (the 3D point-mass and the envelope relation use a subset). A missing required field makes the tick return `VC_ERR_BAD_OBS` with the fallback below.

**Command (`vc_cmd`).** Two layers in one struct: `kind` is `VC_CMD_SURFACES` (normalised `elevator, aileron, rudder` in [-1,1], `throttle` in [0,1], `brake`) or `VC_CMD_DEMAND` (load-factor demand, roll-rate demand, throttle, matching the Rust frontend's 3-component `Cmd`). Each filter declares which kind it consumes and produces (`vc_filter_command_kind`); a *host adapter* (in the host, not the filter) maps its input device to that kind and maps the applied command back (for example surfaces to JSBSim's `fcs/elevator-cmd-norm`, demand to the Rust model's `Cmd`). The Lean 2D `Input` (`stick`, `throttle`, `brake`) is the `SURFACES` kind restricted to the elevator and throttle.

**Info (`vc_info`).** `verdict` (enum above), `margin` (filter-defined, non-negative, 0 means at the boundary; unit documented per filter), `escape_id`, `monitor_flags` (bitfield: which monitor clause failed), `us_total`, `us_lean` (wall-clock microseconds of the tick and of the Lean call), `tick_index`.

**Errors and fallback.** `applied` is always written, including on every error return. On error the fallback is, in order: continue the committed escape if one exists; otherwise the filter's fixed safe command (wings level, throttle idle, brake on ground); never the unchecked pilot command. The return value is `VC_OK`, or a negative code (`VC_ERR_BAD_OBS`, `VC_ERR_NOT_INIT`, `VC_ERR_INTERNAL`); `info->verdict` is set to `MONITOR_FAIL` where applicable and the error is also latched in `monitor_flags`.

**Threading and runtime.** The first `vc_filter_new` in a process initialises the Lean runtime once (`lean_initialize_runtime_module`, the module initialisers, `lean_io_mark_end_initialization`, `lean_init_task_manager`) under a `pthread_once`; the library never finalises it. A `vc_filter` is not internally synchronised: one thread at a time per handle; distinct handles may be ticked concurrently. The calling thread needs a stack of at least 16 MiB (the host's thread, or the library spawns none); the current game uses 64 MiB for deep non-tail recursion. Lean objects the shim creates are freed (`lean_dec`) before return.

**Memory.** The host owns all `vc_obs`, `vc_cmd`, `vc_info` and `vc_config` memory; the library copies what it keeps (`params_path` is read during `vc_filter_new`). The library owns the `vc_filter` until `vc_filter_free`. No pointer into library memory is returned.

## 3. The Lean side

```lean
/-- A verified filter. `Plant` is the model its theorem is about, `Obs` what it reads. -/
structure SafetyFilter (Obs Cmd : Type) where
  St      : Type                                   -- abstract filter state (plan, monitor memory)
  init    : St
  tick    : St → Obs → Cmd → St × Cmd × Verdict    -- the code that runs
  -- the guarantee, supplied by the instance:
  Plant   : PlantSpec                              -- plant state, Allowed, Safe, Init
  view    : Obs → Plant.State                      -- observation mapping (conservative, see below)
  guarantee : ∀ pilot, ClosedLoopAssumptions Plant tick pilot → ∀ n, Plant.Safe (state n)
```

Each filter instance fills in `Plant` and `guarantee`; the ABI shim only ever calls `init` and `tick`. `guarantee` is a field (or a companion theorem named `<filter>_guarantee`) so `#print axioms` and `#spec_surface` run on it, and `make verify` audits it per filter.

**Generalising `Certificate`.** `Certificate` has a deterministic `step : State → Input → State`, and `never_crash` follows from `invariant`. The new interface replaces `step` by a relation `Allowed : State → Input → State → Prop` ("the plant may move from `s` to `s'` under `u`"). `Certificate` is the special case `Allowed s u s' := s' = step s u`, and the existing `never_crash` is recovered as a corollary (a theorem to be proved with the interface, not an edit of the frozen `Spec.lean`). The relational invariant is `Inv s → Allowed s (filter s u) s' → Inv s'`; the robust certificate in `problems/robust-safety/README.md` is `Allowed s u s' := ∃ d ∈ D, s' = perturb (step s u) d`. A stateful filter's `Inv` ranges over the pair (plant state, filter state), and the theorem is projected back to the plant state.

**Conservative conversion.** The host gives doubles; the filter's numbers are fixed-point `Fx` (integer over 2¹⁶). `view` converts with directed rounding chosen per field so the converted state is never more favourable than the observation: heights, clearances and fuel round down, sink rate, speed in overspeed direction, and rates round to the unsafe side, and the conversion widens by one quantum where direction is not known. For interval-based filters `view` returns a box that contains the observed double with margin at least the measured sensor and quantisation error. Non-finite or out-of-range inputs make `view` fail, which the shim reports as `VC_ERR_BAD_OBS`. The conversion is part of the trusted surface and is stated, with a lemma "converted state is within the box of the observation", in Lean.

## 4. What the guarantee says, per filter

In each case the theorem is about the filter's Lean model of the aircraft and the closed loop in which the filter's applied command is what the aircraft receives.

1. **Performance-envelope filter** (after ACAS X, Auto-GCAS, ModelPlex). *Proved:* for any state in which the worst-case closed-form escape check against a clearance map succeeds, flying the escape maneuver from that state stays inside the clearance map (a closed-form inequality over the envelope relation `Allowed`, which over-approximates the aircraft's performance limits). The filter passes the pilot command only if the check succeeds from every state `Allowed` permits next. *Checked at runtime:* each tick, the monitor tests that the observed transition lies in the envelope relation; failure sets `MONITOR_FAIL`. *Only measured:* that the envelope relation actually contains the aircraft's real transitions (flight tests, fuzzing); a monitor that never fires is evidence, not proof. Claim: while the monitor has not fired, the aircraft does not hit the clearance map.
2. **Robust-tube backup filter.** *Proved:* given a committed escape plan (one set per tick) whose every set pushed one tick through an interval step and widened by `D` lands inside the next set (a one-step inclusion check, verified in Lean for each plan the filter commits to), and whose sets avoid crash states, then any plant trajectory with per-tick residual inside `D` stays in the tube. Claim: for every pilot and every disturbance sequence inside `D`, no crash. *Checked at runtime:* the inclusion check on every new plan, and the residual of each observed tick against `D` (monitor). *Only measured:* the bound `D` itself, from JSBSim residuals (`sysid/`); the guarantee is conditional on it.
3. **Point-rollout backup filter** (the current design). *Proved:* `flight_never_crashes`: against the Lean `step`, no pilot sequence crashes. *Checked at runtime:* only the rollout itself. *Only measured:* nothing is bounded; against any other plant (JSBSim's Cessna 172) the theorem does not apply, and the host must treat the Lean model's agreement with that plant as an unproved assumption. The monitor (observed state versus the Lean prediction, thresholded) flags disagreement but gives no soundness.

Every verdict carries which guarantee it falls under: the `vc_filter_guarantee()` string names the theorem, and `MONITOR_FAIL` means "outside the guarantee from now on" until `vc_filter_reset`.

## 5. Host integration

**Sidecar (JSBSim + FlightGear viewer).** One process owns the clock: each tick it reads JSBSim properties into `vc_obs`, reads the pilot command from FlightGear's input over a local socket (or a joystick), calls `vc_filter_tick`, writes `applied` to JSBSim's flight-control properties, runs `JSBSim::FGFDMExec::Run()` for the tick's substeps, and publishes the state to FlightGear in its native or generic-protocol format so FlightGear only renders. Every tick is filtered and every record (obs, pilot, applied, info) is logged, so a flight is replayable bit-for-bit through the filter. A prototype is being built separately; this document fixes only the ABI it calls.

**Rust frontend (`origin/bcbf-city-flight`).** `Sim::tick` (`flight/src/sim.rs`) today calls `FilterState::tick`, which returns `CmdSrc::{Const(Cmd), FollowPlan}`, and then resolves `FollowPlan` against the plan. The trait removes that split: `FollowPlan` is resolved inside the filter.

```rust
pub trait Filter {
    fn tick(&mut self, obs: &Obs, pilot: Cmd) -> (Cmd, Verdict);  // applied is always valid
    fn reset(&mut self);
}
```

`Obs` is built from the 10-state point mass (`X, Y, Z, V, GAM, PSI, PHI, P, N, THR`); physics runs at 100 Hz, the filter at 50 Hz (two physics steps per tick), so `obs` is sampled at the tick boundary and the applied command is held for both steps. Implementations: the existing Rust filter behind the trait, and `LeanFilter`, a wrapper over the C ABI, linked by `build.rs` (invokes `lake build` for the static library and emits `cargo:rustc-link-lib=static=vibecheck_filter` and the Lean runtime libraries) or, for hosts that cannot link Lean, the same `vc_obs`/`vc_cmd`/`vc_info` records over a local socket with a length-prefixed binary framing. Every Rust field maps to an `vc_obs` field or `valid_mask` excludes it.

## 6. Testing

**Shared harness.** One program, in the repo's `Tools/`, drives any filter through the C ABI against any plant adapter (Lean `step`, JSBSim, Rust point mass) with fixed seeds. Pilots: random (uniform and held-key), scripted adversarial (dive at terrain, stall, overspeed, full-throttle brake on ground, alternate extremes at the actuator rate limit), and recorded human flights. Metrics per run: crashes, monitor firings, intervention rate (ticks with verdict other than `PASS`), smoothness (sum of |applied change| per tick), `us_total` mean and max, margin distribution. Results are written as one CSV row per (filter, plant, pilot, seed) so filters compare on identical inputs.

**ABI conformance (every filter must pass).**
- `applied` is written on every call, including after errors and with NaN/out-of-range observations.
- Determinism: the same obs/pilot sequence after `vc_filter_reset` yields identical applied and info.
- Passthrough: when the verdict is `PASS`, `applied == pilot` exactly.
- Admissibility: `applied` is within its declared range.
- Missing required fields give `VC_ERR_BAD_OBS` and a safe `applied`.
- No leaks across 10⁶ ticks and across `new/free` cycles (allocation counters in the shim).
- Two handles ticked from two threads do not interfere.
- Stack: runs on a 16 MiB thread.
- Timing: `us_total` p99 under the host's tick budget (62.5 ms at 16 Hz; 20 ms at 50 Hz).
- Negative controls: with the monitor-fail condition injected, the verdict is `MONITOR_FAIL`.
- The guarantee name returned by the ABI matches a theorem that `make verify` audits to the allowed axioms.

## 7. Open questions

- **Open:** observation `valid_mask` versus a per-filter fixed input struct; the mask is flexible but moves a failure from compile time to run time.
- **Open:** the conservative `view` for 3D observations (heading, bank) and a sensor-error bound: where its constants come from and who reviews them.
- **Open:** whether `MONITOR_FAIL` latches until reset or the filter tries to re-enter its guarantee after the observed state returns inside the envelope.
- **Open:** a single `Verdict` enum versus per-filter extensions; a shared enum makes the harness uniform but may be too coarse for the tube filter.
- **Open:** `SafetyFilter.guarantee` as a structure field versus a companion theorem (a field forces every filter into one proof shape; a companion keeps `Certificate`-style proofs untouched).
- **Open:** how the 2D Lean models (rollout, tube) are used in a 3D host (the Rust frontend): project to the vertical plane, or the filters are 2D-only and the 3D host uses the envelope filter.
- **Open:** the sidecar's handling of JSBSim's internal substeps (the residual bound `D` is per filter tick, so the substep count is part of the guarantee's hypotheses).
