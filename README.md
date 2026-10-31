# Vibecheck TSA: a flight sim you can't crash

A side-view flight simulator whose entire core (aerodynamics, controls model, terrain, crash rules, autopilot and safety filter) is written in Lean 4, with a machine-checked guarantee:

> **No sequence of pilot inputs can crash the aircraft.** The filter only changes an input when keeping it would leave the safe set.

Try it: take off, then dive at the mountains, stall it, overspeed it. A verified filter steps in at the last possible moment, and gives control straight back. Press `F` to switch the filter off and see what would have happened.

```
make install   # elan + SDL3 (Homebrew) if missing, then builds
make run
```

Controls: `UP`/`DOWN` pitch, `W`/`S` throttle, `SPACE` brake, `F` filter on/off, `G` show escape path, `T` 2× speed, `R` restart, `P` pause, `H` help, `ESC` quit.

## What is proved

`Vibecheck/Safety.lean`:

```lean
theorem flight_never_crashes (s₀ : State) (h₀ : Init s₀) (pilot : Nat → Input) (n : Nat) :
    ¬ (traj solution s₀ pilot n).crashed
```

`traj` is the closed loop: at each step the pilot asks for anything, `filter` produces the applied input, `step` advances the dynamics. `solution : Certificate` also carries:

| field | statement |
| --- | --- |
| `admissible` | every applied input is in range (stick ∈ [−1,1], throttle ∈ [0,1]) |
| `invariant` | from a safe state, the applied input always leads to a safe state |
| `passthrough` | an in-range input that keeps the plane safe is passed through unchanged |
| `init_sub` | every initial state (parked on a runway) is safe |
| `safe` | safe states are not crashed |

The safe set is "some runway's autoland, simulated forward with the same `step` function, stops the plane on a runway without crashing". The proof of `invariant` never looks inside the aerodynamics: when the filter overrides, it applies the autoland input whose rollout was just checked, so the next state's rollout is the tail of that one. That is why the model can be as rich as it is (lift with a post-stall drop, drag, thrust, fuel, pitch dynamics with an actuator rate limit, ground roll, touchdown limits, overspeed and 6 g overstress).

Also proved (`Vibecheck/Controls.lean`, `Vibecheck/SpecChecks.lean`): the elevator stays in its travel and moves at most 2/s; fuel never increases; the hypotheses are satisfiable (`Init initState`); no certificate can call every state safe; a filter that ignores the pilot violates `passthrough`.

`make verify` rebuilds the proofs and prints the axioms of each main theorem: only `propext`, `Classical.choice`, `Quot.sound`.

## The proofs are about the code that runs

There is no model gap: the game calls `Vibecheck.filter` and `Vibecheck.step` on every 1/16 s tick, the same definitions the theorems mention. Numbers are exact fixed-point (`Fx`, an integer over 2¹⁶) with documented floor rounding; the fast multiply path through `Int64` is proved equal to the exact integer formula (`Fx.fastMul_eq`), so nothing relies on `implemented_by`.

## Trusted surface

What you have to read to believe the theorem means "can't crash":

- `Vibecheck/Fixed.lean`: the number type.
- `Vibecheck/World.lean`: terrain breakpoints and runways.
- `Vibecheck/Model.lean`: `State`, `Input`, `step` (including what counts as a crash and a safe touchdown), `Init`.
- `Vibecheck/Spec.lean`: `Certificate`, `traj`.

Not trusted: `Autoland.lean`, `Filter.lean` (their correctness is what is proved), and the frontend (`App/`, `c/shim.c`), which only draws and reads keys. The frontend's job in the trust story is to call `filter` and `step` and nothing else to move the aircraft.

Modelling assumptions: no wind; the aircraft is a point (touchdown and terrain clearance at the reference point); the plane flies left to right (runways behind it are not escape options).

## How close is a sim step to the continuous physics?

`proofs/` (Mathlib, `make proofs`) states an idealized model, the real-number ODE for the same forces with the elevator and throttle held over the step, and proves, about the exact `stepAir`:

- **Code = Euler + rounding** (`stepAir_near_euler`): every component of the fixed-point step is within 2⁻¹⁶ m (position), 1/2048 m/s (velocity), 1/2048 rad/s (pitch rate) of one exact Euler step; the pitch vector is within 0.039, almost all of it the renormalization.
- **Euler vs exact flow** (`flow_near_euler_box`): any exact solution that stays in a box is within an explicit componentwise bound of the Euler step after 1/16 s. In a cruise box (speeds ≤ 60 m/s, |q| ≤ 0.5 rad/s): 0.09 m in x, 0.11 m in h, 2 m/s in velocity, 0.25 rad/s in q.
- **Combined** (`flow_near_code`, `flow_near_code_cruise`), with satisfiability examples and an axiom audit.

The velocity bounds are honest but loose (the box bounds each component separately). These are per-step statements: the safety theorem is about the sim, not about an aircraft flying the continuous ODE.

## Envelope theorem (`Envelope/`)

A second guarantee that assumes no physics model, only coarse performance bounds of the closed loop (after ACAS X, Auto-GCAS and ModelPlex), so that it can guard JSBSim. Core Lean, exact `Rat` arithmetic, no Mathlib.

```lean
theorem never_hit (P : Params ι) (hP : P.WellFormed) : NeverHits P (filter P)
-- NeverHits P flt: ∀ pilot s, Init P (s 0) →
--   (∀ n, Allowed P (appliedAt flt s pilot n) (s n) (pilot n) (s (n + 1))) →
--   ∀ n, TickClear P (s n) (s (n + 1))
```

`Allowed` (`Envelope/Relation.lean`) is the envelope, one tick at a time: ground speed in `[vxMin, vxMax]` and distance covered in `dt·[vxMin, vxMax]`; altitude gain at least `dt · min vz vz' − hSlack`; vertical speed and airspeed at least `vzFloor`/`VFloor` (free flight: per-input worst drops; escape: a delay with a bounded drop, then `vz' ≥ min (vz + pull(V)·dt) climb(V)`, airspeed at least `max vMin (V − escVDrop)`). `monitor` checks it at runtime (`monitor_iff`), so on any flight where the monitor never fires, the theorem applies. `TickClear` asks terrain + margin to lie below `min h h' − sag` over the whole swept interval `[x, x']`: between-tick safety, given that the plant stays inside that box within a tick. For a plant that moves in discrete substeps (JSBSim steps 8 times per tick), the host passes the substep states to `substepOK` (each substep's x in `[min x x', max x x']`, its h at least `min h h' − sag`), and that assumption becomes checked: `substep_clear` / `never_hit_substeps` prove every substep that passes is above terrain + margin. For a continuous plant it remains an assumption.

`filter` (`Envelope/Filter.lean`), in either mode, passes the pilot's input whenever `escapeClear` certifies it (one worst-case tick under that input, then a worst-case escape from the box after it, clears terrain); otherwise it keeps a committed escape or commits one. So an escape hands control back as soon as the pilot's input is certified again (`passthrough`, `filter_escape`). The worst-case escape counts as done once it is past its delay, climbing at the guaranteed rate, and above the highest terrain from the box's leading edge to the end of the grid and beyond (`Terrain.maxAhead`, sound because `WellFormed` requires `0 ≤ vxMin`, so the aircraft only moves forward).

Trusted surface (read these to believe the statement): `Envelope/Terrain.lean` (`Terrain`, `cellOf`, `cellHeight`, `heightAt`), `Envelope/Params.lean` (`State`, `Mode`, `Params`, `perf`, `WellFormed`), `Envelope/Relation.lean` (`vzEsc`, `VEsc`, `vzFloor`, `VFloor`, `Allowed`), `Envelope/Spec.lean` (`TickClear`, `modeAt`, `appliedAt`, `NeverHits`, and `substepOK` for the substep theorems). The statement also mentions `filter` and `Init`, and through them the worst-case escape check (`Envelope/Escape.lean`); those need no review for meaning: `Init` only has to be satisfiable (`Envelope/Checks.lean` discharges it). `passthrough` proves the filter passes every input the escape check accepts; nothing proves the check accepts every input whose worst case is safe, so its strictness is only shown by the concrete examples. Assumptions outside Lean: the plant obeys `Allowed` (the monitor checks this), stays in the swept box within a tick (checked by `substepOK` for a substepping plant, assumed for a continuous one), and the terrain grid really bounds the terrain.

`make verify` builds it and prints the axioms of each main theorem (`Tools/EnvelopeAudit.lean`, which also lists the trusted surface).

## Layout

- `Vibecheck/` the verified core (core Lean only, no Mathlib).
- `Envelope/`: the performance-envelope filter and its theorem (core Lean only).
- `App/`, `Main.lean`, `c/shim.c`: SDL3 frontend. Lean runs `main` off the process main thread, but Cocoa needs the main thread, so the shim owns `main` and forwards SDL calls.
- `Jsb/`: fixed-point Lean port of JSBSim's c172p longitudinal model (unverified; not imported by `Vibecheck/`), with residual tooling in `sysid/` and `Tools/JsbResid.lean`.
- `JsbExact/`, `Tools/JsbExactResid.lean`, `jsbx/`, `c/jxmath.c`: offline bit-exact Lean port of JSBSim's c172p (see below; unverified, not imported by anything else).
- `VcFilter/`, `c/vcfilter.h`, `c/filter_abi.c`: the safety-filter C ABI (`docs/filter-interface.md`) with the envelope filter behind it (`make filter-lib`; mappings in `docs/vcfilter-envelope.md`).
- `host/`: Python host for the C ABI: conformance tests and a JSBSim lockstep run (`make filter-test`).
- `Tools/`: `simtest` / `filtertest` headless runs, `Audit.lean`.
- `proofs/`: the Mathlib fidelity package above.
- `problems/`: open problems with checkable goals, for semi-independent work (start with `problems/robust-safety/`).
- `sysid/`: unverified Python experiments against JSBSim (residuals, tube widths).

## JsbExact: JSBSim's C172 in Lean, bit for bit (offline tooling)

`JsbExact.step` reproduces one `FGFDMExec::Run` (dt = 1/128 s) of JSBSim 1.3.3's `c172p` with identical IEEE doubles: 6-DOF (quaternion attitude in ECI, WGS84 gravity, Earth rotation, Adams-Bashforth integrator histories), the aerodynamics and FCS, the IO-320 engine and fixed-pitch propeller, fuel burn with CG and inertia updates, and the landing gear with JSBSim's friction solver. It is written over a `Scalar` class whose only instance is `Float`.

It is offline tooling, not a runtime safety filter, and no theorem depends on it. Intended uses: a target for future interval-based proofs that the model satisfies the envelope filter's one-tick bounds (`Envelope/`), measuring envelope parameters, and a ground-truth lockstep harness.

Limits: no flap kinematic (flaps retracted), no gusts or turbulence (constant wind from the initial condition), engine temperatures skipped, no initial-condition or trim port (state comes from a harness dump), flat terrain for the gear.

Compiler effects reproduced: fused multiply-add sites (clang `-ffp-contract=on`) are written with `fma`; macOS clang's combined `sin`/`cos` (`__sincos_stret`) is reached through `c/jxmath.c`. Trusted for the `Float` instance: libm `fma` and `c/jxmath.c`. `JsbExact/C172Gen.lean` is generated; its constants are the bit patterns of JSBSim's loaded model.

Cost per step on an M-series Mac, measured with `jsbx ... bench`: about 6.8 us in the air, about 13 us on the ground (gear solver).

The Lean side needs no JSBSim source: `lake build JsbExact jsbx`. The comparison needs a harness dump; producing one is optional and needs `cmake`, a C++17 compiler and a pip `jsbsim==1.3.3` install (`python -m venv .venv && .venv/bin/pip install jsbsim==1.3.3`). The harness builds JSBSim v1.3.3 under the gitignored `ext/`:

```
git clone --depth 1 --branch v1.3.3 https://github.com/JSBSim-Team/jsbsim.git ext/jsbsim
cmake -S ext/jsbsim -B ext/build-on -DCMAKE_BUILD_TYPE=Release -DBUILD_DOCS=OFF -DBUILD_PYTHON_MODULE=OFF
cmake --build ext/build-on -j 6 --target libJSBSim && jsbx/build.sh on && mkdir -p ext/data
R=$(.venv/bin/python -c 'import jsbsim,os;print(os.path.dirname(jsbsim.__file__))')
ext/harness-on $R ext/data/bank bank 20 8000 3       # modes: level, rud0, bank, takeoff, land
.venv/bin/python -I jsbx/replay_pip.py ext/data/bank  # source build equals the pip binary bitwise
.venv/bin/python -I jsbx/gen_lean.py ext/data/bank.cfg.json $R/aircraft/c172p/c172p.xml JsbExact/C172Gen.lean
lake build jsbx && .lake/build/bin/jsbx ext/data/bank step   # also: tick (8 steps), free (open-loop episode), bench
```
