# Vibecheck TSA: a flight sim you can't crash

A side-view flight simulator whose entire core (aerodynamics, controls model, terrain, crash rules, autopilot and safety filter) is written in Lean 4, with a machine-checked guarantee:

> **No sequence of pilot inputs can crash the aircraft.** The filter only changes an input when keeping it would leave the safe set.

Try it: take off, then dive at the mountains, stall it, overspeed it. A verified filter steps in at the last possible moment, and gives control straight back. Press `F` to switch the filter off and see what would have happened.

```
make install   # elan + SDL3 (Homebrew) if missing, then builds
make run
```

Controls: `UP`/`DOWN` pitch, `W`/`S` throttle, `SPACE` brake, `F` filter on/off, `G` show escape path, `T` 2× speed, `R` restart, `P` pause, `H` help, `ESC` quit.

Joystick: plug in a HOTAS (tested: Thrustmaster T.Flight HOTAS One, base switch on **PC**) before or after launch. Stick pitches, the lever is the throttle, the trigger brakes; the keyboard keeps working. Other sticks: `VC_JOY_PITCH=<axis> VC_JOY_THR=<axis> make run` (SDL axis numbers). X-Plane setup for the same stick: [`hardware/hotas-one/`](hardware/hotas-one/).

JSBSim flying X-Plane: [`sidecar/`](sidecar/) runs a JSBSim model from the HOTAS and drives X-Plane 12 as the display.

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

## Layout

- `Vibecheck/` the verified core (core Lean only, no Mathlib).
- `App/`, `Main.lean`, `c/shim.c`: SDL3 frontend. Lean runs `main` off the process main thread, but Cocoa needs the main thread, so the shim owns `main` and forwards SDL calls.
- `Jsb/`: fixed-point Lean port of JSBSim's c172p longitudinal model (unverified; not imported by `Vibecheck/`), with residual tooling in `sysid/` and `Tools/JsbResid.lean`.
- `Tools/`: `simtest` / `filtertest` headless runs, `Audit.lean`.
- `proofs/`: the Mathlib fidelity package above.
- `problems/`: open problems with checkable goals, for semi-independent work (start with `problems/robust-safety/`).
- `sysid/`: unverified Python experiments against JSBSim (residuals, tube widths).
