# Findings: guarding JSBSim with a verified safety filter

Status as of 2026-10-31. This records what the experiments found and where the evidence lives, so the conclusions don't exist only in chat logs. Branches named `archive/*` hold finished experiments: their scripts and commit messages, not their data. Data was generated under `/tmp` and is reproducible from the commands in each branch.

## Settled definitions

- **Safe forever.** An escape maneuver ends safely in one of two ways:
  - **climb-out:** a steady climb from which the aircraft stays clear of every obstacle it can still reach, assuming fuel to keep climbing;
  - **landing:** the aircraft is stopped on landable ground (a runway, or any ground meeting the landability criteria).

  Each filter states which of the two its escapes use. Today `Envelope/` uses climb-out, and the toy sim (`Vibecheck/`) uses landing on a runway.
- **The toy 2D sim is its own world.** `Vibecheck/` (game, model, `never_crash`, the `proofs/` fidelity bounds) is self-contained and is not meant to track JSBSim.

## Aircraft models

| Model | Where | What it is | Gap to JSBSim (c172p) |
| --- | --- | --- | --- |
| Toy 2D model | `Vibecheck/Model.lean` | the game's own dynamics, fixed point | not a JSBSim model |
| Fixed-point longitudinal port | `Jsb/` (main) | c172p pitch-plane dynamics, JSBSim's integrators | worst per tick, rudder centred: vz 0.017–0.033 m/s (grows with data), vx ≈ 0.02 m/s |
| Bit-exact port | `JsbExact/` (branch `eric/jsb-exact`, PR pending) | full 6-DOF, engine/propeller, gear, `Float`, generic over a scalar class | **0**: bitwise equal on every compared step, tick and open-loop flight (5 datasets incl. banked turns, takeoff, landing) |

`JsbExact` is the single detailed model going forward. `Jsb/` will be retired once conformance work moves to `JsbExact`.

Why the fixed-point port differs from JSBSim (`archive/exp-vzjump` 43f15ae, `archive/exp-turns` 90165e0):
- **Lateral state omitted.** It dominates the gap. Feeding the measured bank and sideslip cuts worst-case vz from 0.0166 to 0.0020 m/s per tick.
- **Large jumps are real dynamics.** They come from sideslip near the stall break, not from a logging error. The input-pairing audit was clean.
- **Turns.** Up to 15° of bank, the extended port (measured bank, sideslip, rates, side force) stays near the wings-level gap; by 45° the gap is 2–4× larger.
- **Weight and balance.** The model fixes mass, balance and pitch inertia, so a 75 lb weight change already exceeds D, and loaded flights are about 20× worse (`archive/exp-dstab` 86b7250).

## Bounding the gap (D) is not stable

From `archive/exp-dstab` 86b7250: 1,200 random-pilot flights, 773k ticks.
- **The maximum keeps growing.** Worst-case vz grows from 0.017 (40 flights) to 0.033 (1,200 flights). Pitch-rate and pitch-angle errors have heavy tails.
- **The p99 rule fails.** A per-tick p99 bound lapses on about 20% of flights regardless of data volume.
- **D = maximum works only with margin.** With D at the maximum from n calibration flights, held-out flights lapse at roughly 1/n. A 2× margin over 600 flights gives about 0.02%.
- **Conclusion:** a guarantee conditioned on "gap ≤ D every tick" needs margin, and mass/balance as model inputs. With `JsbExact` the gap against JSBSim is zero, which removes this problem for that model.

## Robust tubes (worst-case disturbance every tick)

Untrusted linear or zonotope tubes, mostly on the 2D proxy model:
- **Landing escapes fail completely** (`archive/exp-touchdown` 10f500b). At the full D, worst-case touchdown sink spread is about ±7.5 m/s against a 3 m/s limit. At 0.25×D it is 1.1 m/s, but the escapes then need more elevator rate and throttle than exist. Zero starts certify.
- **Climb-out on the C172 port is weak** (`archive/exp-robust` 1091aa7):
  - only 9.6% of start states with a working nominal escape get a certified tube at D (bar was 50%);
  - at half of D the linear tube covers 99.8%, but the sampled linearisation remainder drops coverage to about 15%;
  - control margin (throttle 0.8, 60% of elevator rate) is mandatory: without it, nothing certifies;
  - plan generation costs about 0.33 s; the per-tick check costs about 0.13 ms.
- **The worst-case-every-tick disturbance is far harsher than reality.** The real gap is smooth (tick-to-tick correlation ≈ 0.98), small in gentle flight, and partly correctable by feedback. A measurement in escape regimes with a state-dependent, bias-plus-fast model is running on branch `eric/exp-realistic-d`.

## The performance-envelope filter

`Envelope/` (merged, PR #7), after ACAS X, Auto-GCAS and ModelPlex:
- **What is proved:** no terrain contact for any trajectory satisfying a one-tick envelope relation. The monitor is exactly that relation; the filter hands control back, accepts substep checks, and looks only at terrain ahead.
- **Known flaw:** the escape-phase bounds compound per tick. With fitted C172 numbers, the worst case loses about 2,000 m of altitude where real escapes lose tens of metres. Fix: bound the escape relative to the state at commit. This is being designed in `Envelope3D/` (branch `eric/envelope-3d`) and will be carried back to 2D.
- **`vMin` is both the start gate and the airspeed floor.** Nose-high starts (vz > 5 m/s) bleed below their start speed, so `Init` should exclude them.

## Runtime cost policy

The runtime filter is the cheap closed-form envelope check plus the per-tick monitor. Detailed simulation (`JsbExact`) is used offline only:
- conformance proofs (via an interval instance of its scalar class);
- envelope measurement;
- a ground-truth lockstep harness.

## Where things are

| Topic | Location |
| --- | --- |
| Problem brief for robust certificates | `problems/robust-safety/README.md` |
| Filter interface design | `docs/filter-interface.md` |
| Lessons from `bcbf-city-flight` | `notes/lessons-from-bcbf-city-flight.md` |
| Residual and tube scripts | `sysid/` (main); experiment variants on `archive/*` |
