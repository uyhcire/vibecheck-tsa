# Problem brief: certifying flight safety without long real-time rollouts

## The problem in one paragraph

The repo's flight sim has a Lean-verified safety filter: no sequence of pilot inputs can crash the aircraft. It works by simulating, every tick, a full escape maneuver (an autoland, up to ~1,500 ticks) from the predicted next state, and passing the pilot's input only if that simulated landing succeeds. That is sound only because the Lean model *is* the plant. To guard a realistic simulator (JSBSim/FlightGear), the filter must instead certify a **set** of possible next states, because the real next state is only known to lie within a disturbance box **D** of the model's prediction. Measurements so far show that propagating sets through long escape rollouts makes them too wide to be useful, and doing it every tick is expensive. **The open problem: a certificate of safety under a per-tick disturbance bound D that is cheap to check online, provably sound, and still lets the pilot fly.**

## What exists

- **Repo:** `uyhcire/vibecheck-tsa`, `main` (merged in PR #1).
  - `Vibecheck/Model.lean`: the 2D side-view dynamics, a deterministic `step : State → Input → State` on exact fixed-point numbers, with tick Δt = 1/16 s. Its state is x, h, vx, vz, the pitch unit vector (dx, dz), pitch rate q, elevator, fuel and phase. It covers lift with stall, drag, thrust, a rate-limited elevator, ground roll, touchdown limits, and an 8 m terrain clearance away from runways.
  - `Vibecheck/Spec.lean`: the `Certificate` structure (safe set, filter, and the proof obligations) and the generic theorem `never_crash`.
  - `Vibecheck/Filter.lean`, `Autoland.lean`, `Safety.lean`: the current rollout-based safe set and its proofs. The invariance proof uses only determinism: the next state's escape rollout is the tail of the one just checked.
  - `README.md` lists the trusted surface. `make verify` builds everything and audits axioms.
- **PR #2** (open): Mathlib proofs bounding how far each sim step can be from the idealized continuous dynamics.
- **Branch `eric/jsbsim-spike`** (local only so far): `sysid/` scripts that fly JSBSim's Cessna 172, fit models, measure residuals, and estimate tube widths.

## Measurements to start from

- **D, the per-tick residual** (JSBSim's actual next state minus the Lean model's prediction, vertical speed, m/s per tick, worst case):

  | Model | Worst case |
  | --- | --- |
  | Generic 2D model fitted to JSBSim | ~1.0 |
  | JSBSim's exact forces with 4 Euler substeps per tick (integration-only floor) | 0.034 |

  A separate effort is porting JSBSim's model and integrator into Lean, aiming for residuals near fixed-point rounding (about 1e-4). **Treat D as a parameter.**
- **Tube widths** from an unverified generator (`sysid/tvlqr_tube.py`): a time-varying LQR tracking controller around a nominal landing approach, with D at the integration floor. The worst case gives ±16 m height and ±5 m/s sink at touchdown, against 8 m clearance and 3 m/s sink limits. Width scales linearly with D. It already reaches ±6 m and ±3.7 m/s after 5 s, so shortening the horizon does not fix it. Pitch-rate residual dominates: it alone contributes ±6.3 m.
- **Residual structure:** the residual varies slowly (tick-to-tick correlation 0.97 for vx and vz, 0.88 for q). Modeling that as a bandwidth limit shrank tubes only about 30%.
- **Cost:** the current point rollout costs 2–10 ms per tick, against a tick budget of 62.5 ms.

## Goal, stated so it can be checked

Produce, for the existing 2D model and a disturbance bound D (a vector of per-component bounds on x, h, vx, vz, pitch, q), a value of a **robust certificate** with these fields:

```lean
structure RobustCertificate (D : Disturbance) where
  inS        : State → Bool                 -- may be replaced by a stateful filter, see below
  filter     : State → Input → Input
  init_sub   : ∀ s, Init s → inS s
  safe       : ∀ s, inS s → ¬ s.crashed
  admissible : ∀ s u, (filter s u).Admissible
  invariant  : ∀ s u d, inS s → d ∈ D → inS (perturb (step s (filter s u)) d)
  passthrough : ∀ s u, inS s → u.Admissible →
                  (∀ d ∈ D, inS (perturb (step s u) d)) → filter s u = u
```

It should come with a generic theorem `never_crash_robust`: for every pilot input sequence and every disturbance sequence inside D, the closed loop never crashes. A **stateful filter** is allowed, for example one that carries a committed tube or a precomputed table. In that case the certificate is over the augmented state, and the theorem must still be about the aircraft's state.

### Milestones and acceptance criteria

1. **M1: the spec.** `RobustCertificate`, `perturb`, the disturbance set, and `never_crash_robust`, proved, plus `example`s showing the hypotheses are satisfiable. Accepted when it builds with no `sorry` and `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
2. **M2: a certificate that avoids long online rollouts, at D = 0.** Accepted when all of these hold:
   - the per-tick online check costs **≤ 1 ms** on a recent Mac;
   - **coverage**, measured on a fixed random sample of states (to be shared with the brief, or drawn from flights of the current game), is at least **50%** of the current rollout-based safe set;
   - the proofs build and the axiom audit is clean.
3. **M3: D > 0.** Report coverage as a function of D for D = 0.25×, 0.5× and 1× the floor vector `[x 0.03 m, h 0.03 m, vx 0.027 m/s, vz 0.034 m/s, pitch 0.001 rad, q 0.014 rad/s]`. The largest D that keeps coverage ≥ 25% with a sound certificate is the headline number.
4. **M4: the plant as a parameter.** The certificate construction takes the plant step function as a parameter, so a ported JSBSim model can be swapped in later. Accepted when the construction is stated over an abstract `step` plus whatever hypotheses it needs, with the 2D model as one instance.

Across milestones, report:
- soundness (theorems and axiom audit);
- coverage;
- intervention rate on a fixed set of pilot input traces, including adversarial ones;
- online cost per tick.

### Rules

- `Vibecheck/Model.lean`, `World.lean`, `Fixed.lean` and `Spec.lean` are frozen; build alongside them, not by editing them. The escape controller, the certificate and any offline tooling are yours to design.
- Offline computation can be as heavy as needed, in any language, as long as its output is **checked in Lean** (an untrusted generator plus a verified checker is the intended split).
- No `sorry`, `native_decide`, new axioms, `implemented_by`, or `maxHeartbeats 0` in anything `never_crash_robust` depends on.

## Directions known so far (non-binding)

- **Committed tubes.** The filter stores a tube (one set per tick) and checks only one-step inclusions: each set, pushed one tick through an interval version of `step` and widened by D, must land inside the next set. Any generator may propose the tube. The proof does not need the set method to be monotone. The open question is width and per-tick cost.
- **An offline robust invariant set with an O(1) online check.** Represent the safe set as a union of cells and verify once, offline in Lean, that every cell's one-step interval image plus D stays inside the union and away from crash states. The online check is then a cell lookup. Dimensionality is the obstacle: the state has 8 dimensions. Translation invariance in x, terrain-relative coordinates, and a reduced state for the slow modes may help.
- **Lowering amplification.** Tube width is roughly the closed loop's amplification of per-tick nudges times D, which plays the role of a condition number. Pitch-rate errors dominate today. An escape controller that holds pitch attitude tightly and damps the slow speed–height oscillation, or one tuned to minimize worst-case amplification directly, should shrink tubes several-fold.
- **Funnels.** Precomputed funnels around a library of escape maneuvers (LQR-trees style), each with a verified robust invariance certificate, so the online step only checks membership in some funnel.
- **State-dependent bounds.** A residual bound that depends on the state is tighter, but must stay runtime-checkable. The integration floor measured so far does not shrink in gentle flight, so this is not a free win.

## Out of scope

The JSBSim port and residual measurement (in progress separately), 3D flight, and rendering.

## Coordination

- D values from the port will be shared as they come in.
- The certificate interface (M4) is the hand-off point: the port provides a `step` function; the certificate work provides a construction parameterized by it.
