# Lessons taken from `bcbf-city-flight`

The `bcbf-city-flight` branch (commit `7fa2a33`, `flight/`, Rust + macroquad) is a backup-CBF safety filter for a 3D light aircraft flying through a procedural city, with a test harness. It uses the same core idea as this repo's verified filter: simulate escape maneuvers forward and let the pilot through only while some escape still works.

This note lists what this repo plans to take from it. Each entry says:
- **What the branch does**, with the file;
- **Evidence**, quoted from `flight/README.md` or measured here;
- **Where it applies**: the JSBSim integration, the robust-safety problem (`problems/robust-safety/`), or a spec decision;
- **Status**: adopt, adapt, or not applicable.

**Review asks** flag statements about the branch that its author should confirm or correct.

## 1. When an escape counts as finished

- **What the branch does** (`flight/src/escape.rs`, `terminal`): an escape is valid once the aircraft has turned 360° and settled into a steady climbing helix (speed, bank and climb angle within tolerances), and the ground circle that helix repeats is clear at the current height. From then on it only gains height over the same ground, so it stays clear. The horizon is 40 s, predicted at 0.1 s steps.
- **Contrast with this repo:** escapes here run to a full stop on a runway, up to ~1,500 ticks at 1/16 s.
- **Why it matters:** in the robust-safety experiments (`sysid/tvlqr_tube.py`), the binding constraints were landing precision (touchdown sink rate) over long horizons. Worst-case tubes at the measured residual floor reach about ±6 m height and ±3.7 m/s vertical speed within 5 s, and level off around ±16 m and ±5 m/s at touchdown. A short climb-out escape only has to keep terrain clearance, so its tube may fit where a landing tube cannot.
- **Applies to:** robust-safety (which escape the certificate uses) and the JSBSim integration (which escapes the C172 filter flies).
- **Status:** adapt. Compare tube widths for a climb-out escape against a landing escape on the ported C172 model once that lands. Note the 2D sim currently requires landing because fuel is limited.
- **Review ask:** does the helix terminal check stay valid "forever" in the nominal model, given that the README says the robust (wind) variant clears one drifting lap only?

## 2. Committed plan (gatekeeper fallback)

- **What the branch does** (`flight/src/filter.rs`, `tick_p1`): each tick it checks "the pilot's command held for `T_LOOK` = 0.5 s, then an escape". A passing check becomes the committed plan. A failing check keeps flying the last plan that passed. Each tick it also re-checks the committed plan's remaining tail.
- **Contrast with this repo:** the filter here is stateless. It checks only one step of the pilot's input before the escape, and recomputes the escape from scratch when it overrides.
- **Applies to:** robust-safety. A stored, already-verified plan is the structure a robust certificate needs: one-step inclusion checks on a committed tube, without requiring the set method to be monotone.
- **Status:** adopt (it requires a stateful filter in the Lean certificate).

## 3. Accept new plans with extra margin, re-check with less

- **What the branch does** (`flight/src/escape.rs`, `EPS_ACC`; `world.rs`, `hc_acc`): new plans must clear an obstacle map one cell (5 m) wider than the re-check map, by 3 m extra. The committed plan is re-checked against the narrower map. Per the README, the gap absorbs predictor/plant differences (RK4 at 0.1 s versus 0.01 s: millimetres generally, about 1 m on pull-ups) and sampling-phase effects.
- **Applies to:** robust-safety.
- **Status:** adapt. Formally: if a plan clears by margin ε and the plan's clearance moves by at most L per unit of state perturbation along the plan, then any state within δ of the prediction keeps the plan valid when L·δ ≤ ε. L can be bounded with interval Jacobians along the one nominal plan, which may be much cheaper than propagating full tubes.

## 4. Blending instead of switching

- **What the branch does** (`flight/src/filter.rs`):
  - **Phase 1:** as the predicted margin falls from 40 m (`H_HI`) to 5 m (`H_LO`), the command slides from the pilot's toward the best escape's, with a decay limit on how fast it slides back.
  - **Phase 2** (after van Wijk et al.): picks the smallest blend factor β satisfying ḣ ≥ −α(h − 12 m), in closed form.
- **Evidence:**
  - **Phase 1:** active on 80% of ticks, with a command change of 0.07 per active tick.
  - **Phase 2:** active on 55% of ticks, with a command change of 0.28 per active tick.
- **Contrast with this repo:** the filter here switches between the pilot's input and the full autoland input.
- **Applies to:** a spec decision. The `passthrough` field of `Certificate` forbids changing an admissible input that keeps the plane safe, so a blending filter cannot satisfy it as stated.
- **Status:** open. Adopting blending means weakening `passthrough`, for example to "untouched while the margin is at least H".

## 5. Clearance map for 3D terrain and buildings

- **What the branch does** (`flight/src/world.rs`):
  - terrain and about 2,100 building boxes go into one 5 m max-height grid;
  - the grid is widened sideways by 3 cells and raised by 10 m, and off-map counts as a wall;
  - each path segment is checked against every cell it crosses (`swept_max`), so the check covers the continuous path, at a cost independent of the building count;
  - collisions in the simulation are judged against the true geometry, never the widened map.
- **Applies to:** the JSBSim integration. The same grid could serve as the Lean spec's terrain and as JSBSim's ground-elevation feed.
- **Status:** adopt. Keep the grid simple enough to review, since it would be part of the trusted spec.

## 6. Test harness with pass/fail checks

- **What the branch does** (`flight/src/harness.rs`, `flight/src/pilot.rs`):
  - **Episodes:** 200 runs of 60 s from random starts inside the safe set, with nose-down-biased random pilots and a kamikaze autopilot in a quarter of them. Every configuration uses the same seeds.
  - **Metrics:** crashes, "invariant violations" (ticks where no verified escape exists; see review ask 2), minimum true clearance, share of ticks with the filter active, share of ticks flying the committed plan, and ms per tick. Kamikaze endurance runs last 300 s.
  - **Failure:** it exits non-zero if an acceptance check fails.
- **Contrast with this repo:** proofs cover soundness, but nothing measures intervention rate, smoothness or cost systematically. The robust-safety brief's coverage metric needs the same machinery.
- **Applies to:** the JSBSim integration (a lockstep harness against JSBSim) and robust-safety (coverage and intervention metrics).
- **Status:** adopt.

## 7. Model mismatch as a measured quantity

- **What the branch does** (`flight/src/model.rs`, `Params::mismatch`): a toggle adds wind and gusts and a weaker, slower aircraft:
  - 80% power;
  - 12% more parasite drag;
  - 1.5× slower load-factor, roll and throttle lags;
  - 80% roll rate;
  - 93% maximum lift.
- **Evidence:**
  - **Nominal filter under mismatch:** 9 of 200 episodes crash.
  - **With Phase 3 margins** (required clearance growing along the prediction by 1 m/s sideways and 0.25 m/s vertically): 2 of 200 crash.
- **Applies to:** robust-safety. It is independent evidence that heuristic margins reduce but do not eliminate failures under mismatch, consistent with the tube experiments here.
- **Status:** adopt the measurement practice. With JSBSim the aircraft mismatch is real rather than synthetic; wind and gusts can come from JSBSim's atmosphere model.

## 8. Speed

- **What the branch does:** 0.58 ms mean per tick single-threaded (README). Contributing techniques:
  - coarse 0.1 s prediction steps;
  - 40 s horizons;
  - abandoning a rollout once its running clearance drops below the best escape found so far (the `cutoff` argument);
  - trying the last successful escape first (`promote`).
- **Contrast with this repo:** 2–10 ms per tick.
- **Status:** adopt pruning and ordering; they do not affect soundness. Not applicable: a prediction step coarser than the plant's, because this repo's proof requires the predictor to equal the plant.

## Not taken

- **The 3D Dubins-style point-mass model** (`flight/src/model.rs`): the JSBSim C172 port is the realism target here.
- **The renderer:** out of scope for the verified core.
- **Phase 2's finite-difference ḣ** on a smoothed clearance: it suits a tested filter, not a proof.

## Review asks, collected

1. Is the nominal helix terminal condition (§1) intended to be clear forever, and what keeps tolerance-band drift from eventually leaving the checked circle?
2. Is the "invariant violation" metric (§6) exactly the ticks where `inv_ok = verified || tail_ok || fresh_ok` is false (no newly verified plan, the committed tail fails its re-check, and no fresh escape from the current state), and is that the intended invariant?
3. Are the Phase 1 versus Phase 2 smoothness numbers (§4) from the `--extended` harness run in the README?
4. Anything this note misses that the branch's author would consider the most important lesson.
