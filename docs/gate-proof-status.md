# Proof status of the city gatekeeper filter

The gatekeeper filter (`flight/src/envfilter.rs`, `--env gate`; packaged as `libgate` in `gate/`) is tested, not
proved. This page separates what is exact, what is only checked numerically, and what is proved elsewhere in the
repository, and lists where a proof of the gate would start.

## What the gate claims and how it is supported

The claim: from a start where some escape verifies, the aircraft never hits terrain or a building, whatever the
pilot does. The filter keeps that invariant tick by tick: it accepts the pilot's command only if an escape verifies
after it, and otherwise flies the escape it verified on the previous tick.

| Part | Status |
|---|---|
| Rollouts: the aircraft the escapes are flown on | **Exact** with respect to `JsbExact`: each check forks the `JsbExact` state and steps it frame by frame, so a committed escape flies exactly the frames that were checked. `JsbExact` equals JSBSim 1.3.3's c172p bit for bit on every compared step of the validation datasets (`README.md`, JsbExact); that equivalence is measured, not proved. |
| Clearance along a rollout | **Numerical.** Clearance (body sphere plus wing capsule against exact boxes and the interpolated terrain) is evaluated every 8 JSBSim frames (1/16 s, about 3 m at 50 m/s) and must exceed 4 m there. Nothing bounds the clearance between samples; the margin is sized by testing. |
| "Safe forever" endings | **Numerical.** A straight escape ends when a climbing ray, in a corridor that widens with distance, clears the 2.5 m max-height raster until it is above the map's highest cell or off the map. A turning escape ends when its last 4 s fit a steady helix whose ground ring, widened for drift, is clear at the current height. Neither is a proof that the aircraft, flying on, stays on that ray or helix. |
| Map geometry | **Numerical.** The ring and ray tests read the 2.5 m raster; leaving the 6 km map counts as clear. |
| The filter's induction (always a verified escape) | **Argued in code comments, not formalised.** |
| The code | The filter and escape laws are Rust (`flight/`, `gate/`), outside Lean. Only `JsbExact` is Lean, and no theorem mentions it. |

Evidence instead of proof: `crashes` on 200 hostile episodes and 5 kamikaze scenarios (0 crashes, 198 verified
starts), `adversary` (0 crashes in 2,640 gap-guided flights), and `gatecheck` through `libgate` (0 crashes from 45
verified starts with raw-surface pilots, 20 with fly-by-wire pilots). See `flight/README.md` and `gate/`.

## What is proved elsewhere

- **On `main`: the envelope filter's no-hit theorem** (`Envelope.never_hit`, `Envelope/Proofs.lean`). For a plant
  that stays inside a performance envelope (`Allowed`, checked at run time by `monitor`), the envelope filter never
  lets the aircraft come within the margin of the terrain grid. It is longitudinal (distance along track and
  height), uses a worst-case escape rather than rollouts, and does not cover buildings or the 6-DOF aircraft.
- **Not on `main`: the longitudinal fixed-point model's referee and terminal-set proofs.**
  - `eric/ci-scoreboard`: the CI referee for filters on the fixed-point longitudinal model (`Jsb/`). It scores a
    filter's terminal set T, attacks it with a reachable falsifier, and audits Lean proofs of `Ci.Goals.TSafe` or
    `Ci.Goals.TInvariant` (T is invariant under the escape law, one tick at a time).
  - `eric/ci-proof` (`docs/ci/log-proof.md`): toward `TInvariant` for one law's T. Proved: every state in T has a
    safe, climbing tick (`SafeIv.tick_safe_climb`, kernel-checked over 267 cells); the image of a tick stays in the
    altitude band (`SafeIv.band_next`); the quadratic form is positive definite (`Skel.P_psd`); the integer and real
    forms agree (`Skel.bridge_in`, `Skel.bridge_out`); the slow-coordinate box follows from the band and form
    conditions (`Skel.static_box`); and `TInvariant` reduces to one remaining obligation (`tInvariant_of_tickInT`,
    `tInvariant_of_fast_enc`). Open: `TickInT`, that one tick maps T into T, which needs the fast coordinates at the
    image (`fastOk`) and an enclosure of the tick that contracts the form (`henc`).

## Where a proof of the gate would go next

1. **Enclose `JsbExact` over sets of states.** `JsbExact` routes every data-dependent branch through its `Scalar`
   class (#11) so that an interval instance can be sound. With that instance, one escape-law frame can be enclosed
   over a box of states, as `eric/ci-proof` does for the longitudinal model.
2. **Prove a terminal set invariant.** For the straight escape's climbing ray or a turning escape's helix, define T
   as a set of 6-DOF states around the settled climb and prove `TInvariant`-style that one frame (or tick) of the
   escape law maps T into T and keeps clear of the map. This replaces the numerical "safe forever" endings.
3. **Make the rollout checks sound.** Bound clearance between samples (for example, a speed bound times the sample
   interval, inside the margin), and prove the raster ring and ray tests conservative with respect to the exact
   boxes and terrain.
4. **Formalise the induction.** The gatekeeper's invariant (a verified escape always exists) and the hand-back rule,
   as `Envelope.never_hit` does for the envelope filter.
5. **Close the code gap.** Either port the escape law and checks to Lean, or check the Rust against a Lean reference
   by differential testing.
