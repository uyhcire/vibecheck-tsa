# continuous-pilot: one-tick escape properties of a fixed-point c172p model (archived experiment)

**Status: archived, superseded.** This is not a result about `CitySafety.Safe` (see `docs/safety-objective.md`: no
reachable closed-loop state of the real JSBSim aircraft, `JsbExact`, ever crashes). Nothing here is used by `make verify`
or the root build.

## Source

- Branch `eric/continuous-pilot`, commit `edf1152`.
- It contains, unchanged, the Lean content of `eric/conformance` (`4dcf8b0`, the `Jsb` interval library and the
  kernel-checked escape properties, without `TickDecomp`) and `eric/continuous-pilot-decomp` (`eeda5c9`, `TickDecomp`).
  Those two branches have no Lean file that is not in this folder (checked by file blob hash), so they are not archived
  separately.
- The `eric/ansatz-*` branches sit on top of this commit; their Lean additions are Float probe executables only (see
  `../README.md`).

## Original objective and model

- **Objective (then):** from every state in a box around a pulled-up climb, one 1/16 s tick of a fixed escape autopilot
  raises the vertical speed by at least 0.031 m/s and lowers the horizontal speed by at most 0.1 m/s ("`IncrProp`"),
  as a step towards "the escape law always climbs out".
- **Model:** `ExpJsb.Model`, a longitudinal (wings level, no sideslip) Lean port of JSBSim's `c172p`, generic over a
  `Scalar` class. Instances: `Fx` (Q16.16 fixed point, the one that runs), `Iv` (integer intervals) and `ℝ`
  (`ExpProofs/Continuous/RealModel.lean`, exact arithmetic, `Real.sqrt`, true `atan2`, piecewise-linear tables).
  It is a fitted model with its own rounding, not the bit-exact `JsbExact` port the current objective uses.
- **Superseded by:** `CitySafety.Safe` on `JsbExact`.

## Main theorems (module names carry the `Exp` prefix; originals are `Jsb`, `Vibecheck`, `Proofs`)

| Theorem | In words |
|---|---|
| `ExpJsb.Iv.mul_sound` (and the other `Iv.*_sound`) | Each interval operation encloses the `Fx` operation it mirrors. |
| `ExpJsb.tickAB_sound` | If the inputs of the model's 8-substep tick lie in intervals, the `Fx` result lies in the interval result. |
| `ExpJsb.region_sound` | If the kernel-evaluated bisection checker `checkRec` returns `true` on a box, `IncrProp` holds at every `Fx` closed-loop state in the box that satisfies the linear side constraints. |
| `ExpJsb.EscapeRegion.escape_box5`, `escape_box10` | `IncrProp` (vz up at least 2048 raw = 0.03125 m/s, vx down at most 6554 raw = 0.1 m/s per tick) holds on boxes covering 5% and 10% of the pulled-up-climb region, for the escape autopilot on `Fx`. |
| `ExpJsb.EscapeRegion.full_region_counterexample` | The property is false on the full region the interval route tried (a concrete state `cBad`). A negative result. |
| `ExpJsb.tick_dvz_lower`, `ExpJsb.incr_of_substeps` | The tick's vz increment is exactly a sum of the eight substeps' evaluated vertical accelerations (up to eight roundings), so a per-substep bound on the acceleration gives the per-tick bound. |
| `ExpJsb.Cont.au_lower` | Over `ℝ`: on an explicit region (`AuRegion`) of the escape climb, the model's vertical acceleration is at least 0.6 m/s^2. |
| `ExpJsb.Cont.dvz_of_bridge` | The vz half of `IncrProp` follows from `au_lower` plus two hypotheses per substep: the visited `Fx` states stay in `AuRegion` (drift) and one `Fx` evaluation of the acceleration is within `ε ≤ 0.01` of the real one (rounding). |
| `ExpJsb.Cont.sWit_region` | The region hypothesis is satisfiable (a concrete level climb-out state). |

## What it does NOT say

- Nothing about the real aircraft, JSBSim, `JsbExact`, terrain or buildings, or any crash. The plant is the Lean `c172p`
  port (`Fx`), longitudinal only.
- Not a safe-forever or invariance statement: only one 1/16 s tick, only from the stated boxes. `escape_box5/10` cover
  5%/10% of the region, not all of it.
- `dvz_of_bridge` is conditional: the drift and rounding hypotheses (`hdrift`, `hround`, `hF`, `h0`) are not
  discharged anywhere in this folder, and only the vz half is covered (no vx half).
- `au_lower` is about the real-number vector field, not the integer code; the link is exactly the unproved bridge
  hypotheses.

## Assumptions

- Lean kernel, `decide +kernel` evaluation of interval ticks (large `maxHeartbeats` on the `box10_*` theorems), Mathlib
  (`v4.35.0`) for `ExpProofs`.
- No `sorry`, no `native_decide`, no new axioms (audit below).

## Roadmap reuse (issues #30, #36)

- The `Scalar`-generic model with an interval instance, and the "paired instance" enclosure trick (`ExpJsb.Enc`,
  `kernel_rfl`), is a template for rung work that needs sound enclosures of one tick of a plant model; the target
  plant would now be `JsbExact`, not this `Fx` port.
- `TickDecomp` (increment as a sum of per-substep derivative evaluations) and `full_region_counterexample` (derivative
  fields as free box coordinates make the box unprovable) are reusable lessons for any per-substep argument (rung 2
  of #30). The Lyapunov identity itself is in `../ci-proof`.

## Build and audit

```
cd experiments/continuous-pilot
lake exe cache get
lake build
lake env lean Audit.lean
```

Build recorded when archiving: `lake build` succeeded (9072 jobs, about 14 minutes including compiling the Mathlib
dependency graph from cache, `nice -n 10`), Lean `v4.35.0`, Mathlib `56a0058` as pinned in `lake-manifest.json`
(copied from the branch's `proofs/lake-manifest.json` with the `vibecheck` path package removed).

## `#print axioms` output

```
'ExpJsb.Iv.mul_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.tickAB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.region_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.EscapeRegion.escape_box5' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.EscapeRegion.escape_box10' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.EscapeRegion.full_region_counterexample' depends on axioms: [propext]
'ExpJsb.tick_dvz_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.incr_of_substeps' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.Cont.au_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.Cont.dvz_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpJsb.Cont.sWit_region' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Layout: `ExpVibecheck` (the branch's `Vibecheck/`, byte-identical to main's at archive time, only renamed), `ExpJsb`
(the branch's `Jsb/`, which differs from main's `Jsb/`), `ExpProofs/Continuous` (the branch's `proofs/Proofs/Continuous`).
Every module root was renamed with an `Exp` prefix by a word-level substitution, and nothing else was edited.
