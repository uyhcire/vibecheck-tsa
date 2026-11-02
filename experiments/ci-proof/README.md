# ci-proof: terminal-set invariance for an escape law on the fixed-point longitudinal model (archived experiment)

**Status: archived, superseded, and incomplete.** The headline goal of this work (`TInvariant lawT`) was never proved.
It is not a result about `CitySafety.Safe` (see `docs/safety-objective.md`: no reachable closed-loop state of the real
JSBSim aircraft, `JsbExact`, ever crashes). Nothing here is used by `make verify` or the root build.

## Source

- Branch `eric/ci-proof`, commit `38d2491` (59 commits ahead of the merge base with main). The branch's own proof log is
  copied verbatim as `log-proof-from-branch.md` (it mentions `sorry`s only in historical lines; the tip has none).
- Not archived from the branch: the Python numerics (`Ci/proof/py`), the unverified Lean prototypes in
  `Ci/proof/harness/` (affine-arithmetic and interval-Jacobian experiments, "inconclusive" per the log), the referee
  executables and scoreboard (`Ci/Report`, `Ci/Bench`, ...), and the Float tools.

## Original objective and model

- **Objective (then):** an *escape law* `lawT` together with a *terminal set* T (`lawT.inT`) such that `TInvariant`
  holds (`Ci.Goals.TInvariant`): from every state in T, one tick (8 substeps of 1/128 s) is safe at every substep and
  climbing, and the end state is again in T. Safe (`Ci.safeOk`) = angle of attack at most atan 0.28, load factor at most
  3.8 g, airspeed at least 27 m/s, stall flag clear, height between 5 m and 6000 m above flat terrain at h = 0.
  Climbing = at every substep either vz at least 2 m/s and h rising, or h at least 2500 m.
- **Model:** `ExpJsb.Model` on `Fx`, the Q16.16 longitudinal (wings level, no sideslip) c172p port; flat ground; the law
  is `Ci.Proof.lawT` (an integer program with a memory `Ci.Lawfirst.Mem`), T is a 7-dimensional Lyapunov ellipsoid on
  slow coordinates around the climb manifold plus slaved fast-coordinate tolerances, altitude band 10 to 2680 m.
- **Superseded by:** `CitySafety.Safe` on `JsbExact`; terminal sets and escape laws are, per `docs/safety-objective.md`,
  design choices inside a proof of `Safe`, not the objective.

## Main theorems (module names carry the `Exp` prefix where the original was `Jsb`, `Vibecheck` or `Proofs`)

Core-only part (`Ci/proof`, kernel-checked interval cells; 267 cells of 10 m):

| Theorem | In words |
|---|---|
| `Ci.Proof.SafeIv.tick_safe_climb` | From every state in T, the tick of `lawT` passes `safeOk` at all 8 substeps and climbs, on the `Fx` model. |
| `Ci.Proof.SafeIv.tick_band_h`, `band_next` | The tick's end state keeps h in T's altitude band, and passes `bandOk` (band, stall flag, stored alpha command bounded). |
| `Ci.Proof.tInvariant_of_tickInT` | `TickInT` (the tick maps T into T) implies `TInvariant lawT`. Conditional: `TickInT` is the open obligation. |
| `Ci.Proof.s1000_in`, `s1000_fast_out` | T is non-empty (a concrete climb-manifold state at 1000 m is in it) and rejects a state 1 m/s too fast. |
| `Ci.Goals.tSafe_of_tInvariant` | `TInvariant L` implies `TSafe L` (generic referee reduction). |

Mathlib part (`ExpProofs/CiProof`):

| Theorem | In words |
|---|---|
| `step_identity` | **Per-substep Lyapunov difference identity.** For symmetric `P`: `V(x + h d) = V(x) + 2 h <x, P d> + h² V(d)`, with `V(x) = xᵀPx`. |
| `step_decrease` | If `<x, P d> ≤ -λ V(x) + β` and `V(d) ≤ γ` then `V(x + h d) ≤ (1 - 2 h λ) V(x) + 2 h β + h² γ` for `h ≥ 0`. |
| `compose_steps` | `V_{k+1} ≤ a V_k + b` for `k < N` gives `V_N ≤ a^N V_0 + b Σ_{k<N} a^k`. |
| `recentre_le`, `contract_step` | Recentring costs at most `√V(c)`; one-step contraction of a PSD seminorm ball with additive remainder. |
| `tInvariant_of_lyap`, `inT_next_of_lyap` | Generic reduction of invariance of a Lyapunov-sublevel terminal set to pointwise obligations (hin/hout integer-real bridges, side conditions, an affine enclosure `A z + e` with `ρ² P - Aᵀ P' A ⪰ 0`). |
| `Skel.P_psd` | Each of the 28 node forms of T is positive definite (exact LDLᵀ certificates by `ring` and `positivity`), so the altitude-interpolated form is PSD. |
| `Skel.bridge_in`, `bridge_out` | The integer test `quadOk` agrees with the real form up to the floors in the altitude interpolation. |
| `Skel.static_box` | `bandOk ∧ quadOk ∧ fastOk → boxOk` (378 LDLᵀ certificates plus 267 kernel-checked cells). |
| `Skel.tInvariant_of_dynamics`, `tInvariant_of_fast_enc` | `TInvariant lawT` follows from: side conditions at the image, and an affine enclosure of the tick in the 7 slow coordinates with a contraction certificate (the latter also needs only `fastOk` at the image). |

## What it does NOT say

- **`TInvariant lawT` is not proved.** `Skel.tInvariant_of_dynamics` / `tInvariant_of_fast_enc` are conditional; their
  dynamics hypotheses (`henc`, and `fastOk` at the image) were never discharged. The branch's log records why: composed
  one-tick enclosures wrap through the stored-derivative feedback loop; a per-substep decrease of the slow-coordinate form
  fails (it rises inside 58% of sampled ticks) and the right object is a periodic family of forms that includes the held
  command, feasible numerically at rho 0.999 per substep but blocked by Fx rounding (about 5.5x the per-substep margin)
  and by entrywise Jacobian enclosure spread. All of that is numerical and unverified.
- `step_identity`, `step_decrease`, `compose_steps` are generic lemmas about quadratic forms. They say nothing about any
  plant until pointwise bounds on `<x, P d>` and `V(d)` are supplied, and for this model no such form was found.
- Nothing about `JsbExact`, JSBSim itself, terrain other than flat ground, or crashes; the plant is the Lean `Fx` port,
  longitudinal only.
- `tick_safe_climb` is one tick from T; it is not safe-forever without the open `TickInT`.

## Assumptions

- Lean kernel evaluation (`decide +kernel`) of the interval cells and tables; Mathlib `v4.35.0` for `ExpProofs`.
- No `sorry`, no `native_decide`, no new axioms (audit below).

## Roadmap reuse (issues #30, #36)

- `step_identity`, `step_decrease`, `compose_steps`, `recentre_le` (`ExpProofs/CiProof/StepLyap.lean`, 49 lines on
  `PsdForm.lean`, Mathlib only): **rung 2 of #30 / step 2 ("Contraction") of #36**, the n-dimensional per-substep
  Lyapunov difference identity that `docs/termsound/rung1.md` already points at (`q_robust_step` generalises with the
  n-dimensional `PsdForm`/`StepLyap` lemmas).
- `PsdForm.lean`, `Reduce.lean` (`inT_next_of_lyap`): the reduction from a contraction certificate to invariance of the
  sublevel set; reusable for any robust-invariance step (#36 steps 2 to 3).
- `NodePsd.lean`/`StaticCert.lean`: LDLᵀ certificates closed by `ring` and `positivity` (reusable pattern for "Q is
  positive definite" at #36 step 2). Per-cell kernel theorems, one per file chunk (a single `decide` ran out of memory).
- The log's negative findings (rows on the periodic form, Jacobian spread) are the same "per-frame margin about 1e-3,
  no per-frame norm contracts" observation recorded in #36 step 2.

## Build and audit

```
cd experiments/ci-proof
lake exe cache get
lake build
lake env lean Audit.lean
```

Build recorded when archiving: `lake build` succeeded (9109 jobs, about 19 minutes with a cold Mathlib build tree, `nice -n 10`; the interval-cell kernel theorems take a few minutes of that), Lean `v4.35.0`, Mathlib `56a0058` as pinned in `lake-manifest.json`.

## `#print axioms` output

```
'ExpProofs.CiProof.step_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.step_decrease' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.recentre_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.compose_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.contract_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.tInvariant_of_lyap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.inT_next_of_lyap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.P_psd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.bridge_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.bridge_out' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.static_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.tInvariant_of_dynamics' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExpProofs.CiProof.Skel.tInvariant_of_fast_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Goals.tSafe_of_tInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.SafeIv.tick_safe_climb' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.SafeIv.tick_band_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.SafeIv.band_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.tInvariant_of_tickInT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.s1000_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ci.Proof.s1000_fast_out' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Layout: `ExpVibecheck/Fixed.lean` and `ExpJsb` (the branch's copies; `Jsb` differs from main's), `Ci` (referee
scaffolding subset the proofs import: `Goals`, `Rules`, `Interface`, `Init`, `lawfirst/`, plus `Ci/proof`), `ExpProofs/CiProof`
(the branch's `proofs/Proofs/CiProof`). Module roots `Vibecheck`, `Jsb`, `Proofs` were renamed with an `Exp` prefix by a
word-level substitution; nothing else was edited. `Ci` is new relative to main and kept as is.
