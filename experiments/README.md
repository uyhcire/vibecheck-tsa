# experiments: archived, superseded Lean proof work

Older Lean work from local branches that predate the ruling that safety means `CitySafety.Safe` (no reachable
closed-loop state of the real JSBSim aircraft, `JsbExact`, ever crashes; see `docs/safety-objective.md`). Each folder is
its own Lake project, pinned to the toolchain and dependency revisions its branch used, and is **not** part of the root
build or `make verify`. `make experiments` (slow) builds every folder and prints the axioms of the theorems each README
names.

Policy: no `sorry`/`admit` on main. Every archived project was checked to contain none (`grep` for `sorry`/`admit`
over each archived `.lean` file, and `#print axioms` on every named theorem shows no `sorryAx`). No file with `sorry` was
dropped or edited, because no unique Lean file on any listed branch contained one.

Nothing here upgrades any claim: each README states what its theorems do not say.

## Archived

| Folder | What it proves | Model | Superseded by | Builds | Axioms (named theorems) |
|---|---|---|---|---|---|
| [`ci-proof`](ci-proof/README.md) | Per-substep Lyapunov difference identity, decrease and composition lemmas (`StepLyap`, rung 2 of #30); PSD node forms, integer/real bridges, `static_box`; one-tick safe-and-climbing over a terminal set T (`tick_safe_climb`). `TInvariant lawT` itself is NOT proved (conditional theorems only). | Fixed-point longitudinal c172p port (`Fx`), flat ground | `CitySafety.Safe` on `JsbExact` | yes | `propext`, `Classical.choice`, `Quot.sound` |
| [`continuous-pilot`](continuous-pilot/README.md) | Interval enclosure of the model; one-tick escape property (vz up, vx down) on 5% and 10% boxes; a counterexample on the full region; a real-number vertical-acceleration clause and a conditional vz end theorem | Fixed-point longitudinal c172p port (`Fx`, interval and real instances) | `CitySafety.Safe` on `JsbExact` | yes | `propext`, `Classical.choice`, `Quot.sound` (counterexample: `propext` only) |
| [`envelope-3d`](envelope-3d/README.md) | 3D performance-envelope filter over a max-height grid never lets a tick hit the grid, if the plant obeys the envelope relation | Abstract rational-valued plant relation (`Allowed`) | `CitySafety.Safe` on `JsbExact` | yes | `propext`, `Classical.choice`, `Quot.sound` |
| [`safety-filter`](safety-filter/README.md) | A `SafetyFilter` interface (per-tick safety under a relational plant model) with the rollout and envelope filters as instances; rounding-direction lemmas | Point-mass models (autoland rollout; performance envelope) as relations | `CitySafety.Safe` on `JsbExact` | yes | `propext`, `Classical.choice`, `Quot.sound` (generic lemmas: none, or `propext`, `Quot.sound`) |

"Superseded by" is the same for all four: the objective changed, not just the method.

## Roadmap reuse (issues #30 and #36)

| Current step | Reusable piece |
|---|---|
| #30 rung 2 / #36 step 2 (contraction) | `ci-proof`: `StepLyap.lean` (`step_identity`, `step_decrease`, `compose_steps`, `recentre_le`), `PsdForm.lean`, and the negative findings in `ci-proof/log-proof-from-branch.md` (no per-frame norm contracts at the 1e-3 per-frame margin; slow-coordinate form rises inside a tick; Jacobian enclosures spread linearly with piece size) |
| robust or funnel invariance reduction | `ci-proof`: `Reduce.lean` (`tInvariant_of_lyap`, `inT_next_of_lyap`), `Bridge.lean`, LDLᵀ-certificate pattern in `NodePsd.lean`. The `eric/ansatz-*` branches have no Lean theorems; see below |
| sound enclosures of one tick of a plant | `continuous-pilot`: `Scalar`-generic model with interval instance, `Enc` paired-instance trick, `TickDecomp` |
| #36 step 4 (geometry / clearance over a height grid) | `envelope-3d`: comparison lemma and `substep_clear` (model-level) |
| turning a tick-level property into a per-frame one | `safety-filter`: `SubstepCheck` |

## Not archived

| Branch | Commit | Reason | What it attempted |
|---|---|---|---|
| `eric/conformance` | `4dcf8b0` | Subsumed: every Lean file is byte-identical to one in `continuous-pilot` | `Jsb` interval library and kernel-checked one-tick escape properties |
| `eric/continuous-pilot-decomp` | `eeda5c9` | Subsumed: every Lean file is in `continuous-pilot` (it lacks `ExpProofs/Continuous`) | `TickDecomp`: per-substep decomposition of one-tick vz/vx increments |
| `eric/ansatz-funnel` | `2768fb5` | No Lean theorem: the Lean addition is a Float probe executable (`Tools/FunnelProbe.lean`); the funnel result is an informal proof (`docs/ansatz/funnel.md`) with Python numerics (`sysid/funnel*.py`) on the branch | Rate-x4 funnel invariance with rounding, as informal proof and numerics |
| `eric/ansatz-envelope` | `8d41b93` | No Lean theorem: Float probe executables only (`Tools/EnvConf.lean`) | Conformance study of the commit-referenced envelope against the `Fx` escape |
| `eric/ansatz-slowfast` | `2d83e5a` | No Lean theorem: Float simulation (`Tools/SlowFastSim.lean`) and Python LP tables; negative result for the then-current escape law | Slow-fast certificate study (LP funnel tables and fast tubes) |
| `eric/ci-cegis` | `3e7fd42` | No theorem about the law: the unique Lean is an executable escape law and data tables (`Ci/cegis`, `Ci/cegis/lab`), `Ci.Audit.claimed` is empty; the shared referee scaffolding (`Ci.Goals`) is in `ci-proof` | Counterexample-guided search for a law and terminal set scoring well under the CI referee (final score 1.704) |
| `eric/ci-lawfirst` | `0b8a4a7` | Same: executable law, terminal-set data and harness only (`Ci/lawfirst`); no proof | Law-first design of an alpha-command escape law (iterations 1 to 7) scored by the referee |
| `eric/ci-wildcard` | `67730c2` | Same: executable law and terminal-set code only (`Ci/wildcard`); no proof | Load-factor-command escape law with a post-bottom climbing box (score 1.740 over 8 seeds) |
| `eric/ci-referee-reach` | `0bcb092` | No Lean proofs: referee code (reachability semantics `TSafeR`/`TInvariantR`, falsifier) is scoreboard infrastructure; `eric/ci-proof` includes the referee definitions its proofs import | Reachability-semantics version of the CI referee and a reachable input-program falsifier |
| `eric/jsb-interval` | `a22c738` | No theorem: a spike executable (`Tools/JsbIvSpike.lean`), "no soundness proof" by its commit message | Float-endpoint interval instance of `JsbExact.Scalar` with width and cost measurements |

These branches remain only as local branches; skipped content is not reproduced anywhere on main.
