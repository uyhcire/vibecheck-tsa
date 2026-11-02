# envelope-3d: a 3D performance-envelope filter over a max-height grid (archived experiment)

**Status: archived, superseded.** Not a result about `CitySafety.Safe` (see `docs/safety-objective.md`: no reachable
closed-loop state of the real JSBSim aircraft, `JsbExact`, ever crashes). Nothing here is used by `make verify` or the
root build.

## Source

- Branch `eric/envelope-3d`, commit `d071e0b` (one commit on top of main's `5df737b`).
- Not archived: `Tools/City3D.lean` and the Rust city exporter it loads (executables that time `escapeClear` on the
  city grid; not proofs).

## Original objective and model

- **Objective (then):** extend the verified point-mass envelope filter (`Envelope/`, unchanged on main) to 3D flight
  over a 2D max-height grid (terrain and buildings), with a climb-out terminal mode and escape clauses bounded against
  the commit state.
- **Model:** an abstract plant given as a *relation* `Allowed` over a rational-valued state
  `(x, y, h, vx, vy, vz, bank)`: the plant may move between two states in one tick only if it obeys the performance
  envelope in `Params` (climb, pull, turn and bank limits per speed band, slack terms). It is not JSBSim and not
  `JsbExact`; whether the real aircraft obeys `Allowed` is not addressed.
- **Superseded by:** `CitySafety.Safe` on `JsbExact`.

## Main theorems

| Theorem | In words |
|---|---|
| `Envelope3D.never_hit3d` | For well-formed parameters, with the filter in the loop, every trajectory whose ticks obey `Allowed` under the filter's commands, from an `Init` state, has every tick `TickClear`: over the horizontal rectangle the tick sweeps, grid height plus margin stays below both endpoint altitudes minus `sag`. |
| `Envelope3D.never_hit3d_tick` | The single-tick form of the same invariant. |
| `Envelope3D.never_hit3d_substeps` | If a host-side `substepOK` check holds for each tick's substep states, each substep also clears. |
| `Envelope3D.substep_clear` | Substep states inside the tick's swept rectangle and no lower than `min h h' - sag` clear the grid. |
| `Envelope3D.comparison` | An escape obeying the envelope stays inside the worst-case boxes (the recurrence behind the filter). |
| `Envelope3D.escLoop_mono` | The escape check is monotone in the box, commit bounds and schedule. |
| `Envelope3D.passthrough` | A pilot input whose escape check passes is not overridden. |
| `Envelope3D.monitor_iff` | The runtime monitor equals `Allowed`. |
| `Envelope3D.Checks.neverTrigger_unsafe`, `climb_allowed`, `P0_wf` | Non-vacuity: a filter that never triggers is unsafe on a concrete example, a climbing turn is `Allowed`, and a concrete parameter set is well formed. |

## What it does NOT say

- Nothing about the real aircraft: all guarantees are conditional on the plant obeying `Allowed` every tick
  (`hA` in the theorems). Nothing links `Allowed` to JSBSim or `JsbExact`.
- `TickClear` is clearance against a grid abstraction (rectangle max of cell heights plus `margin`, minus `sag`), not
  the spec's `Crash`, and says nothing about states between ticks except through `never_hit3d_substeps`' host check.
- The parameters (`Params`) are inputs; only the concrete example in `Checks` is shown well formed, and no claim is made
  that it matches any real aircraft or the city grid.

## Assumptions

- Core Lean only (no Mathlib). Rational arithmetic. No `sorry`, no `native_decide`, no new axioms (audit below).
- Depends on the vendored `ExpEnvelope` (main's `Envelope/`, byte-identical at archive time, only renamed).

## Roadmap reuse (issues #30, #36)

- The comparison-lemma pattern (worst-case boxes recurring per commit state rather than compounding per tick) and
  `substep_clear` are candidates for the geometry step of #36 (step 4, funnel and clearance lemmas over a height
  grid), as a model-level argument; they would need re-stating over `JsbExact` residual bounds.

## Build and audit

```
cd experiments/envelope-3d
lake build
lake env lean Audit.lean
```

Build recorded when archiving: `lake build` succeeded (19 jobs, about 1 minute, `nice -n 10`), Lean `v4.35.0`, no dependencies.

Layout: `ExpEnvelope` (main's `Envelope/` minus its `Checks`; originally `Envelope`), `Envelope3D` (the branch's
files, unchanged apart from the rename). `Audit.lean` is the branch's `Tools/Envelope3DAudit.lean`, and also prints the
trusted-surface lists (`#spec_surface`).

## `#print axioms` output

```
'Envelope3D.never_hit3d' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.never_hit3d_tick' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.never_hit3d_substeps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.escLoop_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.passthrough' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.substep_clear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.monitor_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.Checks.neverTrigger_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.Checks.climb_allowed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Envelope3D.Checks.P0_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
```
