# safety-filter: a `SafetyFilter` interface with the rollout and envelope filters as instances (archived experiment)

**Status: archived, superseded.** Not a result about `CitySafety.Safe` (see `docs/safety-objective.md`: no reachable
closed-loop state of the real JSBSim aircraft, `JsbExact`, ever crashes). Nothing here is used by `make verify` or the
root build.

## Source

- Branch `eric/safety-filter`, commit `564343f` (one commit on top of main's `5df737b`).

## Original objective and model

- **Objective (then):** the Lean side of `docs/filter-interface.md`: one structure, `Filters.SafetyFilter`, carrying
  the code that runs (`init`, `tick`, `monitor`), a plant model, the safety property and the guarantee theorem, so
  that different filters are swappable.
- **Model:** the plant is a *relation* `Allowed s c s'` (a deterministic plant is `s' = step s c`). Two instances:
  the rollout filter (`ExpVibecheck`'s point-mass autoland model, from `flight_never_crashes`) and the envelope filter
  (`ExpEnvelope`, point-mass performance envelope). Neither plant is JSBSim or `JsbExact`.
- **Superseded by:** `CitySafety.Safe` on `JsbExact` (a filter abstract over memory, with the plant fixed).

## Main theorems

| Theorem | In words |
|---|---|
| `Filters.SafetyFilter.guarantee` (field) | For every pilot input sequence and plant trajectory from an `Init` state, if the first `N` transitions obey `Allowed` under the commands the filter applied, those `N` ticks are `Safe`. |
| `Filters.SafetyFilter.always_safe`, `safe_while_monitored` | The unbounded-run form, and: safe as long as the runtime monitor accepts each observed transition. |
| `Filters.SafetyFilter.run_safe` | The runner that threads the filter state over an observed trace (a logged or live flight): every record of a run whose transitions all pass the monitor is a safe tick. |
| `Filters.rollout_guarantee`, `rollout_recovers_flight_never_crashes` | The rollout filter is an instance and `Vibecheck.flight_never_crashes` is recovered from it. |
| `Filters.envelope_guarantee`, `envelope_recovers_never_hit`, `envelope_recovers_never_hit_substeps` | The envelope filter is an instance; `Envelope.never_hit` and its substep form are recovered. |
| `Filters.SubstepCheck.safe_of_checks` | Along the closed loop, while transitions obey `Allowed` and the host-side substep checks pass, each substep is `SafeSub`. |
| `Filters.fxFloor_le`, `Filters.le_fxCeil` | Rounding a rational down (up) into the fixed-point type `Fx` gives a value at most (at least) the rational. |

## What it does NOT say

- Nothing about `JsbExact`, JSBSim or the city: every guarantee is conditional on the plant obeying `Allowed` for the
  stated number of ticks, and `Allowed` for the two instances is the point-mass model's relation.
- The interface fixes a per-tick `Safe` over consecutive states; it is not the reachability formulation of
  `CitySafety.Safe` and has no notion of the filter's memory being part of the reachable state.
- `Conversion` proves rounding direction only, not that a double produced by a host equals what a real plant did.

## Assumptions

- Core Lean only (no Mathlib). No `sorry`, no `native_decide`, no new axioms (audit below).
- Depends on vendored `ExpVibecheck` and `ExpEnvelope` (main's `Vibecheck/` and `Envelope/`, byte-identical at archive
  time, only renamed).

## Roadmap reuse (issues #30, #36)

- None of the proof content bears directly on #30 rungs or #36 steps. The `SubstepCheck` idea (a host-side check on
  substep states turning a per-tick property into a per-substep one) is relevant wherever a tick-level argument must be
  turned into the per-frame `Crash` predicate.

## Build and audit

```
cd experiments/safety-filter
lake build
lake env lean Audit.lean
```

Build recorded when archiving: `lake build` succeeded (30 jobs, about 2 minutes, `nice -n 10`), Lean `v4.35.0`, no dependencies.

Layout: `ExpVibecheck`, `ExpEnvelope` (vendored, renamed), `Filters` (the branch's, with references renamed).
`Audit.lean` is the branch's `Tools/FiltersAudit.lean` (it also prints `#spec_surface` lists, omitted below).

## `#print axioms` output

```
'Filters.rolloutFilter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.rollout_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.rollout_recovers_flight_never_crashes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.envelopeFilter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.envelope_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.envelopeSubsteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.envelope_recovers_never_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.envelope_recovers_never_hit_substeps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.SafetyFilter.always_safe' does not depend on any axioms
'Filters.SafetyFilter.safe_while_monitored' does not depend on any axioms
'Filters.SafetyFilter.run_safe' depends on axioms: [propext, Quot.sound]
'Filters.SubstepCheck.safe_of_checks' does not depend on any axioms
'Filters.fxFloor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Filters.le_fxCeil' depends on axioms: [propext, Classical.choice, Quot.sound]
```
