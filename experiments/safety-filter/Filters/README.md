# `Filters/`: one interface, two verified filters

`SafetyFilter` (`Interface.lean`) packages a filter's code (`init`, `tick`, `monitor`) with its plant model (`Allowed`, a relation), initial set (`Init`), per-tick safety predicate (`Safe`) and its theorem (`guarantee`): for every pilot input sequence and every trajectory from an initial state, if the first `N` transitions obey `Allowed` under the commands the filter applied, those `N` ticks are `Safe`. Swapping the filter swaps the guarantee. Design and differences from the original sketch: `docs/filter-interface.md`, section 3.

| file | contents |
| --- | --- |
| `Interface.lean` | `SafetyFilter`, `SubstepCheck`, `fstateAt`, `cmdAt` (trusted surface) |
| `Generic.lean` | `always_safe`, `safe_while_monitored`, `run` / `run_safe`, `SubstepCheck.safe_of_checks` |
| `Rollout.lean` | `rolloutFilter`: `Vibecheck.solution`, deterministic plant `s' = step s u`, from `flight_never_crashes` |
| `Envelope.lean` | `envelopeFilter P hP`, `envelopeSubsteps`: `Envelope.filter`, from the lemmas of `never_hit` |
| `Conversion.lean` | `ratOfBits` / `ratOfFloat` (exact double → `Rat`), `fxFloor` / `fxCeil` (directed rounding into `Fx`) |
| `Checks.lean` | hypotheses satisfiable for each instance, polymorphic use, rejection of a never-intervening filter, conversion examples |

To read a guarantee: `Interface.lean`, plus the instance's `State`, `Allowed`, `Init` and `Safe` (for the rollout filter, the Vibecheck trusted surface in the top-level README; for the envelope, its trusted surface there). `make verify` prints the axioms of every instance and generic theorem (`Tools/FiltersAudit.lean`).

## Number types at the boundary

- A filter reasons over exact `Rat` (envelope) or over its model's own type (rollout: `Fx`, an integer over 2¹⁶).
- A detailed model that computes in `Float` (the JSBSim port in `Jsb/`) is not reasoned about in `Float`; proofs about it go through an interval instance over `Rat`.
- The host's IEEE doubles are converted once, at the C boundary:
  - to `Rat` exactly: a finite double is a dyadic rational. `ratOfFloat` returns `none` for ±∞ and NaN. Checked against a reference encoding on examples (`decide`) and against `Float.toBits` by evaluation; that it is exact for every double is documented intent, since the kernel cannot evaluate `Float`.
  - to `Fx` conservatively: `fxFloor` for fields where lower is less favourable (height, fuel), `fxCeil` where higher is (sink rate, speed, rates). Both rounding directions are proved.
  - to an interval: a box around the exact value, widened by the sensor error.
