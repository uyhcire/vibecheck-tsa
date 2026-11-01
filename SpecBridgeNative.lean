import CityGate.SpecBridge

/-! `InitChecked cityGate GInit` and the crash-freedom of the spec's starts by `native_decide`, and
`cityGate_spec_safe_funnel` without them. Trusts the Lean compiler and the C maths library (`jx_*`, the `jxmath` extern
library) for the 4 starts: its axioms add the auxiliary axioms `native_decide` creates to the standard three. -/

namespace CityGate.SpecBridge
open GateSafety

/-- The gate's initial check from each of the spec's 4 starts, after the first frame. -/
def startsChecked : Bool :=
  CitySafety.startConds.all fun c => cityGate.rolloutOK cityGate.horizon (cityGate.start (firstPlane c.state),
    firstPlane c.state)

theorem startsChecked_true : startsChecked = true := by native_decide

/-- **`InitChecked` holds**, by running the four rollouts compiled (`native_decide`). -/
theorem initChecked : InitChecked cityGate GInit := by
  intro pl ⟨s, ⟨c, hc, hs⟩, hpl⟩
  subst hs hpl
  have := startsChecked_true
  simp only [startsChecked, List.all_eq_true] at this
  exact this c hc

/-- The spec's 4 starts are crash-free (`startClearB`, run compiled). -/
def startsClear : Bool := CitySafety.startConds.all fun c => startClearB c.state

theorem startsClear_true : startsClear = true := by native_decide

theorem startsSafe : ∀ s, CitySafety.Init s → ¬ CitySafety.Crash cityMap s := by
  intro s ⟨c, hc, hs⟩
  subst hs
  have := startsClear_true
  simp only [startsClear, List.all_eq_true] at this
  exact not_crash_of_startClearB (this c hc)

/-- **The city gate is safe against the spec**, given the clearance test's soundness against the spec's crash (`hc`)
and the funnel assumption (`hF`, `FunnelSoundR`); trusts the compiler and libm for `initChecked` and `startsSafe`. -/
theorem cityGate_spec_safe_funnel (hc : ∀ e pl, clearAt e pl = true → ¬ GCrash pl)
    (hF : TermSoundR cityGate GCrash GInit) : CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_funnel_of hc hF initChecked startsSafe

end CityGate.SpecBridge
