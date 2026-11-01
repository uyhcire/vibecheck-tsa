import CityGate.SpecBridge

/-! `InitChecked cityGate GInit` by `native_decide`, and `cityGate_spec_safe_R` without it. This file trusts the
Lean compiler and the C maths library (`jx_*`, via the `jxmath` extern library) for these four rollouts: its
axioms add the auxiliary axiom `native_decide` creates for `startsChecked_true` to the standard three. -/

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

/-- **The city gate is safe against the spec**, assuming only `TermSoundR` and `AirframeNear`; trusts the compiler
and libm for `initChecked`. -/
theorem cityGate_spec_safe_native {h : Rat} (hh : h ≤ 17 / 2) (hT : TermSoundR cityGate (CrashH h) GInit)
    (hNear : AirframeNear h) : CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_R hh hT initChecked hNear

end CityGate.SpecBridge

#print axioms CityGate.SpecBridge.cityGate_spec_safe_native
