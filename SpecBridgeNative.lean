import CityGate.SpecBridgeNear

/-! `InitChecked cityGate GInit` and `AirframeNearInit 7` by `native_decide`, and `cityGate_spec_safe_native` without
them. Trusts the Lean compiler and the C maths library (`jx_*`, the `jxmath` extern library) for the 4 starts: its
axioms add the two auxiliary axioms `native_decide` creates to the standard three. -/

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

theorem startsNear_true :
    (CitySafety.startConds.all fun c => nearAtB 7 c.state (firstPlane c.state)) = true := by native_decide

/-- **`AirframeNearInit 7` holds**: at the 4 starts the airframe points lie within 7 m of the gate's start. -/
theorem airframeNearInit : AirframeNearInit 7 := by
  intro s ⟨c, hc, hs⟩
  subst hs
  have := startsNear_true
  simp only [List.all_eq_true] at this
  exact nearAt_of_B (this c hc)

/-- **The city gate is safe against the spec**, assuming only `TermSoundR` for the 7 m cube and
`AirframeNearGate 7`; trusts the compiler and libm for `initChecked` and `airframeNearInit`. -/
theorem cityGate_spec_safe_native (hT : TermSoundR cityGate (CrashH 7) GInit) (hNear : AirframeNearGate 7) :
    CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_R (by decide +kernel) hT initChecked (airframeNear_of airframeNearInit hNear)

/-- `cityGate_spec_safe_native` with `AirframeNearGate` reduced to the pose facts `PoseBounded`, `ReportMatchesObs`. -/
theorem cityGate_spec_safe_pose (hT : TermSoundR cityGate (CrashH 7) GInit) (hP : PoseBounded)
    (hR : ReportMatchesObs) : CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_native hT (airframeNearGate hP hR)

end CityGate.SpecBridge

#print axioms CityGate.SpecBridge.cityGate_spec_safe_native
#print axioms CityGate.SpecBridge.cityGate_spec_safe_pose
