import CityGate.SpecBridgeNear

/-! `ReportMatchesObs` holds with gap 0: the gate's `exactPos` reads `CitySafety.report` exactly, as the spec does. -/

namespace CityGate.SpecBridge

theorem ratOf_zero : CitySafety.ratOf 0 = some 0 := by decide +kernel

theorem reportMatchesObs : ReportMatchesObs := by
  intro s ob mc _ c hc
  simp only [exactPos, planeOf, ratOf_zero, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hc
  obtain ⟨ly, hly, lz, hlz, hs, hhs, rfl⟩ := hc
  refine ⟨ly, lz, hs, hly, hlz, hhs, ?_, ?_, ?_⟩ <;>
    simp only [Bd, obsGap, Rat.zero_add, Rat.sub_self] <;> decide +kernel

end CityGate.SpecBridge
