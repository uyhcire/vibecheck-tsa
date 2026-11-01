import CityGate

/-! Axioms of the city gate theorems. Run: `lake env lean Tools/CityGateAudit.lean`. -/

#print axioms CityGate.city_safe
#print axioms CityGate.clear_sound
#print axioms CityGate.frameOut_fst
#print axioms CityGate.clearAt_eq_fast
#print axioms GateSafety.Gate.chooseR_eq
