import SpecBridgeNative

/-! Axioms of the bridge from the city gate to `CitySafety.Safe`. Run: `lake env lean Tools/SpecBridgeAudit.lean`. -/

#print axioms CityGate.SpecBridge.cityGate_spec_safe_funnel_of
#print axioms CityGate.SpecBridge.cityGate_spec_safe_funnel
#print axioms CityGate.SpecBridge.initChecked
#print axioms CityGate.SpecBridge.startsSafe
#print axioms CityGate.SpecBridge.outputsInRange
#print axioms CityGate.SpecBridge.reach_corr
#print axioms CityGate.SpecBridge.not_crash_of_startClearB
#spec_surface CityGate.SpecBridge.cityGate_spec_safe_funnel_of in CityGate.SpecBridge
