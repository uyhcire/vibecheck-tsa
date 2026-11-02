import CityGate.SpecBridgeObs
import CityGate.TermSkeleton
import CityGate.SafetyR

/-! Axioms of the bridge from the city gate to `CitySafety.Safe`. Run: `lake env lean Tools/SpecBridgeAudit.lean`. -/

#print axioms CityGate.SpecBridge.cityGate_spec_safe
#print axioms CityGate.SpecBridge.cityGate_spec_safe_R
#print axioms CityGate.city_safe_R
#print axioms CityGate.SpecBridge.outputsInRange
#print axioms CityGate.SpecBridge.airframeNearGate
#print axioms CityGate.SpecBridge.poseBounded_of
#print axioms CityGate.SpecBridge.reportMatchesObs
#print axioms CityGate.TermSkeleton.termSoundR_of
#print axioms CityGate.TermSkeleton.geo_clear_helix
#print axioms CityGate.TermSkeleton.geo_clear_ray
#print axioms CityGate.SpecBridge.reach_corr
#print axioms CityGate.SpecBridge.clear_soundH
#print axioms CityGate.SpecBridge.cityMap_terrain
#spec_surface CityGate.SpecBridge.cityGate_spec_safe in CityGate.SpecBridge
