import CityGate.EndSets
import Spec.EndSetsExamples

/-! Axioms of the end-set geometry and interface. Run: `lake env lean Tools/EndSetsAudit.lean`. -/

#print axioms CitySafety.EndSets.Helix.clear
#print axioms CitySafety.EndSets.Ray.clear
#print axioms CitySafety.EndSets.Helix.not_crash
#print axioms CitySafety.EndSets.Ray.not_crash
#print axioms CitySafety.EndSets.Helix.geo_of_geoB
#print axioms CitySafety.EndSets.Ray.geo_of_geoB
#print axioms GateSafety.EndSet.safeForever
#print axioms GateSafety.EndSet.termSoundR
#print axioms CityGate.EndSets.Helix.not_crashH
#print axioms CityGate.EndSets.Ray.not_crashH
#print axioms CityGate.EndSets.cityGate_spec_safe_of_endSet
#print axioms CityGate.EndSets.cityGate_spec_safe_of_tubes
