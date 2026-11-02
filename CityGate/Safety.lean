import GateSafety.Proofs
import CityGate.Gate

/-! **The city gate is safe** (`docs/safety-objective.md`): from an allowed start, whatever surfaces and throttle the
pilot gives each JSBSim frame, the aircraft flown by `JsbExact` under `cityGate` never touches a building or the
terrain. The one assumption is that the gate's end-of-escape test means safe forever (`TermSound`). -/

namespace CityGate
open GateSafety

/-- Allowed starts: aircraft from which the gate's initial escape checks out. -/
def Init (s : Plane) : Prop := cityGate.rolloutOK cityGate.horizon (cityGate.start s, s) = true

theorem city_safe (hT : TermSound cityGate Crash) : Safe cityGate Crash Init :=
  safe cityGate Crash Init (fun x h => (cityGate_clear x h).elim fun e he => clear_sound e x.2 he) hT
    (fun _ h => h)

/-- Allowed starts on map `S`. -/
def InitOn (S : Site) (s : Plane) : Prop := (gateOn S).rolloutOK (gateOn S).horizon ((gateOn S).start s, s) = true

/-- **The city gate is safe on any map** `S` (for example San Francisco as the host passes it in, `siteOf`), with
crashes judged against `S`'s own geometry, under the same one assumption. -/
theorem site_safe (S : Site) (hT : TermSound (gateOn S) (CrashOn S.geo.map)) :
    Safe (gateOn S) (CrashOn S.geo.map) (InitOn S) :=
  safe (gateOn S) (CrashOn S.geo.map) (InitOn S)
    (fun x h => (gateOn_clear S x h).elim fun e he => clear_sound_on S.geo e x.2 he) hT (fun _ h => h)

end CityGate
