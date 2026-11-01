import GateSafety.Proofs
import CityGate.Gate

/-! **The city gate is safe** (`docs/safety-objective.md`): from an allowed start, whatever surfaces, throttle and
brakes the pilot gives each JSBSim frame, the aircraft flown by `JsbExact` under `cityGate` never touches a building
or the terrain. Every escape the gate relies on is checked frame by frame until it reaches the landing funnel
(`inFunnel`); the one assumption, `FunnelSound`, is that from the funnel the escape (the autoland) lands safely. -/

namespace CityGate
open GateSafety

/-- Allowed starts: aircraft from which the gate's initial escape checks out (reaches the funnel clear). -/
def Init (s : Plane) : Prop := cityGate.rolloutOK cityGate.horizon (cityGate.start s, s) = true

/-- **The assumption**: an escape that has reached the landing funnel never crashes afterwards. With this file's
`Crash` (any contact, the 6 m cube) it cannot hold, because a landing touches the runway; it is meant for `Crash`
with the landing rule of `Spec/CitySafety` (wheels only, on the runway, within touchdown limits; the flight ends
when stopped), which the gate is being re-targeted to. -/
def FunnelSound : Prop := TermSound cityGate Crash

theorem city_safe (hF : FunnelSound) : Safe cityGate Crash Init :=
  safe cityGate Crash Init (fun x h => (cityGate_clear x h).elim fun e he => clear_sound e x.2 he) hF
    (fun _ h => h)

end CityGate
