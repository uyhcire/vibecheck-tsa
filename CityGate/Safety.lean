import GateSafety.Proofs
import CityGate.Gate
import CityGate.ClearSpec

/-! **The city gate is safe** (`docs/safety-objective.md`): from an allowed start, whatever surfaces, throttle and
brakes the pilot gives each JSBSim frame, the aircraft flown by `JsbExact` under `cityGate` never touches a building
or the terrain. Every escape the gate relies on is checked frame by frame until it reaches the landing funnel
(`inFunnel`); the one assumption, `FunnelSound`, is that from the funnel the escape (the autoland) lands safely. -/

namespace CityGate
open GateSafety

/-- Allowed starts: aircraft from which the gate's initial escape checks out (reaches the funnel clear). -/
def Init (s : Plane) : Prop := cityGate.rolloutOK cityGate.horizon (cityGate.start s, s) = true

/-- The spec's crash for the gate's aircraft: `CitySafety.Crash` on the demo map (only the wheels may touch, only the
runway, gently), of its plant state. -/
def SpecCrash (pl : Plane) : Prop := CitySafety.Crash cityMap pl.st

/-- **The assumption**: an escape that has reached the landing funnel never crashes afterwards (the autoland lands
it safely, in the spec's sense). -/
def FunnelSound : Prop := TermSound cityGate SpecCrash

/-- The gate's clearance test is sound for the spec's crash (`clear_spec_sound`). -/
theorem clearSound_spec : ClearSound cityGate SpecCrash :=
  fun x h => (cityGate_clear x h).elim fun e he => clear_spec_sound e x.2 he

theorem city_safe (hF : FunnelSound) : Safe cityGate SpecCrash Init :=
  safe cityGate SpecCrash Init clearSound_spec hF (fun _ h => h)

end CityGate
