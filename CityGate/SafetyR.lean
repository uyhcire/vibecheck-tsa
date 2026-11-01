import GateSafety.ProofsR
import CityGate.Safety

/-! `city_safe` with the end-of-escape assumption restricted to the gate's own rollouts (`TermSoundR`). -/

namespace CityGate
open GateSafety

theorem city_safe_R (hT : TermSoundR cityGate SpecCrash Init) : Safe cityGate SpecCrash Init :=
  safeR cityGate SpecCrash Init clearSound_spec hT (fun _ h => h)

end CityGate
