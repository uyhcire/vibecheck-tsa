import GateSafety.ProofsR
import CityGate.Safety

/-! `city_safe` with the end-of-escape assumption restricted to the gate's own rollouts (`TermSoundR`). -/

namespace CityGate
open GateSafety

theorem city_safe_R (hT : TermSoundR cityGate Crash Init) : Safe cityGate Crash Init :=
  safeR cityGate Crash Init (fun x h => (cityGate_clear x h).elim fun e he => clear_sound e x.2 he) hT
    (fun _ h => h)

end CityGate
