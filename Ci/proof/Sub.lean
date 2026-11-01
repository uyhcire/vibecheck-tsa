import Ci.proof.Law

/-! ci-proof submission pieces. -/

namespace Ci.Proof
open Vibecheck Jsb Ci.Lawfirst

/-- The ci-proof law with lawfirst's empirical terminal set (reference only, not proved). -/
def lawEmp : Ci.Law :=
  { σ := Mem, name := "ciproof-emp", init := initP p1, step := step, inT := fun q => climbT q || recoverT q,
    enc := encM, dec := decM }

end Ci.Proof
