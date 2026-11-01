import Ci.Baseline
import Ci.proof.Sub

/-! Competitor-owned: the submission the official score evaluates. -/

namespace Ci.Agent

def submission : Ci.Submission := { name := "ciproof", laws := [Ci.Proof.lawEmp], horizon := 640 }

end Ci.Agent
