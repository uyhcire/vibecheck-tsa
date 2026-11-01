import Ci.Baseline
import Ci.proof.T

/-! Competitor-owned: the submission the official score evaluates. -/

namespace Ci.Agent

def submission : Ci.Submission := { name := "ciproof", laws := [Ci.Proof.lawT], horizon := 640 }

end Ci.Agent
