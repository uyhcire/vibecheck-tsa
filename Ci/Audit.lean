import Ci.Agent
import Ci.Goals
import Ci.proof.SafeCells

/-! Competitor-owned: theorems claimed as proved, e.g. `Ci.Goals.TSafe` or `Ci.Goals.TInvariant` of a law.

`tick_safe_climb` is the one-tick safety and climb half of `TInvariant Ci.Proof.lawT`; it earns nothing on its own
(listed as "other"), the invariance half is still open (see `docs/ci/log-proof.md`). -/

namespace Ci.Audit

def claimed : List Lean.Name := [``Ci.Proof.SafeIv.tick_safe_climb]

end Ci.Audit
