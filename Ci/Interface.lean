import Jsb.Model

/-! CI referee: the submission interface (scoreboard-owned; rules in `docs/ci/README.md`). -/

namespace Ci
open Vibecheck Jsb

structure Commit where
  s : State
  pilot : Input
  deriving Repr, Inhabited

structure Law where
  σ : Type
  name : String
  init : Commit → σ
  step : σ → State → Input × σ
  inT : State × σ → Bool
  enc : σ → Array Int
  dec : Array Int → Option σ

/-- `horizon` is in ticks of 1/16 s. -/
structure Submission where
  name : String
  laws : List Law
  horizon : Nat

/-- Physical limits: elevator in [-1, 1], throttle in [0, 1], sideslip and bank 0. -/
def clampInput (u : Input) : Input :=
  ⟨⟨max (-65536) (min 65536 u.elev.raw)⟩, ⟨max 0 (min 65536 u.thr.raw)⟩, ⟨0⟩, ⟨0⟩⟩

end Ci
