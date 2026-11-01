import Ci.proof.SafeProof

/-! The per-cell interval check (`cellOk`); the kernel evaluates it in `Ci/proof/SafeCells*.lean`, one theorem per
cell so that each kernel call stays small. -/

namespace Ci.Proof.SafeIv
open Vibecheck Jsb Ci.Lawfirst

/-- Bisection weights: every coordinate but x, h and the stall bit, normalised by the box's own widths, sin θ (dz)
ten times as heavy (it drives the α margin, the binding check near the level-off altitude). -/
def dimsOf (B : CLOf Iv) : List (Nat × Int) :=
  (List.range 20).filterMap fun i =>
    if i == 0 || i == 1 || i == 11 then none else
    let w := width (B.get i)
    if w ≤ 0 then none else some (i, (if i == 5 then 10 else 1) * 1000000000000 / w)

def cellOk (i : Nat) : Bool := checkRec ok [] (dimsOf (cellBox i)) 22 (cellBox i)

end Ci.Proof.SafeIv
