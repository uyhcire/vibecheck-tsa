import Envelope.Escape

/-! The safety statement (trusted surface, with `Relation.lean`, `Params.lean`, `Terrain.lean`). -/

namespace Envelope
variable {ι : Type}

/-- Between `s.x` and `s'.x`, terrain + margin lies below both endpoint altitudes minus `sag`. -/
def TickClear (P : Params ι) (s s' : State) : Prop :=
  ∀ x, min s.x s'.x ≤ x → x ≤ max s.x s'.x →
    P.terrain.heightAt x + P.margin < min s.h s'.h - P.sag

/-- Mode carried into tick `n` of the closed loop with filter `flt` (free at the start). -/
def modeAt (flt : Mode → State → ι → Mode) (s : Nat → State) (pilot : Nat → ι) : Nat → Mode
  | 0 => .free
  | n + 1 => (flt (modeAt flt s pilot n) (s n) (pilot n)).advance

/-- Mode the filter applies during tick `n`. -/
def appliedAt (flt : Mode → State → ι → Mode) (s : Nat → State) (pilot : Nat → ι) (n : Nat) : Mode :=
  flt (modeAt flt s pilot n) (s n) (pilot n)

/-- Under filter `flt`, every envelope-obeying trajectory from an initial state clears every tick. -/
def NeverHits (P : Params ι) (flt : Mode → State → ι → Mode) : Prop :=
  ∀ (pilot : Nat → ι) (s : Nat → State), Init P (s 0) →
    (∀ n, Allowed P (appliedAt flt s pilot n) (s n) (pilot n) (s (n + 1))) →
    ∀ n, TickClear P (s n) (s (n + 1))

end Envelope
