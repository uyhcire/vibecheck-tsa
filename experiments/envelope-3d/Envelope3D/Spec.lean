import Envelope3D.Escape

/-! The safety statement (trusted surface, with `Relation.lean`, `Params.lean`, `Grid.lean`). -/

namespace Envelope3D
variable {ι : Type}

/-- Over the horizontal rectangle swept by the tick, obstacles + margin lie below both endpoint
altitudes minus `sag`. -/
def TickClear (P : Params ι) (s s' : State) : Prop :=
  ∀ x y, min s.x s'.x ≤ x → x ≤ max s.x s'.x → min s.y s'.y ≤ y → y ≤ max s.y s'.y →
    P.grid.heightAt x y + P.margin < min s.h s'.h - P.sag

/-- Host-side check for a substepping plant: each substep lies in the tick's swept rectangle, no
lower than `min h h' - sag`. -/
def substepOK (P : Params ι) (s s' : State) (subs : List State) : Bool :=
  subs.all fun p =>
    decide (min s.x s'.x ≤ p.x ∧ p.x ≤ max s.x s'.x ∧ min s.y s'.y ≤ p.y ∧ p.y ≤ max s.y s'.y ∧
      min s.h s'.h - P.sag ≤ p.h)

def modeAt (flt : Mode → State → ι → Mode) (s : Nat → State) (pilot : Nat → ι) : Nat → Mode
  | 0 => .free
  | n + 1 => (flt (modeAt flt s pilot n) (s n) (pilot n)).advance

def appliedAt (flt : Mode → State → ι → Mode) (s : Nat → State) (pilot : Nat → ι) (n : Nat) : Mode :=
  flt (modeAt flt s pilot n) (s n) (pilot n)

def NeverHits (P : Params ι) (flt : Mode → State → ι → Mode) : Prop :=
  ∀ (pilot : Nat → ι) (s : Nat → State), Init P (s 0) →
    (∀ n, Allowed P (appliedAt flt s pilot n) (s n) (pilot n) (s (n + 1))) →
    ∀ n, TickClear P (s n) (s (n + 1))

end Envelope3D
