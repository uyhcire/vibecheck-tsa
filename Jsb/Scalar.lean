import Jsb.Math

/-! Scalar operations the c172p model uses, and the `Fx` instance that runs it. -/

namespace Jsb
open Vibecheck

class Scalar (α : Type) extends Add α, Sub α, Mul α, Div α, Neg α, Max α, Min α where
  /-- the constant with raw value `r` (value `r / 2^16`) -/
  lit : Int → α
  mulR : α → α → α
  shr : α → Nat → α
  ab3 : α → α → α → α
  abs : α → α
  sqrt : α → α
  atan2 : α → α → α
  tbl1 : Tbl1 → α → α
  tbl2 : Tbl2 → α → α → α
  /-- standard-atmosphere lookup (50 m spacing) in a raw table -/
  atm : Array Int → α → α
  selLt : α → α → α → α → α
  selLe : α → α → α → α → α
  /-- `mulR c (rnFactor c s)`: attitude renormalisation, a primitive so intervals can split `c` -/
  rnC : α → α → α
  rnS : α → α → α

/-- First-order unit-length correction factor `3/2 - (c^2 + s^2)/2`. -/
def rnFactor {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 2] [OfNat α 3] (c s : α) : α :=
  (3 : α) / 2 - (c * c + s * s) / 2

instance (priority := low) instOfNatScalar {α : Type} [Scalar α] {n : Nat} : OfNat α n := ⟨Scalar.lit ((n : Int) * 65536)⟩

/-- `a / 2^k` rounded to nearest. -/
def shr (a : Fx) (k : Nat) : Fx := ⟨(a.raw + (1 <<< (k - 1))) >>> k⟩

def atmLookup (tab : Array Int) (h : Fx) : Fx :=
  let span : Int := 50 * 65536
  let i := (floorDiv (max 0 (min (span * 159) h.raw)) span).toNat
  let f := max 0 (min span (h.raw - i * span))
  ⟨tab[i]! + (floorDiv64 (Int64.ofInt (tab[i + 1]! - tab[i]!) * Int64.ofInt f) (Int64.ofInt span)).toInt⟩

instance instScalarFx : Scalar Fx where
  add a b := ⟨a.raw + b.raw⟩
  sub a b := ⟨a.raw - b.raw⟩
  neg a := ⟨-a.raw⟩
  mul := fmul
  div := fdiv
  max a b := if a ≤ b then b else a
  min a b := if a ≤ b then a else b
  lit r := ⟨r⟩
  mulR := mulR
  shr := shr
  ab3 a b c := ⟨(23 * a.raw - 16 * b.raw + 5 * c.raw) / 12⟩
  abs := Fx.abs
  sqrt := sqrtFx
  atan2 := atan2Fx
  tbl1 := Tbl1.eval
  tbl2 := Tbl2.eval
  atm := atmLookup
  selLt a b t e := if a.raw < b.raw then t else e
  selLe a b t e := if a.raw ≤ b.raw then t else e
  rnC c s := mulR c (@rnFactor Fx ⟨fun a b => ⟨a.raw + b.raw⟩⟩ ⟨fun a b => ⟨a.raw - b.raw⟩⟩ ⟨fmul⟩ ⟨fdiv⟩ ⟨⟨131072⟩⟩ ⟨⟨196608⟩⟩ c s)
  rnS c s := mulR s (@rnFactor Fx ⟨fun a b => ⟨a.raw + b.raw⟩⟩ ⟨fun a b => ⟨a.raw - b.raw⟩⟩ ⟨fmul⟩ ⟨fdiv⟩ ⟨⟨131072⟩⟩ ⟨⟨196608⟩⟩ c s)

end Jsb
