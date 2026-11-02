import ExpVibecheck.Fixed
import ExpEnvelope.Params

/-! The single number conversion at the host boundary: IEEE 754 binary64 doubles to the filter's
number type. Every finite double is a dyadic rational, so the conversion to `Rat` is exact; the
conversion to `Fx` (grid 2⁻¹⁶) rounds, in a direction the caller picks per field. -/

namespace Filters

/-- The exact rational value of an IEEE 754 binary64 bit pattern; `none` for ±∞ and NaN.
Bit 63 is the sign, bits 52–62 the biased exponent `e`, bits 0–51 the fraction `m`; a normal number
(`0 < e < 2047`) is `(2⁵² + m) · 2^(e − 1075)`, a subnormal or zero (`e = 0`) is `m · 2^(−1074)`. -/
def ratOfBits (b : UInt64) : Option Rat :=
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let m := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e = 0x7FF then none
  else
    let sig : Nat := if e = 0 then m else 2 ^ 52 + m
    let ex : Int := (if e = 0 then 1 else (e : Int)) - 1075
    let mag : Rat := if 0 ≤ ex then ((sig * 2 ^ ex.toNat : Nat) : Rat) else mkRat sig (2 ^ (-ex).toNat)
    some (if b >>> 63 = 1 then -mag else mag)

/-- The exact rational value of a finite double (`none` for ±∞ and NaN). Intended meaning, checked on
examples in `Filters/Checks.lean` but not proved in general (the kernel cannot evaluate `Float`):
`ratOfFloat x = some q` iff `x` is finite and denotes exactly `q`. -/
def ratOfFloat (x : Float) : Option Rat := ratOfBits x.toBits

/-! ### Reference encoding, for checking `ratOfBits` -/

/-- `2 ^ k` for an integer `k`. -/
def pow2 (k : Int) : Rat := if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/-- The bit pattern with sign `neg`, biased exponent `e` and fraction `m`. -/
def bitsOf (neg : Bool) (e m : Nat) : UInt64 :=
  (if neg then (1 : UInt64) <<< 63 else 0) ||| (e.toUInt64 <<< 52) ||| m.toUInt64

/-- The textbook value: `(−1)^neg · 1.m · 2^(e − 1023)` (normal) or `(−1)^neg · 0.m · 2^(−1022)`
(subnormal), for `e < 2047`, `m < 2⁵²`. -/
def valueOf (neg : Bool) (e m : Nat) : Rat :=
  let frac : Rat := (m : Rat) / ((2 ^ 52 : Nat) : Rat)
  let mag := if e = 0 then frac * pow2 (-1022) else (1 + frac) * pow2 ((e : Int) - 1023)
  if neg then -mag else mag

/-! ### Into the filters' number types -/

/-- An exact `ExpEnvelope.State` from doubles (all five fields finite, else `none`). -/
def envelopeStateOf (x h vx vz V : Float) : Option ExpEnvelope.State := do
  pure ⟨← ratOfFloat x, ← ratOfFloat h, ← ratOfFloat vx, ← ratOfFloat vz, ← ratOfFloat V⟩

/-- Largest `Fx` at or below `q`: for fields where smaller is less favourable (height, fuel). -/
def fxFloor (q : Rat) : ExpVibecheck.Fx := ⟨(q * 65536).floor⟩

/-- Smallest `Fx` at or above `q`: for fields where larger is less favourable (sink rate, speed). -/
def fxCeil (q : Rat) : ExpVibecheck.Fx := ⟨(q * 65536).ceil⟩

theorem fxFloor_le (q : Rat) : (fxFloor q).toRat ≤ q := by
  have := Rat.floor_le (q * 65536)
  simp only [fxFloor, ExpVibecheck.Fx.toRat]
  grind

theorem le_fxCeil (q : Rat) : q ≤ (fxCeil q).toRat := by
  have := Rat.le_ceil (x := q * 65536)
  simp only [fxCeil, ExpVibecheck.Fx.toRat]
  grind

end Filters
