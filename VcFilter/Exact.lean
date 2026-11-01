/-! Exact conversion of IEEE-754 binary64 values to `Rat` (every finite double is a dyadic rational). -/

namespace VcFilter

/-- `m · 2^e` as a rational. -/
def dyadic (m : Int) (e : Int) : Rat :=
  if 0 ≤ e then (m : Rat) * ((2 ^ e.toNat : Nat) : Rat) else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

/-- The exact value of the binary64 word `b`; `none` for infinities and NaNs. -/
def ratOfBits (b : UInt64) : Option Rat :=
  let neg := b >>> 63 == 1
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0x7FF then none
  else
    let (m, ex) : Nat × Int := if e == 0 then (frac, -1074) else (frac + 2 ^ 52, (e : Int) - 1075)
    let q := dyadic m ex
    some (if neg then -q else q)

/-- The exact value of the double `f`; `none` if it is not finite. -/
def ratOfFloat (f : Float) : Option Rat := ratOfBits f.toBits

/-- Nearest-ish double to `q`, for reporting only (never used in a decision). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

#guard ratOfFloat 0.125 == some (1 / 8)
#guard ratOfFloat (-2.5) == some (-5 / 2)
#guard ratOfFloat 0 == some 0
#guard ratOfFloat (-0.0) == some 0
#guard ratOfFloat 1 == some 1
#guard ratOfFloat 300 == some 300
#guard ratOfFloat 0.1 == some (3602879701896397 / 36028797018963968)
#guard ratOfBits 1 == some ((1 : Rat) / ((2 ^ 1074 : Nat) : Rat))
#guard ratOfBits 0x7FEFFFFFFFFFFFFF == some (((2 ^ 53 - 1 : Nat) : Rat) * ((2 ^ 971 : Nat) : Rat))
#guard ratOfFloat (1 / 0) == none
#guard ratOfFloat (-1 / 0) == none
#guard ratOfFloat (0 / 0) == none
#guard (List.range 200).all fun i =>
  let f := Float.ofInt ((i : Int) * 7919 - 700000) / 1024
  ratOfFloat f == some (((i : Int) * 7919 - 700000 : Int) / (1024 : Rat))

end VcFilter
