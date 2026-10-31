import Vibecheck.Fixed

/-! Deterministic fixed-point helpers for the JSBSim c172p port: table lookup, square root, arctangent. -/

namespace Jsb
open Vibecheck

/-- Floor of `a / b` for `b > 0`. -/
def floorDiv64 (a b : Int64) : Int64 :=
  let q := a / b
  if a % b < 0 then q - 1 else q

/-- Floor of `n / d` for `d > 0` in `Int64` (Lean's `Int` leaves its scalar range above 2^31, which costs a heap allocation). -/
def floorDiv (n d : Int) : Int :=
  if 0 < d then
    (floorDiv64 (Int64.ofInt n) (Int64.ofInt d)).toInt
  else n / d

/-- Floor division on `Fx`, meaning the same as the `Div` instance of `Vibecheck.Fx` for positive divisors. -/
def fdiv (a b : Fx) : Fx :=
  let b64 := Int64.ofInt b.raw
  let a64 := Int64.ofInt a.raw
  if 0 < b64 ∧ -140737488355328 ≤ a64 ∧ a64 < 140737488355328 then
    ⟨(floorDiv64 (a64 <<< (16 : Int64)) b64).toInt⟩
  else ⟨a.raw * 65536 / b.raw⟩

/-- Floor product, same meaning as `Vibecheck.Fx.fastMul`; the range test runs on `Int64` so no `Int` literal above 2^31 is compared. -/
def fmul (a b : Fx) : Fx :=
  let a64 := Int64.ofInt a.raw
  let b64 := Int64.ofInt b.raw
  if -2147483648 ≤ a64 ∧ a64 < 2147483648 ∧ -2147483648 ≤ b64 ∧ b64 < 2147483648 then
    ⟨((a64 * b64) >>> (16 : Int64)).toInt⟩
  else ⟨a.raw * b.raw / 65536⟩

instance : Div Fx := ⟨fdiv⟩
instance : Mul Fx := ⟨fmul⟩

/-- Product rounded to nearest (the `Fx` product floors). -/
def mulR (a b : Fx) : Fx :=
  let a64 := Int64.ofInt a.raw
  let b64 := Int64.ofInt b.raw
  if -2147483648 ≤ a64 ∧ a64 < 2147483648 ∧ -2147483648 ≤ b64 ∧ b64 < 2147483648 then
    ⟨((a64 * b64 + 32768) >>> (16 : Int64)).toInt⟩
  else ⟨(a.raw * b.raw + 32768) / 65536⟩

/-- Piecewise-linear table over raw `Fx` abscissae (ascending); clamped at both ends like JSBSim's `FGTable`. -/
structure Tbl1 where
  xs : Array Int
  ys : Array Int

/-- Bilinear table; `data` is row-major with `cols.size` entries per row. -/
structure Tbl2 where
  rows : Array Int
  cols : Array Int
  data : Array Int

/-- Largest `i` with `i + 2 ≤ xs.size` and `xs[i] ≤ x` (linear scan, fuel = size). -/
def segment (xs : Array Int) (x : Int) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => if i + 2 < xs.size ∧ xs[i + 1]! ≤ x then segment xs x n (i + 1) else i

/-- `y0 + (y1 - y0) (x - x0) / (x1 - x0)` on raw integers. -/
def lerp (x0 x1 y0 y1 x : Int) : Int :=
  y0 + (if 0 < x1 - x0 then (floorDiv64 (Int64.ofInt (y1 - y0) * Int64.ofInt (x - x0)) (Int64.ofInt (x1 - x0))).toInt else 0)

def Tbl1.eval (t : Tbl1) (x : Fx) : Fx :=
  let n := t.xs.size
  if x.raw ≤ t.xs[0]! then ⟨t.ys[0]!⟩
  else if t.xs[n - 1]! ≤ x.raw then ⟨t.ys[n - 1]!⟩
  else
    let i := segment t.xs x.raw n 0
    ⟨lerp t.xs[i]! t.xs[i + 1]! t.ys[i]! t.ys[i + 1]! x.raw⟩

def Tbl2.eval (t : Tbl2) (r c : Fx) : Fx :=
  let nc := t.cols.size
  let rc := max t.rows[0]! (min t.rows[t.rows.size - 1]! r.raw)
  let cc := max t.cols[0]! (min t.cols[nc - 1]! c.raw)
  let i := segment t.rows rc t.rows.size 0
  let j := segment t.cols cc nc 0
  let cell (a b : Nat) : Int := t.data[a * nc + b]!
  let row (a : Nat) : Int := lerp t.cols[j]! t.cols[j + 1]! (cell a j) (cell a (j + 1)) cc
  ⟨lerp t.rows[i]! t.rows[i + 1]! (row i) (row (i + 1)) rc⟩

/-- Newton iteration from above; exact floor square root for the sizes used here. -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => let y := (x + n / x) / 2; if y < x then isqrtAux n f y else x

def isqrt (n : Nat) : Nat :=
  if n < 2 then n else isqrtAux n 64 (1 <<< (Nat.log2 n / 2 + 1))

/-- Square root of a non-negative `Fx` (0 for negative input), truncated to the grid. -/
def sqrtFx (a : Fx) : Fx := ⟨(isqrt (a.raw.toNat * 65536) : Nat)⟩

/-- Horner coefficients of `atanS30` after the leading one, in 2^30 fixed point. -/
def atanCoef : List Int := [-17357828, 46073847, -80841635, 114420763, -152566896, 214679118, -357911922, 1073741824]

/-- Arctangent kernel on [-1, 1] in 2^30 fixed point (Abramowitz & Stegun 4.4.49, |error| ≤ 2e-8). -/
def atanS30 (t : Int) : Int :=
  let t64 := Int64.ofInt t
  let t2 := (t64 * t64) >>> (30 : Int64)
  let step (acc : Int64) (c : Int) : Int64 := Int64.ofInt c + ((acc * t2) >>> (30 : Int64))
  let p := atanCoef.foldl step 3077586
  ((t64 * p) >>> (30 : Int64)).toInt

/-- `atan2 y x` for `x > 0` or `y ≠ 0`, rad; |error| < 1 LSB (2^-16) after rounding to the grid. -/
def atan2Fx (y x : Fx) : Fx :=
  let ay := y.raw.natAbs
  let ax := x.raw.natAbs
  if ay == 0 && ax == 0 then ⟨0⟩ else
  let big := ay > ax
  let num : Int := if big then ax else ay
  let den : Int := if big then ay else ax
  let a := atanS30 (floorDiv (num * 1073741824) den) / 16384
  let a := if big then (102944 : Int) - a else a
  let a := if x.raw < 0 then (205887 : Int) - a else a
  ⟨if y.raw < 0 then -a else a⟩

end Jsb
