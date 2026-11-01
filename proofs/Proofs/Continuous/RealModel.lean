import Mathlib
import Jsb.Model

/-! The c172p longitudinal model over `ℝ`: a `Scalar ℝ` instance with exact arithmetic, `Real.sqrt`, the true
arctangent and continuous piecewise-linear tables, so `evaluate (α := ℝ)` is the real-number vector field. -/

namespace Jsb.Cont
open Real

/-- Value of a raw `Fx` integer. -/
noncomputable def ofRaw (r : Int) : ℝ := (r : ℝ) / 65536

/-- Sum of the segment contributions of a piecewise-linear interpolant (slope times clamped progress). -/
noncomputable def plAux : List ℝ → List ℝ → ℝ → ℝ
  | x0 :: x1 :: xs, y0 :: y1 :: ys, x =>
      (y1 - y0) / (x1 - x0) * (max x0 (min x x1) - x0) + plAux (x1 :: xs) (y1 :: ys) x
  | _, _, _ => 0

/-- Continuous piecewise-linear interpolant through `(xs, ys)`, constant beyond both ends (for ascending `xs`
this is JSBSim's clamped table lookup). -/
noncomputable def pl (xs ys : List ℝ) (x : ℝ) : ℝ := ys.headD 0 + plAux xs ys x

noncomputable def rawList (a : Array Int) : List ℝ := a.toList.map ofRaw

noncomputable def tbl1R (t : Tbl1) (x : ℝ) : ℝ := pl (rawList t.xs) (rawList t.ys) x

/-- Column `b` of a row-major table. -/
def col (t : Tbl2) (b : Nat) : Array Int := (List.range t.rows.size).toArray.map fun a => t.data[a * t.cols.size + b]!

/-- Hat weight of column `b` at `c`. -/
noncomputable def hat (t : Tbl2) (b : Nat) (c : ℝ) : ℝ :=
  pl (rawList t.cols) ((List.range t.cols.size).map fun j => if j = b then 1 else 0) c

/-- Bilinear interpolation with clamping: hat weights over columns times row interpolants. -/
noncomputable def tbl2R (t : Tbl2) (r c : ℝ) : ℝ :=
  ((List.range t.cols.size).map fun b => hat t b c * pl (rawList t.rows) (rawList (col t b)) r).sum

/-- Standard atmosphere at 50 m spacing from 0 m. -/
noncomputable def atmR (tab : Array Int) (h : ℝ) : ℝ :=
  pl ((List.range tab.size).map fun i => (50 * i : ℝ)) (rawList tab) h

/-- `atan2 y x` (the principal argument of `x + i y`). -/
noncomputable def atan2R (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

/-- Not a global instance: with `Scalar ℝ` in scope, numerals and `/` on `ℝ` would elaborate through `Scalar`. -/
noncomputable def realScalar : Scalar ℝ where
  add := (· + ·)
  sub := (· - ·)
  neg x := -x
  mul := (· * ·)
  div := (· / ·)
  max := max
  min := min
  lit := ofRaw
  mulR := (· * ·)
  shr a k := a / 2 ^ k
  ab3 a b c := (23 * a - 16 * b + 5 * c) / 12
  abs := abs
  sqrt := Real.sqrt
  atan2 := atan2R
  tbl1 := tbl1R
  tbl2 := tbl2R
  atm := atmR
  selLt a b t e := if a < b then t else e
  selLe a b t e := if a ≤ b then t else e
  rnC c s := c * (3 / 2 - (c * c + s * s) / 2)
  rnS c s := s * (3 / 2 - (c * c + s * s) / 2)

end Jsb.Cont

namespace Jsb.Cont
open Real

/-! Rewriting the instance's operations to Mathlib's. -/
section inst
local notation "RS" => realScalar
theorem i_add (a b : ℝ) : @HAdd.hAdd ℝ ℝ ℝ (@instHAdd ℝ (@Scalar.toAdd ℝ RS)) a b = a + b := rfl
theorem i_sub (a b : ℝ) : @HSub.hSub ℝ ℝ ℝ (@instHSub ℝ (@Scalar.toSub ℝ RS)) a b = a - b := rfl
theorem i_mul (a b : ℝ) : @HMul.hMul ℝ ℝ ℝ (@instHMul ℝ (@Scalar.toMul ℝ RS)) a b = a * b := rfl
theorem i_div (a b : ℝ) : @HDiv.hDiv ℝ ℝ ℝ (@instHDiv ℝ (@Scalar.toDiv ℝ RS)) a b = a / b := rfl
theorem i_neg (a : ℝ) : @Neg.neg ℝ (@Scalar.toNeg ℝ RS) a = -a := rfl
theorem i_max (a b : ℝ) : @Max.max ℝ (@Scalar.toMax ℝ RS) a b = max a b := rfl
theorem i_min (a b : ℝ) : @Min.min ℝ (@Scalar.toMin ℝ RS) a b = min a b := rfl
theorem i_lit (r : Int) : @Scalar.lit ℝ RS r = (r : ℝ) / 65536 := rfl
theorem i_ofNat (n : Nat) : (@OfNat.ofNat ℝ n (@instOfNatScalar ℝ RS n)) = (n : ℝ) := by
  show ofRaw _ = _; simp [ofRaw]
theorem i_selLt (a b t e : ℝ) : @Scalar.selLt ℝ RS a b t e = if a < b then t else e := rfl
theorem i_selLe (a b t e : ℝ) : @Scalar.selLe ℝ RS a b t e = if a ≤ b then t else e := rfl
theorem i_sqrt (a : ℝ) : @Scalar.sqrt ℝ RS a = Real.sqrt a := rfl
theorem i_atan2 (a b : ℝ) : @Scalar.atan2 ℝ RS a b = atan2R a b := rfl
theorem i_tbl1 (t : Tbl1) (a : ℝ) : @Scalar.tbl1 ℝ RS t a = tbl1R t a := rfl
theorem i_tbl2 (t : Tbl2) (a b : ℝ) : @Scalar.tbl2 ℝ RS t a b = tbl2R t a b := rfl
theorem i_atm (t : Array Int) (a : ℝ) : @Scalar.atm ℝ RS t a = atmR t a := rfl
theorem i_abs (a : ℝ) : @Scalar.abs ℝ RS a = |a| := rfl
theorem i_shr (a : ℝ) (k : Nat) : @Scalar.shr ℝ RS a k = a / 2 ^ k := rfl
end inst

/-- The real-number evaluation (forces, moments, engine, derivatives) of the model. -/
noncomputable def evalR (inp : InputOf ℝ) (s : StateOf ℝ) : StateOf ℝ × ProbeOf ℝ := @evaluate ℝ realScalar 7 inp s

end Jsb.Cont
