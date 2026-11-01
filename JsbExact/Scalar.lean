/-! Scalar interface; `mac`/`msc`/`nmac` mark where clang `-ffp-contract=on` fuses JSBSim's `a*b ± c`. -/

namespace JsbExact

class Scalar (α : Type) where
  ofFloat : Float → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  fma : α → α → α → α
  lt : α → α → Bool
  le : α → α → Bool
  eq : α → α → Bool
  sqrt : α → α
  sin : α → α
  cos : α → α
  sinS : α → α
  cosS : α → α
  atan : α → α
  asin : α → α
  atan2 : α → α → α
  pow : α → α → α
  exp : α → α
  abs : α → α

@[extern "jx_sin"] opaque jxSin : Float → Float
@[extern "jx_cos"] opaque jxCos : Float → Float
@[extern "jx_sincos_sin"] opaque jxSincosSin : Float → Float
@[extern "jx_sincos_cos"] opaque jxSincosCos : Float → Float

instance : Scalar Float where
  ofFloat x := x
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  div := Float.div
  neg := Float.neg
  fma := Float.fma
  lt a b := a < b
  le a b := a ≤ b
  eq a b := a == b
  sqrt := Float.sqrt
  sin := jxSin
  cos := jxCos
  sinS := jxSincosSin
  cosS := jxSincosCos
  atan := Float.atan
  asin := Float.asin
  atan2 := Float.atan2
  pow := Float.pow
  exp := Float.exp
  abs := Float.abs

variable {α : Type} [Scalar α]

instance : Add α := ⟨Scalar.add⟩
instance : Sub α := ⟨Scalar.sub⟩
instance : Mul α := ⟨Scalar.mul⟩
instance : Div α := ⟨Scalar.div⟩
instance : Neg α := ⟨Scalar.neg⟩
instance (priority := low) : Inhabited α := ⟨Scalar.ofFloat 0.0⟩

namespace S
@[inline] def lit (x : Float) : α := Scalar.ofFloat x
@[inline] def zero : α := lit 0.0
@[inline] def one : α := lit 1.0
/-- C `a*b + c` under contraction. -/
@[inline] def mac (a b c : α) : α := Scalar.fma a b c
/-- C `a*b - c` under contraction. -/
@[inline] def msc (a b c : α) : α := Scalar.fma a b (-c)
/-- C `c - a*b` under contraction. -/
@[inline] def nmac (a b c : α) : α := Scalar.fma (-a) b c
@[inline] def lt (a b : α) : Bool := Scalar.lt a b
@[inline] def le (a b : α) : Bool := Scalar.le a b
@[inline] def gt (a b : α) : Bool := Scalar.lt b a
@[inline] def ge (a b : α) : Bool := Scalar.le b a
@[inline] def eq (a b : α) : Bool := Scalar.eq a b
@[inline] def ne (a b : α) : Bool := !Scalar.eq a b
/-- `std::max(a, b)`. -/
@[inline] def max (a b : α) : α := if lt a b then b else a
/-- `std::min(a, b)`. -/
@[inline] def min (a b : α) : α := if lt b a then b else a
/-- `FGJSBBase::Constrain(lo, x, hi)`. -/
@[inline] def constrain (lo x hi : α) : α := if lt x lo then lo else if gt x hi then hi else x
/-- `FGJSBBase::sign`. -/
@[inline] def sign (x : α) : α := if ge x zero then one else lit (-1.0)
@[inline] def sqrt (x : α) : α := Scalar.sqrt x
@[inline] def sin (x : α) : α := Scalar.sin x
@[inline] def cos (x : α) : α := Scalar.cos x
/-- `sin` where the C function also takes `cos` of the same argument (clang emits `__sincos_stret`). -/
@[inline] def sinS (x : α) : α := Scalar.sinS x
@[inline] def cosS (x : α) : α := Scalar.cosS x
@[inline] def atan (x : α) : α := Scalar.atan x
@[inline] def asin (x : α) : α := Scalar.asin x
@[inline] def atan2 (y x : α) : α := Scalar.atan2 y x
@[inline] def pow (x y : α) : α := Scalar.pow x y
@[inline] def exp (x : α) : α := Scalar.exp x
@[inline] def abs (x : α) : α := Scalar.abs x
end S

end JsbExact
