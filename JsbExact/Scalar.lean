/-! Scalar interface; `mac`/`msc`/`nmac` mark where clang `-ffp-contract=on` fuses JSBSim's `a*b ± c`. -/

namespace JsbExact

class Scalar (α : Type) where
  Cond : Type
  ofFloat : Float → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  fma : α → α → α → α
  lt : α → α → Cond
  le : α → α → Cond
  eq : α → α → Cond
  ofBool : Bool → Cond
  not : Cond → Cond
  and : Cond → Cond → Cond
  or : Cond → Cond → Cond
  /-- `t ()` if `c` holds, else `e ()`; a set-valued instance returns `join` of both when `c` is undecided. -/
  branch {β : Type} : (β → β → β) → Cond → (Unit → β) → (Unit → β) → β
  join : α → α → α
  /-- Outcome of a decision whose branches have no join; set-valued enclosures hold only where `c` is decided. -/
  mode : Cond → Bool
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
  Cond := Bool
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
  ofBool b := b
  not c := !c
  and a b := a && b
  or a b := a || b
  branch _ c t e := if c then t () else e ()
  join a _ := a
  mode c := c
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
instance : Inhabited (Scalar.Cond α) := ⟨Scalar.ofBool false⟩

/-- The join `branch` uses for a result of type `β`, built componentwise from `Scalar.join`. -/
class Join (α : Type) [Scalar α] (β : Type) where
  join : β → β → β

instance : Join α α := ⟨Scalar.join⟩
instance {β γ : Type} [Join α β] [Join α γ] : Join α (β × γ) :=
  ⟨fun a b => (Join.join (α := α) a.1 b.1, Join.join (α := α) a.2 b.2)⟩
/-- Elementwise; both arrays have the same length wherever the model joins them. -/
instance {β : Type} [Join α β] : Join α (Array β) := ⟨fun a b => Array.zipWith (Join.join (α := α)) a b⟩

namespace S
@[inline] def br {β : Type} [Join α β] (c : Scalar.Cond α) (t e : Unit → β) : β :=
  Scalar.branch (Join.join (α := α)) c t e
end S

syntax:lead "sif " term " then " term " else " term : term
macro_rules
  | `(sif $c then $t else $e) => `(JsbExact.S.br $c (fun _ => $t) (fun _ => $e))

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
@[inline] def lt (a b : α) : Scalar.Cond α := Scalar.lt a b
@[inline] def le (a b : α) : Scalar.Cond α := Scalar.le a b
@[inline] def gt (a b : α) : Scalar.Cond α := Scalar.lt b a
@[inline] def ge (a b : α) : Scalar.Cond α := Scalar.le b a
@[inline] def eq (a b : α) : Scalar.Cond α := Scalar.eq a b
@[inline] def ne (a b : α) : Scalar.Cond α := Scalar.not (Scalar.eq a b)
@[inline] def cnot (c : Scalar.Cond α) : Scalar.Cond α := Scalar.not c
@[inline] def cand (a b : Scalar.Cond α) : Scalar.Cond α := Scalar.and a b
@[inline] def cor (a b : Scalar.Cond α) : Scalar.Cond α := Scalar.or a b
@[inline] def cbool (b : Bool) : Scalar.Cond α := Scalar.ofBool b
@[inline] def mode (c : Scalar.Cond α) : Bool := Scalar.mode c
@[inline] def ite (c : Scalar.Cond α) (a b : α) : α := sif c then a else b
/-- `std::max(a, b)`. -/
@[inline] def max (a b : α) : α := ite (lt a b) b a
/-- `std::min(a, b)`. -/
@[inline] def min (a b : α) : α := ite (lt b a) b a
/-- `FGJSBBase::Constrain(lo, x, hi)`. -/
@[inline] def constrain (lo x hi : α) : α := sif lt x lo then lo else ite (gt x hi) hi x
/-- `FGJSBBase::sign`. -/
@[inline] def sign (x : α) : α := ite (ge x zero) one (lit (-1.0))
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
