import Jsb.Scalar

/-! Interval instance of `Scalar` over raw `Fx` endpoints, in plain `Int` so the kernel can evaluate it. -/

namespace Jsb
open Vibecheck

inductive Iv where
  | top
  | box (lo hi : Int)
  deriving Repr, Inhabited, DecidableEq

namespace Iv

def Mem : Iv → Fx → Prop
  | top, _ => True
  | box lo hi, x => lo ≤ x.raw ∧ x.raw ≤ hi

/-- `2^63`: operands of `Int64` fast paths must lie in `[-2^63, 2^63)`. -/
def B63 : Int := 9223372036854775808
/-- `2^62`: bound on products formed by the `Int64` kernels of `atan2Fx` and table lerps. -/
def B62 : Int := 4611686018427387904

def in64 (lo hi : Int) : Bool := decide (-B63 ≤ lo) && decide (hi < B63)

def hull : Iv → Iv → Iv
  | box a b, box c d => box (min a c) (max b d)
  | _, _ => top

def min4 (a b c d : Int) : Int := min (min a b) (min c d)
def max4 (a b c d : Int) : Int := max (max a b) (max c d)

def add : Iv → Iv → Iv
  | box a b, box c d => box (a + c) (b + d)
  | _, _ => top

def sub : Iv → Iv → Iv
  | box a b, box c d => box (a - d) (b - c)
  | _, _ => top

def neg : Iv → Iv
  | box a b => box (-b) (-a)
  | top => top

def prods (a b c d : Int) : Int × Int := (min4 (a * c) (a * d) (b * c) (b * d), max4 (a * c) (a * d) (b * c) (b * d))

def mul : Iv → Iv → Iv
  | box a b, box c d =>
    if in64 a b && in64 c d then let p := prods a b c d; box (p.1 / 65536) (p.2 / 65536) else top
  | _, _ => top

def mulR : Iv → Iv → Iv
  | box a b, box c d =>
    if in64 a b && in64 c d then let p := prods a b c d; box ((p.1 + 32768) / 65536) ((p.2 + 32768) / 65536)
    else top
  | _, _ => top

def div : Iv → Iv → Iv
  | box a b, box c d =>
    if in64 a b && in64 c d && decide (0 < c) then
      box (min (a * 65536 / c) (a * 65536 / d)) (max (b * 65536 / c) (b * 65536 / d))
    else top
  | _, _ => top

def max : Iv → Iv → Iv
  | box a b, box c d => box (Max.max a c) (Max.max b d)
  | _, _ => top

def min : Iv → Iv → Iv
  | box a b, box c d => box (Min.min a c) (Min.min b d)
  | _, _ => top

def shrZ (a : Int) (k : Nat) : Int := (a + (1 <<< (k - 1))) >>> k

def shr : Iv → Nat → Iv
  | box a b, k => box (shrZ a k) (shrZ b k)
  | top, _ => top

def ab3 : Iv → Iv → Iv → Iv
  | box a b, box c d, box e f => box ((23 * a - 16 * d + 5 * e) / 12) ((23 * b - 16 * c + 5 * f) / 12)
  | _, _, _ => top

def abs : Iv → Iv
  | box a b => if 0 ≤ a then box a b else if b ≤ 0 then box (-b) (-a) else box 0 (Max.max (-a) b)
  | top => top

def sqrt : Iv → Iv
  | box a b => if b < 2 ^ 100 then box (isqrt (a.toNat * 65536)) (isqrt (b.toNat * 65536)) else top
  | top => top

def mulShr30 (a b c d : Int) : Option (Int × Int) :=
  let p := prods a b c d
  if -B62 < p.1 ∧ p.2 < B62 then some (p.1 >>> 30, p.2 >>> 30) else none

def atanStep (t2lo t2hi : Int) : Option (Int × Int) → Int → Option (Int × Int)
  | some (a, b), c =>
    match mulShr30 a b t2lo t2hi with
    | some (p, q) => if -B62 < c + p ∧ c + q < B62 then some (c + p, c + q) else none
    | none => none
  | none, _ => none

def atanS30I (lo hi : Int) : Option (Int × Int) :=
  if -2147483648 ≤ lo ∧ hi ≤ 2147483648 then
    let sq := if 0 ≤ lo then (lo * lo, hi * hi) else if hi ≤ 0 then (hi * hi, lo * lo)
              else (0, Max.max (lo * lo) (hi * hi))
    match atanCoef.foldl (atanStep (sq.1 >>> 30) (sq.2 >>> 30)) (some (3077586, 3077586)) with
    | some (p, q) => mulShr30 lo hi p q
    | none => none
  else none

def atan2 : Iv → Iv → Iv
  | box yl yh, box xl xh =>
    let m := Max.max (-yl) yh
    if 0 < xl ∧ m ≤ xl ∧ xh < 2 ^ 32 then
      let nlo : Int := if yl ≤ 0 ∧ 0 ≤ yh then 0 else Min.min yl.natAbs yh.natAbs
      match atanS30I (nlo * 1073741824 / xh) (m * 1073741824 / xl) with
      | some (p, q) =>
        let lo := p / 16384
        let hi := q / 16384
        if 0 ≤ yl then box lo hi else if yh < 0 then box (-hi) (-lo) else box (Min.min lo (-hi)) (Max.max hi (-lo))
      | none => top
    else top
  | _, _ => top

def acc (o : Option (Int × Int)) (lo hi : Int) : Option (Int × Int) :=
  match o with
  | none => some (lo, hi)
  | some (a, b) => some (Min.min a lo, Max.max b hi)

def lerpZ (x0 x1 y0 y1 x : Int) : Int := y0 + (if 0 < x1 - x0 then (y1 - y0) * (x - x0) / (x1 - x0) else 0)

def lerpI (x0 x1 p P r R xa xb : Int) : Option (Int × Int) :=
  let dy := Max.max (R - p) (P - r)
  if 0 ≤ x1 - x0 ∧ x1 - x0 < B62 ∧ dy < B62 ∧ dy * (x1 - x0) < B62 then
    some (Min.min (lerpZ x0 x1 p r xa) (lerpZ x0 x1 p r xb), Max.max (lerpZ x0 x1 P R xa) (lerpZ x0 x1 P R xb))
  else none

def segsI (xs : Array Int) (val : Nat → Option (Int × Int × Int × Int)) (lo hi : Int) :
    Nat → Nat → Option (Int × Int) → Option (Option (Int × Int))
  | 0, _, o => some o
  | n + 1, i, o =>
    let a := Max.max lo xs[i]!
    let b := Min.min hi xs[i + 1]!
    if a ≤ b then
      match val i with
      | some (p, P, r, R) =>
        match lerpI xs[i]! xs[i + 1]! p P r R a b with
        | some (u, v) => segsI xs val lo hi n (i + 1) (acc o u v)
        | none => none
      | none => none
    else segsI xs val lo hi n (i + 1) o

def ofAcc : Option (Option (Int × Int)) → Iv
  | some (some (a, b)) => box a b
  | some none => box 1 0
  | none => top

def tbl1 (t : Tbl1) : Iv → Iv
  | box lo hi =>
    let n := t.xs.size
    let o : Option (Int × Int) := if lo ≤ t.xs[0]! then some (t.ys[0]!, t.ys[0]!) else none
    let o := if t.xs[n - 1]! ≤ hi then acc o t.ys[n - 1]! t.ys[n - 1]! else o
    let lo' := Max.max lo (t.xs[0]! + 1)
    let hi' := Min.min hi (t.xs[n - 1]! - 1)
    if lo' ≤ hi' then
      match segsI t.xs (fun i => some (t.ys[i]!, t.ys[i]!, t.ys[i + 1]!, t.ys[i + 1]!)) lo' hi' (n - 1) 0 o with
      | some o => ofAcc (some o)
      | none => top
    else ofAcc (some o)
  | top => top

def tbl2 (t : Tbl2) : Iv → Iv → Iv
  | box rlo rhi, box clo chi =>
    let nr := t.rows.size
    let nc := t.cols.size
    if 2 ≤ nr ∧ 2 ≤ nc ∧ t.rows[0]! ≤ t.rows[nr - 1]! ∧ t.cols[0]! ≤ t.cols[nc - 1]! then
      let rl := Max.max t.rows[0]! (Min.min t.rows[nr - 1]! rlo)
      let rh := Max.max t.rows[0]! (Min.min t.rows[nr - 1]! rhi)
      let cl := Max.max t.cols[0]! (Min.min t.cols[nc - 1]! clo)
      let ch := Max.max t.cols[0]! (Min.min t.cols[nc - 1]! chi)
      let row (a : Nat) : Option (Int × Int) :=
        (segsI t.cols (fun j => some (t.data[a * nc + j]!, t.data[a * nc + j]!, t.data[a * nc + j + 1]!,
          t.data[a * nc + j + 1]!)) cl ch (nc - 1) 0 none).bind id
      let val (i : Nat) : Option (Int × Int × Int × Int) :=
        match row i, row (i + 1) with
        | some (p, P), some (r, R) => some (p, P, r, R)
        | _, _ => none
      ofAcc (segsI t.rows val rl rh (nr - 1) 0 none)
    else top
  | _, _ => top

def atmCells (tab : Array Int) (lo hi : Int) : Nat → Nat → Option (Int × Int) → Option (Option (Int × Int))
  | 0, _, o => some o
  | n + 1, i, o =>
    let span : Int := 50 * 65536
    let fa := Max.max 0 (Min.min span (lo - i * span))
    let fb := Max.max 0 (Min.min span (hi - i * span))
    match lerpI 0 span tab[i]! tab[i]! tab[i + 1]! tab[i + 1]! fa fb with
    | some (u, v) => atmCells tab lo hi n (i + 1) (acc o u v)
    | none => none

def atm (tab : Array Int) : Iv → Iv
  | box lo hi =>
    let span : Int := 50 * 65536
    let il := (Max.max 0 (Min.min (span * 159) lo) / span).toNat
    let ih := (Max.max 0 (Min.min (span * 159) hi) / span).toNat
    if lo ≤ hi then ofAcc (atmCells tab lo hi (ih + 1 - il) il none) else box 1 0
  | top => top

def selLt : Iv → Iv → Iv → Iv → Iv
  | box a1 a2, box b1 b2, t, e => if a2 < b1 then t else if b2 ≤ a1 then e else hull t e
  | _, _, t, e => hull t e

def selLe : Iv → Iv → Iv → Iv → Iv
  | box a1 a2, box b1 b2, t, e => if a2 ≤ b1 then t else if b2 < a1 then e else hull t e
  | _, _, t, e => hull t e

def lit (r : Int) : Iv := box r r

def rnFactorI (c s : Iv) : Iv := sub (div (lit 196608) (lit 131072)) (div (add (mul c c) (mul s s)) (lit 131072))

/-- Hull of `f` over the pieces `[t j, t (j+1)]`, `j < m`. -/
def hullPieces (f : Iv → Iv) (t : Nat → Int) : Nat → Iv
  | 0 => box 1 0
  | 1 => f (box (t 0) (t 1))
  | m + 1 => hull (hullPieces f t m) (f (box (t m) (t (m + 1))))

def rnSplit : Nat := 8

def splitMap (f : Iv → Iv) : Iv → Iv
  | box a b => hullPieces f (fun j => a + (b - a) * j / rnSplit) rnSplit
  | top => f top

def rnC (c s : Iv) : Iv := splitMap (fun c' => mulR c' (rnFactorI c' s)) c
def rnS (c s : Iv) : Iv := splitMap (fun c' => mulR s (rnFactorI c' s)) c

instance : Scalar Iv where
  add := add
  sub := sub
  neg := neg
  mul := mul
  div := div
  max := max
  min := min
  lit := lit
  mulR := mulR
  shr := shr
  ab3 := ab3
  abs := abs
  sqrt := sqrt
  atan2 := atan2
  tbl1 := tbl1
  tbl2 := tbl2
  atm := atm
  selLt := selLt
  selLe := selLe
  rnC := rnC
  rnS := rnS

end Iv

end Jsb
