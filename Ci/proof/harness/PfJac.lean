import Ci.proof.T
open Vibecheck Jsb

/-! Unverified prototype: interval enclosure of the Jacobian (w.r.t. the 7 slow coordinates) of the real one-tick map
over a box, by forward-mode differentiation on intervals (Float, raw units, no outward rounding). Measures how tight
a verified mean-value argument could be. -/

namespace PfJac

def ND : Nat := 7

structure Ivl where
  lo : Float
  hi : Float
  deriving Inhabited

namespace Ivl
def pt (v : Float) : Ivl := ⟨v, v⟩
def add (a b : Ivl) : Ivl := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Ivl) : Ivl := ⟨a.lo - b.hi, a.hi - b.lo⟩
def neg (a : Ivl) : Ivl := ⟨-a.hi, -a.lo⟩
def mul (a b : Ivl) : Ivl :=
  let p := [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  ⟨p.foldl min 1e300, p.foldl max (-1e300)⟩
def scale (s : Float) (a : Ivl) : Ivl := if s ≥ 0 then ⟨s * a.lo, s * a.hi⟩ else ⟨s * a.hi, s * a.lo⟩
def inv (a : Ivl) : Ivl := if a.lo > 0 || a.hi < 0 then ⟨1 / a.hi, 1 / a.lo⟩ else ⟨-1e300, 1e300⟩
def hull (a b : Ivl) : Ivl := ⟨min a.lo b.lo, max a.hi b.hi⟩
def sq (a : Ivl) : Ivl := if a.lo ≥ 0 then ⟨a.lo * a.lo, a.hi * a.hi⟩ else if a.hi ≤ 0 then ⟨a.hi * a.hi, a.lo * a.lo⟩
  else ⟨0, max (a.lo * a.lo) (a.hi * a.hi)⟩
end Ivl

/-- value interval and derivative intervals -/
structure D where
  v : Ivl
  d : Array Ivl
  deriving Inhabited

def zeroD : Array Ivl := Array.replicate ND (Ivl.pt 0)
def cst (x : Float) : D := ⟨Ivl.pt x, zeroD⟩
def dmap (f : Ivl → Ivl) (a : D) : Array Ivl := a.d.map f
def dzip (f : Ivl → Ivl → Ivl) (a b : D) : Array Ivl := (a.d.zip b.d).map fun (p, q) => f p q
def hullD (a b : D) : D := ⟨Ivl.hull a.v b.v, dzip Ivl.hull a b⟩
def mulD (a b : D) : D :=  -- raw a b / 65536
  ⟨Ivl.scale (1 / 65536) (Ivl.mul a.v b.v), dzip (fun da db => Ivl.scale (1 / 65536) (Ivl.add (Ivl.mul a.v db) (Ivl.mul b.v da))) a b⟩
/-- chain rule for a unary function with value enclosure `fv` and derivative enclosure `fd` over the input range -/
def unaryD (fv fd : Ivl) (a : D) : D := ⟨fv, a.d.map fun da => Ivl.mul fd da⟩

/-- piecewise-linear table on raw xs, ys (clamped): value and slope enclosures over [lo, hi] -/
def plEnc (xs ys : Array Float) (x : Ivl) : Ivl × Ivl := Id.run do
  let n := xs.size
  let f := fun (t : Float) =>
    if t ≤ xs[0]! then ys[0]! else if xs[n - 1]! ≤ t then ys[n - 1]! else Id.run do
      let mut i := 0
      for k in [0:n - 1] do
        if xs[k]! ≤ t then i := k
      return ys[i]! + (ys[i + 1]! - ys[i]!) * (t - xs[i]!) / (xs[i + 1]! - xs[i]!)
  let mut vlo := min (f x.lo) (f x.hi); let mut vhi := max (f x.lo) (f x.hi)
  let mut slo : Float := 1e300; let mut shi : Float := -1e300
  if x.lo < xs[0]! || x.hi > xs[n - 1]! then slo := min slo 0; shi := max shi 0
  for k in [0:n - 1] do
    let a := xs[k]!; let b := xs[k + 1]!
    if b > x.lo && a < x.hi then
      let s := (ys[k + 1]! - ys[k]!) / (b - a)
      slo := min slo s; shi := max shi s
    if x.lo ≤ xs[k]! && xs[k]! ≤ x.hi then vlo := min vlo ys[k]!; vhi := max vhi ys[k]!
  if slo > shi then slo := 0; shi := 0
  return (⟨vlo, vhi⟩, ⟨slo, shi⟩)

def fl (a : Array Int) : Array Float := a.map Float.ofInt

instance : Scalar D where
  add a b := ⟨Ivl.add a.v b.v, dzip Ivl.add a b⟩
  sub a b := ⟨Ivl.sub a.v b.v, dzip Ivl.sub a b⟩
  neg a := ⟨Ivl.neg a.v, dmap Ivl.neg a⟩
  mul := mulD
  div a b :=  -- raw a 65536 / b
    let ib := Ivl.inv b.v
    let q := Ivl.scale 65536 (Ivl.mul a.v ib)
    let ib2 := Ivl.mul ib ib
    ⟨q, dzip (fun da db => Ivl.scale 65536 (Ivl.sub (Ivl.mul da ib) (Ivl.mul (Ivl.mul a.v db) ib2))) a b⟩
  max a b := if a.v.hi ≤ b.v.lo then b else if b.v.hi ≤ a.v.lo then a else hullD a b
  min a b := if a.v.hi ≤ b.v.lo then a else if b.v.hi ≤ a.v.lo then b else hullD a b
  lit r := cst (Float.ofInt r)
  mulR := mulD
  shr a k := let s := 1 / (2 ^ k.toFloat); ⟨Ivl.scale s a.v, dmap (Ivl.scale s) a⟩
  ab3 a b c := let f := fun (x y z : Ivl) => Ivl.scale (1 / 12) (Ivl.add (Ivl.sub (Ivl.scale 23 x) (Ivl.scale 16 y)) (Ivl.scale 5 z))
    ⟨f a.v b.v c.v, ((a.d.zip b.d).zip c.d).map fun ((x, y), z) => f x y z⟩
  abs a := if a.v.lo ≥ 0 then a else if a.v.hi ≤ 0 then ⟨Ivl.neg a.v, dmap Ivl.neg a⟩
    else ⟨⟨0, max (-a.v.lo) a.v.hi⟩, a.d.map fun x => Ivl.hull x (Ivl.neg x)⟩
  sqrt a :=  -- raw sqrt(a 65536); derivative 65536 / (2 sqrt(a 65536))
    let lo := Float.sqrt (max 0 a.v.lo * 65536); let hi := Float.sqrt (max 0 a.v.hi * 65536)
    unaryD ⟨lo, hi⟩ ⟨65536 / (2 * max hi 1e-9), 65536 / (2 * max lo 1e-9)⟩ a
  atan2 y x :=  -- raw atan2(y, x) 65536 for x > 0
    let vlo := Float.atan2 y.v.lo x.v.hi; let vhi := Float.atan2 y.v.hi x.v.lo  -- monotone for x > 0 (y > 0 case)
    let v : Ivl := ⟨65536 * min vlo (Float.atan2 y.v.lo x.v.lo), 65536 * max vhi (Float.atan2 y.v.hi x.v.hi)⟩
    let den := Ivl.inv (Ivl.add (Ivl.sq x.v) (Ivl.sq y.v))
    ⟨v, dzip (fun dy dx => Ivl.scale 65536 (Ivl.mul den (Ivl.sub (Ivl.mul x.v dy) (Ivl.mul y.v dx)))) y x⟩
  tbl1 t a := let (v, s) := plEnc (fl t.xs) (fl t.ys) a.v; unaryD v s a
  tbl2 t r c :=
    let cc := (c.v.lo + c.v.hi) / 2
    let j := if cc < Float.ofInt t.cols[1]! then 0 else 1
    let col := (List.range t.rows.size).toArray.map fun a => Float.ofInt t.data[a * t.cols.size + j]!
    let (v, s) := plEnc (fl t.rows) col r.v
    unaryD v s r
  atm tab h :=
    let xs := (List.range tab.size).toArray.map fun i => 50 * 65536 * i.toFloat
    let (v, s) := plEnc xs (fl tab) h.v
    unaryD v s h
  selLt a b t e := if a.v.hi < b.v.lo then t else if b.v.hi ≤ a.v.lo then e else hullD t e
  selLe a b t e := if a.v.hi ≤ b.v.lo then t else if b.v.hi < a.v.lo then e else hullD t e
  rnC c s := mulD c (⟨Ivl.sub (Ivl.pt 98304) (Ivl.scale 0.5 (Ivl.add (Ivl.mul c.v c.v) (Ivl.mul s.v s.v) |> Ivl.scale (1 / 65536))),
    dzip (fun dc ds => Ivl.scale (-1 / 65536) (Ivl.add (Ivl.mul c.v dc) (Ivl.mul s.v ds))) c s⟩)
  rnS c s := mulD s (⟨Ivl.sub (Ivl.pt 98304) (Ivl.scale 0.5 (Ivl.add (Ivl.mul c.v c.v) (Ivl.mul s.v s.v) |> Ivl.scale (1 / 65536))),
    dzip (fun dc ds => Ivl.scale (-1 / 65536) (Ivl.add (Ivl.mul c.v dc) (Ivl.mul s.v ds))) c s⟩)

/-- Input: 21 lines "lo hi d0lo d0hi ... d6lo d6hi" for the 19 state fields, eI and the elevator (with its
derivative enclosure), then a line with the throttle. Output: the 19 end-state fields in the same format. -/
def run : IO Unit := do
  let stdin ← IO.getStdin
  let rd : IO D := do
    let l ← stdin.getLine
    let w := ((l.trimAscii.toString.splitOn " ").filter (· ≠ "")).toArray.map fun s => (s.toInt!.toFloat / 1000.0 : Float)
    return ⟨⟨w[0]!, w[1]!⟩, (List.range ND).toArray.map fun i => ⟨w[2 + 2 * i]!, w[3 + 2 * i]!⟩⟩
  let mut fs : Array D := #[]
  for _ in [0:19] do fs := fs.push (← rd)
  let el ← rd
  let thrL ← stdin.getLine
  let thr := thrL.trimAscii.toString.toInt!.toFloat
  let S : StateOf D := ⟨fs[0]!, fs[1]!, fs[2]!, fs[3]!, fs[4]!, fs[5]!, fs[6]!, fs[7]!, fs[8]!, fs[9]!, fs[10]!, fs[11]!,
    fs[12]!, fs[13]!, fs[14]!, fs[15]!, fs[16]!, fs[17]!, fs[18]!⟩
  let U : InputOf D := ⟨el, cst thr, cst 0, cst 0⟩
  let S' := iter 8 (Jsb.step 7 true U) S
  for x in [S'.x, S'.h, S'.vx, S'.vz, S'.dx, S'.dz, S'.q, S'.rpm, S'.tmap, S'.udot, S'.wdot, S'.stall, S'.ah, S'.au,
            S'.qd, S'.ah1, S'.au1, S'.pvz, S'.pvz2] do
    IO.println (s!"{x.v.lo} {x.v.hi} " ++ " ".intercalate (x.d.toList.map fun i => s!"{i.lo} {i.hi}"))

end PfJac
