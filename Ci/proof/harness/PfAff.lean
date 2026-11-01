import Ci.proof.T
open Vibecheck Jsb

/-! Unverified affine-arithmetic prototype of the model (Float, raw units), to measure how tight an affine
enclosure of one tick over a piece of T is, before anyone builds a verified one. Each value is
`c + Σ a_i ε_i ± e` with noise symbols `ε_i ∈ [-1, 1]`; every Fx rounding adds 1 raw to `e`; nonlinear unary
functions are linearised on the input range by the secant, with the residual measured by sampling the actual Fx
function. Not a proof of anything. -/

structure Aff where
  c : Float
  a : Array Float
  e : Float
  deriving Inhabited

namespace Aff
def N : Nat := 18
def zeros : Array Float := Array.replicate N 0
def rad (x : Aff) : Float := x.a.foldl (fun s v => s + v.abs) 0 + x.e
def lo (x : Aff) : Float := x.c - x.rad
def hi (x : Aff) : Float := x.c + x.rad
def const (v : Float) : Aff := ⟨v, zeros, 0⟩
def zipW (f : Float → Float → Float) (u v : Array Float) : Array Float :=
  let n := max u.size v.size
  (Array.range n).map fun i => f (u.getD i 0) (v.getD i 0)

initialize freshRef : IO.Ref Nat ← IO.mkRef 0
/-- A fresh noise symbol index (unverified prototype: a global counter, threaded through a data dependency). -/
@[noinline] unsafe def freshImpl (salt : Float) : Nat :=
  unsafeBaseIO (freshRef.modifyGet fun n => (n + N + (if salt == salt then 0 else 1), n + 1))
@[implemented_by freshImpl] opaque fresh (salt : Float) : Nat
def FRESH : Bool := true
/-- put `w` on a new noise symbol (or lump it into `e` when FRESH is off) -/
def withFresh (x : Aff) (w : Float) : Aff :=
  if !FRESH || w == 0 then { x with e := x.e + w } else
  let k := fresh (x.c + w)
  let a := if x.a.size ≤ k then x.a ++ Array.replicate (k + 1 - x.a.size) 0 else x.a
  { x with a := a.set! k w }
def add (x y : Aff) : Aff := ⟨x.c + y.c, zipW (· + ·) x.a y.a, x.e + y.e⟩
def sub (x y : Aff) : Aff := ⟨x.c - y.c, zipW (· - ·) x.a y.a, x.e + y.e⟩
def scale (s : Float) (x : Aff) : Aff := ⟨s * x.c, x.a.map (s * ·), s.abs * x.e⟩
def addErr (x : Aff) (r : Float) : Aff := { x with e := x.e + r }
/-- rounding errors also on fresh symbols (defined after `withFresh`) -/
def hull (x y : Aff) : Aff := let l := min x.lo y.lo; let h := max x.hi y.hi; withFresh ⟨(l + h) / 2, zeros, 0⟩ ((h - l) / 2)
/-- raw product `x y / 65536` floored (as `fmul`) -/
def mulRaw (x y : Aff) : Aff :=
  let rx := x.rad - x.e; let ry := y.rad - y.e
  let c := x.c * y.c
  let a := zipW (fun p q => x.c * q + y.c * p) x.a y.a
  let e := x.c.abs * y.e + y.c.abs * x.e + x.e * (ry + y.e) + y.e * rx
  withFresh (withFresh (scale (1 / 65536) ⟨c, a, e⟩) (rx * ry / 65536)) 1
/-- secant linearisation of a unary raw function on the input range, residual by sampling -/
def unary (f : Int → Int) (x : Aff) : Aff :=
  let l := x.lo; let h := x.hi
  if h - l < 1 then withFresh (const (Float.ofInt (f (Float.round x.c).toInt64.toInt))) (x.rad + 2) else
  let fl := Float.ofInt (f l.ceil.toInt64.toInt); let fh := Float.ofInt (f h.floor.toInt64.toInt)
  let s := (fh - fl) / (h - l)
  let pts := (List.range 65).map fun k => l + (h - l) * k.toFloat / 64
  let res := pts.map fun t => Float.ofInt (f t.round.toInt64.toInt) - s * t
  let rmin := res.foldl min 1e300; let rmax := res.foldl max (-1e300)
  let d := (rmax + rmin) / 2
  -- curvature between samples and rounding: 10 % of the residual band plus 2 raw
  withFresh (withFresh ⟨s * x.c + d, x.a.map (s * ·), s.abs * x.e⟩ ((rmax - rmin) / 2 * 1.1 + s.abs * (h - l) / 64)) 2
/-- secant linearisation of a real (Float) function, residual by sampling (no grid rounding) -/
def unaryF (f : Float → Float) (x : Aff) : Aff :=
  let l := x.lo; let h := x.hi
  if h - l < 1e-9 then ⟨f x.c, zeros, 0⟩ else
  let s := (f h - f l) / (h - l)
  let pts := (List.range 65).map fun k => l + (h - l) * k.toFloat / 64
  let res := pts.map fun t => f t - s * t
  let rmin := res.foldl min 1e300; let rmax := res.foldl max (-1e300)
  let d := (rmax + rmin) / 2
  withFresh ⟨s * x.c + d, x.a.map (s * ·), s.abs * x.e⟩ ((rmax - rmin) / 2 * 1.1 + 1e-9)
def decLt (x y : Aff) : Option Bool := if x.hi < y.lo then some true else if y.hi ≤ x.lo then some false else none
def decLe (x y : Aff) : Option Bool := if x.hi ≤ y.lo then some true else if y.hi < x.lo then some false else none
end Aff

instance : Scalar Aff where
  add := Aff.add
  sub := Aff.sub
  neg x := Aff.scale (-1) x
  mul := Aff.mulRaw
  div x y := -- fdiv: x 65536 / y = x * (2^32 / y) / 65536, floored
    Aff.withFresh (Aff.mulRaw x (Aff.unaryF (fun t => 4294967296 / t) y)) 1
  max x y := match Aff.decLe x y with | some true => y | some false => x | none => Aff.hull x y
  min x y := match Aff.decLe x y with | some true => x | some false => y | none => Aff.hull x y
  lit r := Aff.const (Float.ofInt r)
  mulR x y := Aff.withFresh (Aff.mulRaw x y) 1
  shr x k := Aff.withFresh (Aff.scale (1 / (2 ^ k.toFloat)) x) 1
  ab3 a b c := Aff.withFresh (Aff.scale (1 / 12) (Aff.add (Aff.sub (Aff.scale 23 a) (Aff.scale 16 b)) (Aff.scale 5 c))) 1
  abs x := if 0 ≤ x.lo then x else if x.hi ≤ 0 then Aff.scale (-1) x else Aff.hull x (Aff.scale (-1) x)
  sqrt x := Aff.unary (fun t => (sqrtFx ⟨t⟩).raw) x
  atan2 w u := -- u > 0 on our boxes: atan(w/u)
    let q := Aff.mulRaw w (Aff.unaryF (fun t => 4294967296 / t) u)
    Aff.unary (fun t => (atan2Fx ⟨t⟩ ⟨65536⟩).raw) q
  tbl1 t x := Aff.unary (fun v => (Tbl1.eval t ⟨v⟩).raw) x
  tbl2 t r c := if c.hi - c.lo < 1 then Aff.unary (fun v => (Tbl2.eval t ⟨v⟩ ⟨(Float.round c.c).toInt64.toInt⟩).raw) r
    else Aff.hull (Aff.const (Float.ofInt (Tbl2.eval t ⟨(Float.round r.lo).toInt64.toInt⟩ ⟨0⟩).raw)) (Aff.const 0)
  atm tab x := Aff.unary (fun v => (atmLookup tab ⟨v⟩).raw) x
  selLt a b t e := match Aff.decLt a b with | some true => t | some false => e | none => Aff.hull t e
  selLe a b t e := match Aff.decLe a b with | some true => t | some false => e | none => Aff.hull t e
  rnC c s := Aff.withFresh (Aff.mulRaw c (Aff.sub (Aff.const 98304)
    (Aff.withFresh (Aff.scale (1 / 2) (Aff.add (Aff.mulRaw c c) (Aff.mulRaw s s))) 1))) 1
  rnS c s := Aff.withFresh (Aff.mulRaw s (Aff.sub (Aff.const 98304)
    (Aff.withFresh (Aff.scale (1 / 2) (Aff.add (Aff.mulRaw c c) (Aff.mulRaw s s))) 1))) 1

namespace PfAff
open Ci.Lawfirst

def toFx (v : Float) : Fx := ⟨v.round.toInt64.toInt⟩

/-- Law elevator as an affine form: central differences along each noise symbol, residual by random sampling. -/
def lawAff (sel : Input × Mem → Int) (cen : Array Float) (rows : Array (Array Float)) (seed : Nat) : Aff := Id.run do
  let pt := fun (eps : Array Float) =>
    let v := fun (i : Nat) => cen[i]! + ((rows[i]!).zip eps).foldl (fun s (r, e) => s + r * e) 0
    let s : State := ⟨toFx (v 0), toFx (v 1), toFx (v 2), toFx (v 3), toFx (v 4), toFx (v 5), toFx (v 6), toFx (v 7),
      toFx (v 8), toFx (v 9), toFx (v 10), toFx (v 11), toFx (v 12), toFx (v 13), toFx (v 14), toFx (v 15), toFx (v 16),
      toFx (v 17), toFx (v 18)⟩
    let m : Mem := ⟨(v 19).round.toInt64.toInt, (v 20).round.toInt64.toInt⟩
    Float.ofInt (sel (Ci.Proof.step m s))
  let z := Aff.zeros
  let f0 := pt z
  let mut a := z
  for k in [0:Aff.N] do
    let ep := z.set! k 1; let em := z.set! k (-1)
    a := a.set! k ((pt ep - pt em) / 2)
  let mut err : Float := 0
  let mut r := seed
  for _ in [0:256] do
    let mut eps := z
    for k in [0:Aff.N] do
      r := (r * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      eps := eps.set! k (if (r >>> 33) % 2 == 0 then -1 else 1)
    let lin := f0 + (a.zip eps).foldl (fun s (p, q) => s + p * q) 0
    err := max err (pt eps - lin).abs
  return ⟨f0, a, err * 1.5 + 2⟩

def run : IO Unit := do
  let stdin ← IO.getStdin
  let readRow : IO (Array Float) := do
    let l ← stdin.getLine
    return ((l.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map (fun w => (w.toInt!.toFloat : Float))).toArray
  let readRowF : IO (Array Float) := do
    let l ← stdin.getLine
    return ((l.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map (fun w => (String.toNat! (w.replace "." "")).toFloat)).toArray
  let _ := readRowF
  let cen ← readRow
  let mut rows : Array (Array Float) := #[]
  for _ in [0:21] do
    let l ← stdin.getLine
    rows := rows.push (((l.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map (fun w => (w.toInt!.toFloat / 1000.0 : Float))).toArray)
  let fld := fun (i : Nat) => (⟨cen[i]!, rows[i]!, 0⟩ : Aff)
  let S : StateOf Aff := ⟨fld 0, fld 1, fld 2, fld 3, fld 4, fld 5, fld 6, fld 7, fld 8, fld 9, fld 10, fld 11, fld 12,
    fld 13, fld 14, fld 15, fld 16, fld 17, fld 18⟩
  let el := lawAff (fun r => r.1.elev.raw) cen rows 7
  let eIa := lawAff (fun r => r.2.eI) cen rows 11
  let elc : Aff := { el with c := max (-65536) (min 65536 el.c) }
  let h0 := cen[1]!.round.toInt64.toInt
  let U : InputOf Aff := ⟨elc, Aff.const (Float.ofInt (Ci.Proof.thrH h0)), Aff.const 0, Aff.const 0⟩
  let nsub := (← IO.getEnv "NSUB").bind String.toNat? |>.getD 8
  let S' := iter nsub (Jsb.step 7 true U) S
  let out := fun (x : Aff) => s!"{x.c} {x.e} " ++ " ".intercalate (x.a.toList.map toString)
  if (← IO.getEnv "PROBE").isSome then
    let pr := (Jsb.evaluate 7 U (Jsb.integrate 7 true S)).2
    for (nm, x) in [("rho", pr.rho), ("alpha", pr.alpha), ("adot", pr.adot), ("qbar", pr.qbar), ("fxA", pr.fxA),
        ("fzA", pr.fzA), ("mA", pr.mA), ("thrust", pr.thrustKN), ("hp", pr.hp), ("vind", pr.vind), ("cl", pr.cl),
        ("cd", pr.cd), ("tipM", pr.tipMach), ("ct", pr.ct), ("adv", pr.adv)] do
      IO.println s!"{nm} {x.c} err {x.e} rad {x.rad}"
  IO.println s!"elev {out el}"
  for x in [S'.x, S'.h, S'.vx, S'.vz, S'.dx, S'.dz, S'.q, S'.rpm, S'.tmap, S'.udot, S'.wdot, S'.stall, S'.ah, S'.au,
            S'.qd, S'.ah1, S'.au1, S'.pvz, S'.pvz2] do
    IO.println (out x)
  IO.println (out eIa)

end PfAff
