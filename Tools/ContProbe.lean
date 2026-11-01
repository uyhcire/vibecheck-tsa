import Jsb.Conformance
open Vibecheck Jsb

/-! `contprobe`: sampled margins for the continuous-model pilot; `Float` stands in for the real-number model. -/

namespace Jsb.ContProbe

def S : Float := 65536.0
def ofRaw (r : Int) : Float := Float.ofInt r / S
def rawF (x : Float) : Int := (x * S).round.toInt64.toInt

def segF (xs : Array Int) (x : Float) : Nat := Id.run do
  let mut i := 0
  for k in [0:xs.size] do
    if k + 2 < xs.size ∧ ofRaw xs[k + 1]! ≤ x then i := k + 1
  return i

def lerpF (x0 x1 y0 y1 x : Float) : Float := if x1 > x0 then y0 + (y1 - y0) * (x - x0) / (x1 - x0) else y0

def tbl1F (t : Tbl1) (x : Float) : Float :=
  let n := t.xs.size
  if x ≤ ofRaw t.xs[0]! then ofRaw t.ys[0]! else if ofRaw t.xs[n - 1]! ≤ x then ofRaw t.ys[n - 1]! else
  let i := segF t.xs x
  lerpF (ofRaw t.xs[i]!) (ofRaw t.xs[i + 1]!) (ofRaw t.ys[i]!) (ofRaw t.ys[i + 1]!) x

def tbl2F (t : Tbl2) (r c : Float) : Float :=
  let nc := t.cols.size
  let rc := max (ofRaw t.rows[0]!) (min (ofRaw t.rows[t.rows.size - 1]!) r)
  let cc := max (ofRaw t.cols[0]!) (min (ofRaw t.cols[nc - 1]!) c)
  let i := segF t.rows rc
  let j := segF t.cols cc
  let cell (a b : Nat) : Float := ofRaw t.data[a * nc + b]!
  let row (a : Nat) : Float := lerpF (ofRaw t.cols[j]!) (ofRaw t.cols[j + 1]!) (cell a j) (cell a (j + 1)) cc
  lerpF (ofRaw t.rows[i]!) (ofRaw t.rows[i + 1]!) (row i) (row (i + 1)) rc

def atmF (tab : Array Int) (h : Float) : Float :=
  let hc := max 0 (min (50 * 159) h)
  let i := (hc / 50).floor.toUInt64.toNat
  let i := min i 158
  lerpF (50 * i.toFloat) (50 * (i + 1).toFloat) (ofRaw tab[i]!) (ofRaw tab[i + 1]!) hc

instance : Max Float := ⟨fun a b => if a ≤ b then b else a⟩
instance : Min Float := ⟨fun a b => if a ≤ b then a else b⟩

instance instScalarFloat : Scalar Float where
  add := (· + ·)
  sub := (· - ·)
  neg x := -x
  mul := (· * ·)
  div a b := if b == 0 then 0 else a / b
  max a b := if a ≤ b then b else a
  min a b := if a ≤ b then a else b
  lit := ofRaw
  mulR := (· * ·)
  shr a k := a / (2 ^ k.toFloat)
  ab3 a b c := (23 * a - 16 * b + 5 * c) / 12
  abs := Float.abs
  sqrt x := if x ≤ 0 then 0 else Float.sqrt x
  atan2 := Float.atan2
  tbl1 := tbl1F
  tbl2 := tbl2F
  atm := atmF
  selLt a b t e := if a < b then t else e
  selLe a b t e := if a ≤ b then t else e
  rnC c s := c * (1.5 - (c * c + s * s) / 2)
  rnS c s := s * (1.5 - (c * c + s * s) / 2)

def regionCons : List LinCon :=
  [⟨[(10, 3), (1, 2)], 0, 65536000⟩, ⟨[(1, 2), (-20, 3)], 0, 65536000⟩, ⟨[(40, 5), (-1, 3)], 262144, 419430⟩,
   ⟨[(1, 13), (-1, 16)], -8520, 8520⟩, ⟨[(1, 12), (-1, 15)], -2621, 2621⟩, ⟨[(1, 3), (-1, 17)], -7209, 7209⟩,
   ⟨[(1, 17), (-1, 18)], -7209, 7209⟩]

def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- Region coordinates (as in `Tools/BoxProbe.lean`). -/
def lo : List Float := [0, 600, 35, -4, 0.981, 0.03, 0.03, 1550, 61, -1.7, -6.4, 0, -2.4, 1.2, -0.3, -2.4, 1.1, -4.1, -4.2, 0.067]
def hi : List Float := [0, 1250, 45, 2.25, 0.9996, 0.19, 0.21, 2810, 91, 1.9, 0.1, 0, 2.1, 13.3, 0.47, 2.1, 13.4, 2.2, 2.2, 0.345]

def mkS (f : Nat → Float) : StateOf Float :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩

def toFx (s : StateOf Float) : StateOf Fx := s.map fun x => ⟨rawF x⟩
def ofFx (s : StateOf Fx) : StateOf Float := s.map Fx.toFloat

/-- Physical region test (`cons` of `EscapeRegion` in SI units, plus the box on the physical coordinates). -/
def physOK (h vx vz dx dz q rpm tmap elev : Float) : Bool :=
  600 ≤ h && h ≤ 1250 && 35 ≤ vx && vx ≤ 45 && -4 ≤ vz && vz ≤ 2.25 && 0.981 ≤ dx && dx ≤ 0.9996 &&
  0.03 ≤ dz && dz ≤ 0.19 && 0.03 ≤ q && q ≤ 0.21 && 1550 ≤ rpm && rpm ≤ 2810 && 61 ≤ tmap && tmap ≤ 91 &&
  0.067 ≤ elev && elev ≤ 0.345 && 10 * vz + vx ≥ 0 && vx - 20 * vz ≥ 0 && 40 * dz - vz ≥ 4.0 && 40 * dz - vz ≤ 6.4

structure Acc where
  n : Nat := 0
  mz : Float := 1e9
  mx : Float := 1e9
  worstX : List Float := []
  worstZ : List Float := []
  mauk : Float := 1e9
  mahk : Float := 1e9
  maxErrAu : Float := 0
  maxErrAh : Float := 0
  maxErrQd : Float := 0
  mauR : Float := 1e9
  mahR : Float := 1e9
  maxUnit : Float := 0

def inp (e : Float) : InputOf Float := ⟨e, 1, 0, 0⟩

def consistent (h vx vz dx dz q rpm tmap elev : Float) : StateOf Fx :=
  let s0 : StateOf Float := { x := 0, h, vx, vz, dx, dz, q, rpm, tmap, udot := 0, wdot := 0, stall := 0,
                              ah := 0, au := 0, qd := 0, ah1 := 0, au1 := 0, pvz := vz, pvz2 := vz }
  let u : InputOf Fx := ⟨⟨rawF elev⟩, 1, 0, 0⟩
  let f0 := toFx s0
  let e1 := (evaluate 7 u f0).1
  let e2 := (evaluate 7 u { f0 with udot := e1.udot, wdot := e1.wdot }).1
  { f0 with udot := e2.udot, wdot := e2.wdot, ah := e2.ah, au := e2.au, qd := e2.qd, ah1 := e2.ah, au1 := e2.au }

def run (mode : String) (n : Nat) (unitAtt : Bool) : IO Unit := do
  let mut seed : UInt64 := 987654321
  let mut a : Acc := {}
  let mut tries := 0
  while a.n < n && tries < 200 * n do
    tries := tries + 1
    let mut u : Array Float := #[]
    for _ in [0:20] do
      seed := lcg seed
      let r := (seed >>> 11).toFloat / 9007199254740992.0
      u := u.push (if tries % 3 == 0 then (if r < 0.5 then 0.0 else 1.0) else r)
    let g (i : Nat) := lo[i]! + (hi[i]! - lo[i]!) * u[i]!
    let h := g 1; let vx := g 2; let vz := g 3; let q := g 6; let rpm := g 7; let tmap := g 8; let elev := g 19
    let (dx, dz) := if unitAtt then
        let dz := vz / 40.0 + 0.10 + 0.06 * u[5]!
        (Float.sqrt (1 - dz * dz), dz)
      else (g 4, g 5)
    if !physOK h vx vz dx dz q rpm tmap elev then continue
    let c : CLOf Fx := if mode == "box" then
        let s := mkS g
        let s := { s with dx, dz }
        let cf : CLOf Fx := ⟨toFx s, ⟨rawF elev⟩⟩
        if (regionCons.all fun l => decide (l.lo ≤ l.val cf) && decide (l.val cf ≤ l.hi)) then cf else ⟨toFx s, ⟨0⟩⟩
      else ⟨consistent h vx vz dx dz q rpm tmap elev, ⟨rawF elev⟩⟩
    if c.elev.raw == 0 then continue
    a := { a with n := a.n + 1 }
    let r := tickIncr c
    let pt := [h, vx, vz, dx, dz, q, rpm, tmap, elev, c.s.ah.toFloat, c.s.au.toFloat, c.s.udot.toFloat, c.s.wdot.toFloat]
    if r.1.toFloat < a.mz then a := { a with mz := r.1.toFloat, worstZ := pt }
    if r.2.toFloat < a.mx then a := { a with mx := r.2.toFloat, worstX := pt }
    let ui := Escape.input c
    let uf : InputOf Float := ⟨ui.elev.toFloat, 1, 0, 0⟩
    let mut st := c.s
    for _ in [0:8] do
      let si := integrate 7 true st
      let ef := (evaluate 7 ui si).1
      let er := (evaluate 7 uf (ofFx si)).1
      a := { a with mauk := min a.mauk ef.au.toFloat, mahk := min a.mahk ef.ah.toFloat,
                    mauR := min a.mauR er.au, mahR := min a.mahR er.ah,
                    maxErrAu := max a.maxErrAu (Float.abs (ef.au.toFloat - er.au)),
                    maxErrAh := max a.maxErrAh (Float.abs (ef.ah.toFloat - er.ah)),
                    maxErrQd := max a.maxErrQd (Float.abs (ef.qd.toFloat - er.qd)),
                    maxUnit := max a.maxUnit (Float.abs (ef.dx.toFloat ^ 2 + ef.dz.toFloat ^ 2 - 1)) }
      st := ef
  IO.println s!"mode {mode} unit {unitAtt}: {a.n} samples ({tries} tries)"
  IO.println s!"  IncrProp margins: min dvz {a.mz} (need ≥ 0.03125), min dvx {a.mx} (need ≥ -0.1)"
  IO.println s!"  worst dvx at [h vx vz dx dz q rpm tmap elev ah au udot wdot] = {a.worstX}"
  IO.println s!"  worst dvz at {a.worstZ}"
  IO.println s!"  substep evaluations: min au Fx {a.mauk} / Float {a.mauR}; min ah Fx {a.mahk} / Float {a.mahR}"
  IO.println s!"  max |Fx - Float| per evaluation: au {a.maxErrAu}, ah {a.maxErrAh}, qd {a.maxErrQd}; max |dx²+dz²-1| {a.maxUnit}"

end Jsb.ContProbe

open Jsb.ContProbe in
def main (args : List String) : IO Unit := do
  let n := (args[1]?.bind String.toNat?).getD 2000
  match args.head? with
  | some "box" => run "box" n false; run "box" n true
  | some "cons" => run "cons" n true; run "cons" n false
  | _ => IO.println "usage: contprobe (box|cons) [n]"
