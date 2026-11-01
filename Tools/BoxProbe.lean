import Jsb.Conformance
open Vibecheck Jsb

/-! `boxprobe`: how much each coordinate's range widens the interval vz/vx increments of one escape tick. -/

def S : Float := 65536.0
def rawF (x : Float) : Int := (x * S).round.toInt64.toInt

/-- Region bounds per coordinate (state fields then elevator), SI units. -/
def lo : List Float := [0, 600, 35, -4, 0.981, 0.03, 0.03, 1550, 61, -1.7, -6.4, 0, -2.4, 1.2, -0.3, -2.4, 1.1, -4.1, -4.2, 0.067]
def hi : List Float := [0, 1250, 45, 2.25, 0.9996, 0.19, 0.21, 2810, 91, 1.9, 0.1, 0, 2.1, 13.3, 0.47, 2.1, 13.4, 2.2, 2.2, 0.345]

def names : List String := ["x", "h", "vx", "vz", "dx", "dz", "q", "rpm", "tmap", "udot", "wdot", "stall", "ah", "au", "qd",
  "ah1", "au1", "pvz", "pvz2", "elev"]

def mk (f : Nat → Iv) : CLOf Iv :=
  ⟨⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩, f 19⟩

def ptAt (c : List Float) (i : Nat) : Iv := .box (rawF c[i]!) (rawF c[i]!)

def showIv : Iv → String
  | .box a b => s!"[{Float.ofInt a / S}, {Float.ofInt b / S}] w {Float.ofInt (b - a) / S}"
  | .top => "top"

def wd : Iv → Float
  | .box a b => Float.ofInt (b - a) / S
  | .top => 1e30

/-- Per-substep widths when only coordinate `d` is widened by `half`, against the sampled spread of 9 points. -/
def trace (d : Nat) (half : Float) : IO Unit := do
  let mid := (List.range 20).map fun i => (lo[i]! + hi[i]!) / 2
  let B := mk fun i => if i == d then .box (rawF (mid[i]! - half)) (rawF (mid[i]! + half)) else ptAt mid i
  let U := Escape.input B
  let samples : List (CLOf Fx) := (List.range 9).map fun k =>
    let v := mid[d]! - half + 2 * half * k.toFloat / 8
    let c := mk fun i => ptAt mid i
    let cf : CLOf Fx := c.map fun | .box a _ => ⟨a⟩ | .top => ⟨0⟩
    cf.set d ⟨rawF v⟩
  let mut S' := B.s
  let mut ss := samples.map fun c => c.s
  let us := samples.map Escape.input
  IO.println s!"input elev width {wd U.elev}"
  for k in [0:8] do
    S' := step 7 true U S'
    ss := (ss.zip us).map fun (s, u) => step 7 true u s
    let spread (f : State → Fx) : Float :=
      let vs := ss.map fun s => (f s).toFloat
      vs.foldl max (-1e30) - vs.foldl min 1e30
    IO.println s!"sub {k}: vx {wd S'.vx}/{spread (·.vx)} vz {wd S'.vz}/{spread (·.vz)} dz {wd S'.dz}/{spread (·.dz)} q {wd S'.q}/{spread (·.q)} au {wd S'.au}/{spread (·.au)} ah {wd S'.ah}/{spread (·.ah)} wdot {wd S'.wdot}/{spread (·.wdot)} qd {wd S'.qd}/{spread (·.qd)} rpm {wd S'.rpm}/{spread (·.rpm)}"

def r (x : Float) : Int := rawF x

def cons : List LinCon := [
  ⟨[(10, 3), (1, 2)], 0, r 1000⟩, ⟨[(1, 2), (-20, 3)], 0, r 1000⟩, ⟨[(40, 5), (-1, 3)], r 4.0, r 6.4⟩,
  ⟨[(1, 13), (-1, 16)], r (-0.13), r 0.13⟩, ⟨[(1, 12), (-1, 15)], r (-0.04), r 0.04⟩,
  ⟨[(1, 3), (-1, 17)], r (-0.11), r 0.11⟩, ⟨[(1, 17), (-1, 18)], r (-0.11), r 0.11⟩]

def dims : List (Nat × Int) := [(1, 32), (2, 40700), (3, 53900), (4, 525000), (5, 2690000), (6, 121000), (7, 23),
  (8, 10), (12, 2070), (13, 2380), (15, 610), (16, 620), (19, 70900)]

structure Stats where
  evals : Nat := 0
  leaves : Nat := 0
  infeasible : Nat := 0
  depth : Nat := 0
  fails : Nat := 0
  minWidth : Float := 1e9

/-- `checkRec` instrumented, giving up after `budget` interval evaluations. -/
partial def countRec (ok : CLOf Iv → Bool) (budget : Nat) (st : IO.Ref Stats) (n d : Nat) (B : CLOf Iv) : IO Bool := do
  if (← st.get).evals ≥ budget then return false
  if !allFeasible cons B then
    st.modify fun s => { s with infeasible := s.infeasible + 1, depth := Nat.max s.depth d }
    return true
  st.modify fun s => { s with evals := s.evals + 1 }
  if ok B then
    st.modify fun s => { s with leaves := s.leaves + 1, depth := Nat.max s.depth d }
    return true
  match n with
  | 0 => st.modify fun s => { s with fails := s.fails + 1 }; return false
  | n + 1 =>
    let h := halve B (pick dims B)
    let a ← countRec ok budget st n (d + 1) h.1
    if !a then return false
    countRec ok budget st n (d + 1) h.2

def regionAt (fr : Float) : CLOf Iv :=
  let mid := (List.range 20).map fun i => (lo[i]! + hi[i]!) / 2
  mk fun i => let h := (hi[i]! - lo[i]!) / 2 * fr; .box (rawF (mid[i]! - h)) (rawF (mid[i]! + h))

def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- Sampled minimum of the true increments over feasible points (vertices and random points) of a scaled region. -/
def sample (fr : Float) (n : Nat) : IO Unit := do
  let B := regionAt fr
  let mut seed : UInt64 := 12345
  let mut mz : Float := 1e9
  let mut mx : Float := 1e9
  let mut cnt := 0
  for k in [0:n] do
    let mut pt : List Int := []
    for i in [0:20] do
      seed := lcg seed
      let u := (seed >>> 11).toFloat / 9007199254740992.0
      let u := if k % 2 == 0 then (if u < 0.5 then 0.0 else 1.0) else u
      match B.get i with
      | .box a b => pt := pt ++ [a + ((Float.ofInt (b - a)) * u).toInt64.toInt]
      | .top => pt := pt ++ [0]
    let c : CLOf Fx := mk (fun i => .box pt[i]! pt[i]!) |>.map fun | .box a _ => ⟨a⟩ | .top => ⟨0⟩
    if cons.all fun l => decide (l.lo ≤ l.val c) && decide (l.val c ≤ l.hi) then
      cnt := cnt + 1
      let r := tickIncr c
      mz := min mz r.1.toFloat
      mx := min mx r.2.toFloat
  IO.println s!"scale {fr}: {cnt} feasible samples, min dvz {mz} min dvx {mx}"

def ivLit : Iv → String
  | .box a b => s!".box ({a}) ({b})"
  | .top => ".top"

def subB (B : CLOf Iv) (p : List Bool) : CLOf Iv :=
  p.foldl (fun B b => if b then (halve B (pick dims B)).2 else (halve B (pick dims B)).1) B

def main (args : List String) : IO Unit := do
  if args.head? == some "subcount" then
    let fr := args[1]!.toNat!.toFloat / 1000.0
    for p in [[false, false], [false, true], [true, false], [true, true]] do
      let st ← IO.mkRef ({} : Stats)
      let ok ← countRec (incrOK 2048 (-6554)) 200000 st 60 0 (subB (regionAt fr) p)
      let x ← st.get
      IO.println s!"{p}: ok {ok} evals {x.evals} leaves {x.leaves} depth {x.depth}"
    return
  if args.head? == some "emit" then
    let B := regionAt (args[1]!.toNat!.toFloat / 1000.0)
    IO.println s!"{(List.range 20).map fun i => ivLit (B.get i)}"
    IO.println s!"{cons.map fun l => (l.terms, l.lo, l.hi)}"
    IO.println s!"{dims}"
    return
  if args.head? == some "sample" then
    for f in args.drop 1 do sample (f.toNat!.toFloat / 1000.0) 20000
    return
  if args.head? == some "count" then
    let dvz := rawF ((args[1]!.toNat!).toFloat / 10000.0)
    let dvx := -rawF ((args[2]!.toNat!).toFloat / 10000.0)
    for f in args.drop 3 do
      let fr := f.toNat!.toFloat / 1000.0
      let st ← IO.mkRef ({} : Stats)
      let t0 ← IO.monoNanosNow
      let ok ← countRec (incrOK dvz dvx) 200000 st 60 0 (regionAt fr)
      let t1 ← IO.monoNanosNow
      let x ← st.get
      IO.println s!"scale {fr}: ok {ok} evals {x.evals} leaves {x.leaves} infeasible {x.infeasible} depth {x.depth} native {(t1 - t0).toFloat / 1e6} ms"
    return
  if args.head? == some "trace" then
    trace (args[1]!).toNat! (args[2]!.toNat!.toFloat / 1000.0)
    return
  let frac := (args.head?.bind String.toNat?).getD 100
  let fr : Float := frac.toFloat / 100.0
  let mid := (List.range 20).map fun i => (lo[i]! + hi[i]!) / 2
  let c0 := mk (ptAt mid)
  IO.println s!"centre: dvz {showIv (tickIncr c0).1} dvx {showIv (tickIncr c0).2}"
  for d in List.range 20 do
    let half := (hi[d]! - lo[d]!) / 2 * fr
    let B := mk fun i => if i == d then .box (rawF (mid[i]! - half)) (rawF (mid[i]! + half)) else ptAt mid i
    let r := tickIncr B
    IO.println s!"{names[d]!} ±{half}: dvz {showIv r.1} dvx {showIv r.2}"
  let half (i : Nat) := (hi[i]! - lo[i]!) / 2 * fr
  let Bf := mk fun i => .box (rawF (mid[i]! - half i)) (rawF (mid[i]! + half i))
  IO.println s!"all: dvz {showIv (tickIncr Bf).1} dvx {showIv (tickIncr Bf).2}"
