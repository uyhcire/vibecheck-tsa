import Ci.Report
import Ci.Bench
import Ci.Goals
import Tools.EnvConf
open Vibecheck Jsb Ci

namespace Ci.Gen
def parseF' (s : String) : Float := Jsb.EnvConf.parseF s
end Ci.Gen

/-! `ciscore`: the CI referee (scoreboard-owned). Rules and score definition: `docs/ci/README.md`. -/

namespace Ci.Score

def F (x : Int) : Float := Float.ofInt x / 65536
def FN (n : Nat) : Float := n.toFloat

def sorted (xs : Array Float) : Array Float := xs.qsort (· < ·)
def pct (xs : Array Float) (p : Float) : Float :=
  if xs.isEmpty then 0 else
  let s := sorted xs
  s[min (s.size - 1) (p * FN (s.size - 1)).round.toUInt64.toNat]!
def median (xs : Array Float) : Float := pct xs 0.5
def mean (xs : Array Float) : Float := if xs.isEmpty then 0 else xs.foldl (· + ·) 0 / FN xs.size
def maxF (xs : Array Float) : Float := xs.foldl max 0

def fmt (x : Float) : String :=
  if x.isNaN || x.isInf then "null" else toString ((x * 10000).round / 10000)

@[noinline] def timed {β : Type} (f : Unit → β) : IO (β × Float) := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  let t1 ← IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1000)

structure StateRes where
  e : Entry
  accepted : Bool
  law : Nat
  loss : Float
  ticks : Nat
  spent : Nat
  us : Float
  hstar : Option Float
  ticksH : Nat
  usH : Float
  why : String

def classify (s : State) : String :=
  if !alphaOk s then "alpha" else if !loadOk s then "load" else if !speedOk s then "speed"
  else if s.stall.raw != 0 then "stall" else "clearance"

def failKind (L : Law) (c : Commit) (i : Nat) : String := Id.run do
  let mut s := c.s
  let mut m := L.init c
  let mut idx := 0
  for _ in [0:i / 8 + 1] do
    let r := L.step m s
    let u := clampInput r.1
    for _ in [0:8] do
      s := sub u s
      if idx == i then return classify s
      idx := idx + 1
    m := r.2
  return "?"

def rejectWhy (S : Submission) (c : Commit) : String :=
  ";".intercalate (S.laws.map fun L =>
    let r := rollLaw L c S.horizon
    match r.fail with
    | some i => s!"{L.name}:{failKind L c i}@tick{i / 8}"
    | none => s!"{L.name}:T-not-reached")

/-- Lowest commit height on a 0.25 m grid, from 1 m below `clearance + loss`, at which the filter accepts:
a 12 m scan, then bisection up to the stored altitude (assumes acceptance is monotone in height there). -/
def hstar (S : Submission) (c : Commit) (loss : Int) : Option (Int × Nat × Nat) := Id.run do
  let q : Int := 16384
  let start := ((clearance + loss + q - 1) / q) * q - 4 * q
  for j in [0:48] do
    let hc := start + j * q
    if let (some (_, r), t) := check S (c.atHeight hc) then return some (hc, r.ticks, t)
  let mut lo := start + 47 * q
  let mut hi := (c.s.h.raw / q) * q
  let some (best, tk, sp) := (match check S (c.atHeight hi) with
    | (some (_, r), t) => some (hi, r.ticks, t) | _ => none) | return none
  let mut res := (best, tk, sp)
  while hi - lo > q do
    let mid := ((lo + hi) / 2 / q) * q
    if mid ≤ lo then break
    match check S (c.atHeight mid) with
    | (some (_, r), t) => hi := mid; res := (mid, r.ticks, t)
    | _ => lo := mid
  return some res

def runBench (S : Submission) (es : Array Entry) : IO (Array StateRes) := do
  let mut out := #[]
  for e in es do
    let ((res, spent), us) ← timed fun _ => check S e.c
    match res with
    | some (i, r) =>
      let loss := e.c.s.h.raw - r.hMin
      let ((hs, _), usH) ← timed fun _ => (hstar S e.c loss, 0)
      out := out.push { e, accepted := true, law := i, loss := F loss, ticks := r.ticks, spent, us,
                        hstar := hs.map (F ·.1), ticksH := (hs.map (·.2.1)).getD 0, usH, why := "" }
    | none =>
      out := out.push { e, accepted := false, law := 0, loss := 0, ticks := 0, spent, us, hstar := none,
                        ticksH := 0, usH := 0, why := rejectWhy S e.c }
  return out

/-- Climb-out window at the end of every T test: the last 10 s must climb at every tick. -/
def climbWindow : Nat := 160

/-- Fly `M` ticks from a T state; `none` when every substep is safe and the last `climbWindow` ticks climb. -/
def testT (L : Law) (p : State × L.σ) (M : Nat) : Option String := Id.run do
  let mut s := p.1
  let mut m := p.2
  let mut lastNoClimb : Option Nat := none
  for k in [0:M] do
    let r := tickT L s m
    if !r.safe then
      let u := clampInput (L.step m s).1
      let mut s' := s
      let mut kind := "?"
      for _ in [0:8] do
        s' := sub u s'
        if kind == "?" && !safeOk s' then kind := classify s'
      return some s!"{kind}@tick{k}"
    if !r.climb then lastNoClimb := some k
    s := r.s; m := r.m
  match lastNoClimb with
  | some k => if k + climbWindow ≥ M then some s!"no-climb@tick{k}" else none
  | none => none

def rollToT (L : Law) (c : Commit) (n : Nat) : Option (State × L.σ) := Id.run do
  let mut s := c.s
  let mut m := L.init c
  for _ in [0:n + 1] do
    if L.inT (s, m) then return some (s, m)
    let r := tickT L s m
    s := r.s; m := r.m
  return none

def vecOf (L : Law) (p : State × L.σ) : Array Int := (stateRaw p.1).toArray ++ L.enc p.2

def unvec (L : Law) (v : Array Int) : Option (State × L.σ) := do
  let dz := max (-65536) (min 65536 v[5]!)
  let dzf := F dz
  let dx : Int := (Float.sqrt (1 - dzf * dzf) * 65536).round.toInt64.toInt
  let v := (v.set! 5 dz).set! 4 dx
  let m ← L.dec (v.extract 19 v.size)
  some (stateOfRaw v 0, m)

/-- Raw units. -/
def minScale : Array Int :=
  #[0, 5 * 65536, 32768, 32768, 0, 655, 1311, 20 * 65536, 65536, 13107, 13107, 0, 13107, 13107, 13107, 13107,
    13107, 19661, 19661]

structure CE where
  kind : String
  why : String
  vec : Array Int

structure AdvRes where
  tests : Nat
  longTests : Nat
  inTSamples : Nat
  ces : Array CE

def adversary (L : Law) (seeds : Array (State × L.σ)) (budget : Nat) (longN : Nat) (seed : UInt64) : AdvRes := Id.run do
  if seeds.isEmpty then return ⟨0, 0, 0, #[]⟩
  let vs := seeds.map (vecOf L)
  let d := vs[0]!.size
  let idx : Array Nat := (List.range d).toArray
  let lo : Array Int := idx.map fun j => vs.foldl (fun a v => min a v[j]!) (vs[0]![j]!)
  let hi : Array Int := idx.map fun j => vs.foldl (fun a v => max a v[j]!) (vs[0]![j]!)
  let scale : Array Int := idx.map fun j =>
    if j < 19 then (if minScale[j]! == 0 then (0 : Int) else max minScale[j]! ((hi[j]! - lo[j]!) / 2))
    else max (655 : Int) ((hi[j]! - lo[j]!) / 2)
  let mut r : Ci.Rng := ⟨seed⟩
  let mut ces : Array CE := #[]
  let mut tests := 0
  let mut inT := 0
  let tryTest (kind : String) (p : State × L.σ) (M : Nat) : Option CE :=
    (testT L p M).map fun why => ⟨kind, why, vecOf L p⟩
  let stride := max 1 (seeds.size / max 1 (budget / 6))
  let mut i := 0
  while i < seeds.size do
    tests := tests + 1
    if let some p := seeds[i]? then
      if let some ce := tryTest "entry" p 640 then ces := ces.push ce
    i := i + stride
  for t in [0:budget] do
    let (x, r1) := r.next; r := r1
    let base := vs[(x % vs.size.toUInt64).toNat]!
    let mode := t % 5
    let mut cand : Option (State × L.σ) := none
    if mode == 0 then
      let mut tries := 0
      while cand.isNone && tries < 20 do
        tries := tries + 1
        let (amp, r2) := r.pick #[0.05, 0.2, 0.5, 1.0]; r := r2
        let mut v := base
        for j in [0:d] do
          let (u, r3) := r.unif (-1) 1; r := r3
          v := v.set! j (v[j]! + (amp * u * Float.ofInt scale[j]!).round.toInt64.toInt)
        if let some p := unvec L v then
          inT := inT + 1
          if L.inT p then cand := some p
    else if mode == 1 then
      let mut a : Int := clearance
      let mut b : Int := base[1]!
      let atH (h : Int) : Option (State × L.σ) := (unvec L (base.set! 1 h)).filter L.inT
      if (atH a).isSome then cand := atH a else
      for _ in [0:24] do
        let mid := (a + b) / 2
        if (atH mid).isSome then b := mid else a := mid
      cand := atH b
    else if mode == 2 then
      let mut dir : Array Float := #[]
      for _ in [0:d] do
        let (u, r3) := r.unif (-1) 1; r := r3
        dir := dir.push u
      let atT (tt : Float) : Option (State × L.σ) :=
        (unvec L (idx.map fun j =>
          (base[j]! + (tt * dir[j]! * Float.ofInt scale[j]!).round.toInt64.toInt : Int))).filter L.inT
      let mut a := 0.0
      let mut b := 4.0
      if (atT b).isSome then cand := atT b else
      for _ in [0:16] do
        let mid := (a + b) / 2
        if (atT mid).isSome then a := mid else b := mid
      cand := atT a
    else if mode == 4 then
      let mut v := base
      for j in [0:d] do
        let (u, r3) := r.unif (-1) 1; r := r3
        v := v.set! j (v[j]! + (u * Float.ofInt scale[j]!).round.toInt64.toInt)
      if let some p := unvec L v then
        let mut q := p
        for _ in [0:8] do
          if cand.isNone then
            let rr := tickT L q.1 q.2
            q := (rr.s, rr.m)
            if L.inT q then cand := some q
    else
      let mut tries := 0
      while cand.isNone && tries < 200 do
        tries := tries + 1
        let mut v := base
        for j in [0:d] do
          if j < 19 && minScale[j]! == 0 then continue
          let w := hi[j]! - lo[j]!
          let (u, r3) := r.unif (-0.5) 1.5; r := r3
          v := v.set! j (lo[j]! + (u * Float.ofInt w).round.toInt64.toInt)
        if let some p := unvec L v then
          inT := inT + 1
          if L.inT p then cand := some p
    if let some p := cand then
      tests := tests + 1
      if let some ce := tryTest s!"mode{mode}" p 640 then ces := ces.push ce
  let mut longT := 0
  let lstride := max 1 (seeds.size / max 1 longN)
  let mut k := 0
  while k < seeds.size && longT < longN do
    longT := longT + 1
    if let some p := seeds[k]? then
      if let some ce := tryTest "long" p 1920 then ces := ces.push ce
    k := k + lstride
  return ⟨tests, longT, inT, ces⟩

/-! ### Falsifier: a second, structural attack on T

The seeded adversary above runs a full 640-tick test per candidate, which caps it at a few hundred in-T
candidates per seed. The falsifier screens many more candidates with a short test, ranks them by how close
they come to the envelope, and hill-climbs the closest ones along the boundary of T. Any envelope failure in a
short test is a genuine counterexample (the full test would fail at the same tick). Every 16th candidate also
gets the full test, which catches `no-climb`. -/

/-- Normalised distance to the envelope over a short flight, one entry per limit: α (per 0.05 rad of tan α),
load (per 0.5 g), speed (per 2 m/s), height above clearance (per 2 m). Negative means violated. -/
structure Margins where
  a : Float
  n : Float
  v : Float
  h : Float
  deriving Inhabited

def Margins.min (m : Margins) : Float := Min.min (Min.min m.a m.n) (Min.min m.v m.h)

def Margins.get (m : Margins) (k : Nat) : Float :=
  match k with | 0 => m.a | 1 => m.n | 2 => m.v | _ => m.h

def stateMargins (s : State) : Margins :=
  let u := s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw
  let w := s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw
  let a := if u ≤ 0 then -1.0 else Float.ofInt (alphaTanMax * u - w * 65536) / (Float.ofInt u * 65536) / 0.05
  let n := Float.ofInt (loadMaxX10 * gRaw * 65536 - 10 * loadNum s) / (10 * Float.ofInt gRaw * 65536) / 0.5
  let v := (Float.sqrt (F s.vx.raw ^ 2 + F s.vz.raw ^ 2) - F vFloor) / 2
  let h := Min.min (F (s.h.raw - clearance)) (F (hMax - s.h.raw)) / 2
  let st := if s.stall.raw != 0 then -1.0 else 1.0
  ⟨Min.min a st, n, v, h⟩

def Margins.meet (x y : Margins) : Margins :=
  ⟨Min.min x.a y.a, Min.min x.n y.n, Min.min x.v y.v, Min.min x.h y.h⟩

/-- Fly `k` ticks; the first unsafe substep (as in `testT`) and the worst margins seen. -/
def shortTest (L : Law) (p : State × L.σ) (k : Nat) : Option String × Margins := Id.run do
  let mut s := p.1
  let mut m := p.2
  let mut mg : Margins := ⟨1e9, 1e9, 1e9, 1e9⟩
  for t in [0:k] do
    let r := L.step m s
    let u := clampInput r.1
    for _ in [0:8] do
      s := sub u s
      mg := mg.meet (stateMargins s)
      if !safeOk s then return (some s!"{classify s}@tick{t}", mg)
    m := r.2
  return (none, mg)

/-- Bisection along `dir` (scaled by `scale`) from an in-T vector to the last in-T point before `tMax`. -/
def boundary (L : Law) (base : Array Int) (dir : Array Float) (scale : Array Int) (tMax : Float) (iters : Nat) :
    Option (State × L.σ) := Id.run do
  let at_ (tt : Float) : Option (State × L.σ) :=
    (unvec L ((List.range base.size).toArray.map fun (j : Nat) =>
      (base[j]! + (tt * dir[j]! * Float.ofInt scale[j]!).round.toInt64.toInt : Int))).filter L.inT
  if (at_ tMax).isSome then return at_ tMax
  let mut a := 0.0
  let mut b := tMax
  for _ in [0:iters] do
    let mid := (a + b) / 2
    if (at_ mid).isSome then a := mid else b := mid
  return at_ a

/-- Lowest height at which `v` (otherwise unchanged) is still in T, by bisection; `none` if `v` is not in T. -/
def lowestH (L : Law) (v : Array Int) : Option (State × L.σ) := Id.run do
  let atH (h : Int) : Option (State × L.σ) := (unvec L (v.set! 1 h)).filter L.inT
  if (atH v[1]!).isNone then return none
  if (atH clearance).isSome then return atH clearance
  let mut a : Int := clearance
  let mut b : Int := v[1]!
  for _ in [0:32] do
    if b - a ≤ 1 then break
    let mid := (a + b) / 2
    if (atH mid).isSome then b := mid else a := mid
  return atH b

structure FalsRes where
  screened : Nat
  full : Nat
  hill : Nat
  ces : Array CE
  worst : Margins

/-- Structural falsifier for one law. Generators, cycled: perturbation (modes 0), boundary bisection along a random
direction, coordinate extremes (one axis to the boundary, both signs), the same at the lowest height in T (the
first-substep dip of h-dependent sets), altitude jumps (same state at another height, acceleration fields
unchanged), and one-tick images. Then hill-climbing on the boundary of T from the candidates closest to each
envelope limit. Deterministic: splitmix64 from `seed`. -/
def falsify (L : Law) (seeds : Array (State × L.σ)) (nScreen nHill hillSteps : Nat) (seed : UInt64) : FalsRes :=
  Id.run do
  if seeds.isEmpty then return ⟨0, 0, 0, #[], ⟨1e9, 1e9, 1e9, 1e9⟩⟩
  let shortK : Nat := 64
  let vs := seeds.map (vecOf L)
  let d := vs[0]!.size
  let idx : Array Nat := (List.range d).toArray
  let lo : Array Int := idx.map fun j => vs.foldl (fun a v => min a v[j]!) (vs[0]![j]!)
  let hi : Array Int := idx.map fun j => vs.foldl (fun a v => max a v[j]!) (vs[0]![j]!)
  let scale : Array Int := idx.map fun j =>
    if j < 19 then (if minScale[j]! == 0 then (0 : Int) else max minScale[j]! ((hi[j]! - lo[j]!) / 2))
    else max (655 : Int) ((hi[j]! - lo[j]!) / 2)
  let free : Array Nat := idx.filter fun j => scale[j]! != 0
  let hTop : Int := hi[1]! + (hi[1]! - lo[1]!) / 2
  let mut r : Ci.Rng := ⟨seed⟩
  let mut ces : Array CE := #[]
  let mut screened := 0
  let mut full := 0
  let mut worst : Margins := ⟨1e9, 1e9, 1e9, 1e9⟩
  -- best (smallest) margin per limit, kept as (margin, vector) for hill-climbing
  let mut tops : Array (Array (Float × Array Int)) := #[#[], #[], #[], #[]]
  let keep := Max.max 1 nHill
  for t in [0:nScreen + seeds.size] do
    let mut cand : Option (State × L.σ) := none
    let (x, r1) := r.next; r := r1
    -- every seed once at its lowest height in T, then the cycled generators
    let base := if t < seeds.size then vs[t]! else vs[(x % vs.size.toUInt64).toNat]!
    let g := if t < seeds.size then 99 else (t - seeds.size) % 6
    if g == 99 then
      cand := lowestH L base
    else if g == 0 then
      let mut tries := 0
      while cand.isNone && tries < 20 do
        tries := tries + 1
        let (amp, r2) := r.pick #[0.02, 0.05, 0.2, 0.5, 1.0]; r := r2
        let mut v := base
        for j in free do
          let (u, r3) := r.unif (-1) 1; r := r3
          v := v.set! j (v[j]! + (amp * u * Float.ofInt scale[j]!).round.toInt64.toInt)
        cand := (unvec L v).filter L.inT
    else if g == 1 then
      let mut dir : Array Float := Array.replicate d 0
      for j in free do
        let (u, r3) := r.unif (-1) 1; r := r3
        dir := dir.set! j u
      cand := boundary L base dir scale 4.0 20
    else if g == 2 || g == 3 then
      let (k, r2) := r.next; r := r2
      let j := free[(k % free.size.toUInt64).toNat]!
      let (sgn, r3) := r.pick #[-1.0, 1.0]; r := r3
      let b0 := if g == 3 then ((lowestH L base).map (vecOf L)).getD base else base
      let dir := (Array.replicate d 0.0).set! j sgn
      let c := boundary L b0 dir scale 8.0 24
      cand := if g == 3 then (c.bind fun p => lowestH L (vecOf L p)) else c
    else if g == 4 then
      let (u, r2) := r.unif 0 1; r := r2
      let h := clearance + (u * Float.ofInt (hTop - clearance)).round.toInt64.toInt
      cand := (unvec L (base.set! 1 h)).filter L.inT
    else
      let mut v := base
      for j in free do
        let (u, r3) := r.unif (-1) 1; r := r3
        v := v.set! j (v[j]! + (u * Float.ofInt scale[j]!).round.toInt64.toInt)
      if let some p := unvec L v then
        let mut q := p
        for _ in [0:8] do
          if cand.isNone then
            let rr := tickT L q.1 q.2
            q := (rr.s, rr.m)
            if L.inT q then cand := some q
    if let some p := cand then
      screened := screened + 1
      let (fail, mg) := shortTest L p shortK
      worst := worst.meet mg
      if let some why := fail then
        ces := ces.push ⟨s!"fals{g}", why, vecOf L p⟩
      else
        if screened % 16 == 0 then
          full := full + 1
          if let some why := testT L p 640 then ces := ces.push ⟨s!"fals{g}-full", why, vecOf L p⟩
        for k in [0:4] do
          let m := mg.get k
          let row := tops[k]!
          if row.size < keep || m < (row.back?.map (·.1)).getD 1e9 then
            let row := (row.push (m, vecOf L p)).qsort (fun a b => a.1 < b.1)
            tops := tops.set! k (if row.size > keep then row.pop else row)
  -- hill-climbing: shrink each limit's margin by small moves that stay in T (pulled back onto the boundary)
  let mut hill := 0
  for k in [0:4] do
    for (m0, v0) in tops[k]! do
      let mut cur := v0
      let mut curM := m0
      let mut step := 0.05
      for _ in [0:hillSteps] do
        let mut dir : Array Float := Array.replicate d 0
        for j in free do
          let (u, r3) := r.unif (-1) 1; r := r3
          dir := dir.set! j u
        let mv := (List.range d).toArray.map fun (j : Nat) =>
          (cur[j]! + (step * dir[j]! * Float.ofInt scale[j]!).round.toInt64.toInt : Int)
        let next : Option (State × L.σ) := match (unvec L mv).filter L.inT with
          | some p => some p
          | none => boundary L cur (dir.map (· * step)) scale 1.0 12
        if let some p := next then
          hill := hill + 1
          let (fail, mg) := shortTest L p shortK
          worst := worst.meet mg
          if let some why := fail then
            ces := ces.push ⟨s!"hill{k}", why, vecOf L p⟩
            break
          if mg.get k < curM then cur := vecOf L p; curM := mg.get k; step := Min.min 0.2 (step * 1.5)
          else step := Max.max 0.005 (step * 0.7)
  return ⟨screened, full, hill, ces, worst⟩

structure Audit where
  rows : List (String × String × Bool × String × Int)
  provedLaws : List Nat

def audit (nLaws : Nat) (ext : List String := []) : Audit :=
  let rows := (Ci.Report.auditRows ++ ext).map fun l =>
    match l.splitOn "|" with
    | [n, a, s, k, i] => (n, a, s == "true", k, (i.toInt?).getD (-1))
    | _ => (l, "", false, "other", -1)
  let proved := (List.range nLaws).filter fun i =>
    rows.any fun (_, _, std, k, li) => std && li == i && (k == "Ci.Goals.TSafe" || k == "Ci.Goals.TInvariant")
  ⟨rows, proved⟩

def jsonStr (s : String) : String := "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

end Ci.Score

open Ci.Score in
def traceMain (i n : Nat) : IO UInt32 := do
  let lines := (← IO.FS.lines benchPath).toList.drop 1
  let some e := (lines.filterMap Entry.parse)[i]? | return 2
  let some L := Ci.Agent.submission.laws.head? | return 2
  let mut s := e.c.s
  let mut m := L.init e.c
  IO.println s!"{e.family} {e.params}"
  for k in [0:n + 1] do
    if k % 32 == 0 || L.inT (s, m) then
      IO.println s!"k {k} inT {L.inT (s, m)} h {F s.h.raw} vx {s.vx.raw} vz {s.vz.raw} dz {s.dz.raw} q {s.q.raw} m {L.enc m} rpm {F s.rpm.raw} dah {s.ah.raw - s.ah1.raw} dau {s.au.raw - s.au1.raw} dvz {s.vz.raw - s.pvz.raw} dpvz {s.pvz.raw - s.pvz2.raw}"
      if L.inT (s, m) then break
    let r := tickT L s m
    s := r.s; m := r.m
  return 0

open Ci.Score in
/-- `--verify-ce FILE [N]`: re-test up to N counterexample rows (law name, kind, why, raw vector) with the full
T test, independently of how they were found, and print the per-tick trace around the failure. -/
def verifyMain (path : String) (n : Nat) : IO UInt32 := do
  let rows := ((← IO.FS.lines path).toList.drop 1).filter (· ≠ "")
  let mut bad := 0
  let mut k := 0
  for row in rows.take n do
    let parts := row.splitOn ","
    let some L := Ci.Agent.submission.laws.find? (·.name == parts[0]!) | IO.println s!"no law {parts[0]!}"; continue
    let vec := ((parts.getLast!).splitOn " ").filterMap String.toInt? |>.toArray
    let some p := unvec L vec | IO.println "undecodable"; bad := bad + 1; continue
    let r := testT L p 640
    IO.println s!"row {k} {parts[1]!} claimed {parts[2]!}: inT {L.inT p} full-test {r.getD "PASS"}"
    if !L.inT p || r.isNone then bad := bad + 1
    k := k + 1
  IO.println s!"verified {k - bad}/{k}"
  return if bad == 0 then 0 else 1

open Ci.Score in
/-- Worst box-baseline loss (raw, -1 if any throttle is rejected) per typical-grid (V, γ) node, as a Lean literal. -/
def fitMain : IO UInt32 := do
  let lines := (← IO.FS.lines benchPath).toList.drop 1
  let es := (lines.filterMap Entry.parse).filter (·.family == "typical")
  let mut tbl : Array Int := Array.replicate 88 (-2)
  for e in es do
    let ps := (e.params.splitOn ";").map fun kv => ((kv.splitOn "=")[1]?.getD "0")
    let V := Ci.Gen.parseF' ps[0]!; let g := Ci.Gen.parseF' ps[1]!
    let iv := ((V - 30) / 3).round.toUInt64.toNat
    let ig := ((g + 0.5) / 0.1).round.toUInt64.toNat
    let k := iv * 8 + ig
    let v := match (check Ci.Baseline.box e.c).1 with
      | some (_, r) => e.c.s.h.raw - r.hMin
      | none => -1
    let old := tbl[k]!
    tbl := tbl.set! k (if old == -1 || v == -1 then -1 else max old v)
  IO.println s!"#[{", ".intercalate (tbl.toList.map toString)}]"
  return 0

open Ci.Score in
def main (args : List String) : IO UInt32 := do
  if args == ["--fit"] then return ← fitMain
  if let ["--trace", i, n] := args then return ← traceMain i.toNat! n.toNat!
  if let ["--verify-ce", f, n] := args then return ← verifyMain f n.toNat!
  let rec optSub : List String → String
    | "--sub" :: n :: _ => n
    | _ :: rest => optSub rest
    | [] => "agent"
  let subName := optSub args
  let rec optSeed : List String → UInt64
    | "--seed" :: n :: _ => (n.toNat?.getD 0xC172).toUInt64
    | _ :: rest => optSeed rest
    | [] => 0xC172
  let advSeed := optSeed args
  let rec optExt : List String → Option String
    | "--external-proofs" :: p :: _ => some p
    | _ :: rest => optExt rest
    | [] => none
  let ext ← match optExt args with
    | some p => do pure ((← IO.FS.lines p).toList.filter (· ≠ ""))
    | none => pure []
  let quick := args.contains "--quick"
  let outDir : System.FilePath := "ci-out" / subName
  IO.FS.createDirAll outDir
  let (S, staticBad) : Submission × List String := match subName with
    | "box" => (Ci.Baseline.box, Ci.Report.staticBox)
    | "interior" => (Ci.Baseline.interior, Ci.Report.staticInterior)
    | _ => (Ci.Agent.submission, Ci.Report.staticAgent)
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile benchPath
  let hash := fnv1a bytes
  let hashOk := hash == benchHash
  let lines := (String.fromUTF8! bytes).splitOn "\n" |>.drop 1 |>.filter (· ≠ "")
  let es := (lines.filterMap Entry.parse).toArray
  let es := if quick then es.extract 0 0 ++ (List.range (es.size / 10)).toArray.map (es[10 * ·]!) else es
  let res ← runBench S es
  let tBench ← IO.monoMsNow
  let acc := res.filter (·.accepted)
  let nEnt := FN es.size
  let coverage := FN acc.size / max 1 nEnt
  let losses := acc.map (·.loss)
  let hst := acc.map fun r => r.hstar.getD (F r.e.c.s.h.raw)
  let gen (r : StateRes) : Float :=
    if !r.accepted then 0 else 10 / (10 + max 0 ((r.hstar.getD (F r.e.c.s.h.raw)) - F clearance))
  -- Measured at h*, not the stored ~1000 m altitude, where a T like "h ≥ 900 m" would be reached at once.
  let shortR (r : StateRes) : Float :=
    if r.accepted then 16 / (16 + FN (if r.hstar.isSome then r.ticksH else r.ticks)) else 0
  let Q := mean (res.map gen)
  let R := mean (res.map shortR)
  let ticksHi := acc.map (FN ·.ticks)
  let ticksLo := acc.map (FN ·.ticksH)
  let spent := res.map (FN ·.spent)
  let usAll := res.map (·.us)
  let usTick := (usAll.foldl (· + ·) 0) / max 1 (spent.foldl (· + ·) 0)
  let worstTicks := S.horizon * S.laws.length
  let B := min 1 (FN budgetTicks / max 1 (FN worstTicks))
  let mut ces : Array (String × CE) := #[]
  let mut advLines : Array String := #[]
  let mut li := 0
  for L in S.laws do
    let mut seeds : Array (State × L.σ) := #[]
    for r in acc do
      if r.law == li then
        if let some p := rollToT L r.e.c S.horizon then seeds := seeds.push p
        if let some h := r.hstar then
          if let some p := rollToT L (r.e.c.atHeight (h * 65536).round.toInt64.toInt) S.horizon then
            seeds := seeds.push p
    -- Official runs attack with eight seeds: competitors found counterexamples that four seeds missed.
    let advSeeds : List UInt64 := if quick then [advSeed] else [advSeed, 3, 5, 7, 11, 13, 17, 19]
    for sd in advSeeds do
      let a := adversary L seeds (if quick then 200 else 2000) (if quick then 8 else 64) (sd + li.toUInt64)
      advLines := advLines.push s!"\{\"law\":{jsonStr L.name},\"adv_seed\":{sd},\"seeds\":{seeds.size},\"tests\":{a.tests},\"long_tests\":{a.longTests},\"counterexamples\":{a.ces.size}}"
      ces := ces ++ a.ces.map (L.name, ·)
    -- Structural falsifier: many short screened tests, coordinate extremes, lowest-height and altitude-jump
    -- candidates, then hill-climbing toward each envelope limit (see `falsify`).
    let fr := falsify L seeds (if quick then 3000 else 30000) (if quick then 4 else 24) (if quick then 20 else 40)
      (0xF00D + li.toUInt64)
    advLines := advLines.push s!"\{\"law\":{jsonStr L.name},\"falsifier\":true,\"seeds\":{seeds.size},\"screened\":{fr.screened},\"full_tests\":{fr.full},\"hill_tests\":{fr.hill},\"worst_margin\":{fmt fr.worst.min},\"counterexamples\":{fr.ces.size}}"
    ces := ces ++ fr.ces.map (L.name, ·)
    li := li + 1
  let tAdv ← IO.monoMsNow
  let au := audit S.laws.length ext
  let provedAll := !S.laws.isEmpty && au.provedLaws.length == S.laws.length
  let valid := hashOk && staticBad.isEmpty && ces.isEmpty && !S.laws.isEmpty && S.horizon > 0
  let P : Float := if provedAll then 1 else 0
  -- P counts in proportion to coverage, so a proved but empty or useless T earns nothing.
  let headline : Float := if valid then 1 + P * coverage + 0.5 * Q + 0.4 * R + 0.1 * B else 0
  let ceText := "law,kind,why,vec\n" ++ "\n".intercalate (ces.toList.map fun (n, c) =>
    s!"{n},{c.kind},{c.why},{" ".intercalate (c.vec.toList.map toString)}")
  IO.FS.writeFile (outDir / "t-counterexamples.csv") (ceText ++ "\n")
  let stText := "family,id,accepted,law,loss_m,hstar_m,ticks_to_T,ticks_to_T_at_hstar,ticks_spent,us,why\n" ++
    "\n".intercalate (res.toList.map fun r =>
      s!"{r.e.family},{r.e.id},{r.accepted},{r.law},{fmt r.loss},{(r.hstar.map fmt).getD ""},{r.ticks},{r.ticksH},{r.spent},{fmt r.us},{r.why}")
  IO.FS.writeFile (outDir / "states.csv") (stText ++ "\n")
  let fams := #["typical", "push", "zoom", "fastdive", "slowidle", "elevtrans"]
  let famJson := ",".intercalate (fams.toList.map fun f =>
    let rs := res.filter (·.e.family == f)
    let a := rs.filter (·.accepted)
    s!"{jsonStr f}:\{\"n\":{rs.size},\"coverage\":{fmt (FN a.size / max 1 (FN rs.size))},\"median_hstar_m\":{fmt (median (a.map fun r => r.hstar.getD (F r.e.c.s.h.raw)))},\"median_ticks_to_T\":{fmt (median (a.map (FN ·.ticks)))}}")
  let auditJson := ",".intercalate (au.rows.map fun (n, a, s, k, i) =>
    s!"\{\"name\":{jsonStr n},\"axioms\":{jsonStr a},\"proved\":{s},\"goal\":{jsonStr k},\"law\":{i}}")
  let tEnd ← IO.monoMsNow
  let json := s!"\{\"submission\":{jsonStr S.name},\"valid\":{valid},\"headline\":{fmt headline}," ++
    s!"\"components\":\{\"proved_T\":{provedAll},\"Q_generosity\":{fmt Q},\"R_short_rollouts\":{fmt R},\"B_budget\":{fmt B}}," ++
    s!"\"bench\":\{\"entries\":{es.size},\"fnv1a\":\"{hash}\",\"hash_ok\":{hashOk},\"quick\":{quick},\"adversary_seed\":{advSeed}}," ++
    s!"\"coverage\":{fmt coverage},\"loss_to_T_m\":\{\"mean\":{fmt (mean losses)},\"median\":{fmt (median losses)},\"p90\":{fmt (pct losses 0.9)},\"max\":{fmt (maxF losses)}}," ++
    s!"\"hstar_m\":\{\"mean\":{fmt (mean hst)},\"median\":{fmt (median hst)},\"p90\":{fmt (pct hst 0.9)},\"max\":{fmt (maxF hst)}}," ++
    s!"\"rollout_ticks_to_T\":\{\"stored_alt_median\":{fmt (median ticksHi)},\"stored_alt_max\":{fmt (maxF ticksHi)},\"at_hstar_median\":{fmt (median ticksLo)},\"at_hstar_max\":{fmt (maxF ticksLo)}}," ++
    s!"\"realtime\":\{\"horizon\":{S.horizon},\"laws\":{S.laws.length},\"worst_case_ticks_per_check\":{worstTicks},\"budget_ticks\":{budgetTicks},\"ticks_spent_median\":{fmt (median spent)},\"ticks_spent_max\":{fmt (maxF spent)},\"us_per_tick\":{fmt usTick},\"check_us_median\":{fmt (median usAll)},\"check_us_max\":{fmt (maxF usAll)},\"worst_case_check_ms_est\":{fmt (FN worstTicks * usTick / 1000)},\"tick_ms\":62.5}," ++
    s!"\"families\":\{{famJson}}," ++
    s!"\"T_adversary\":[{",".intercalate advLines.toList}],\"T_counterexamples\":{ces.size}," ++
    s!"\"static_R4_violations\":[{",".intercalate (staticBad.map jsonStr)}]," ++
    s!"\"proofs\":[{auditJson}]," ++
    s!"\"runtime_s\":\{\"bench\":{fmt ((tBench - t0).toFloat / 1000)},\"adversary\":{fmt ((tAdv - tBench).toFloat / 1000)},\"total\":{fmt ((tEnd - t0).toFloat / 1000)}}}"
  IO.FS.writeFile (outDir / "score.json") (json ++ "\n")
  IO.println s!"== ciscore: {S.name} ({es.size} benchmark states{if quick then ", QUICK (not official)" else ""}) =="
  IO.println s!"VALID: {valid}   HEADLINE: {fmt headline}"
  IO.println s!"  proved T: {provedAll}   Q (coverage x generosity): {fmt Q}   R (short rollouts): {fmt R}   B (budget): {fmt B}"
  IO.println s!"  coverage {fmt coverage}; loss until T median {fmt (median losses)} m, mean {fmt (mean losses)} m; h* median {fmt (median hst)} m, p90 {fmt (pct hst 0.9)} m"
  IO.println s!"  rollout ticks to T: median {fmt (median ticksHi)}, max {fmt (maxF ticksHi)} (stored alt); at h*: median {fmt (median ticksLo)}, max {fmt (maxF ticksLo)}"
  IO.println s!"  real time: worst case {worstTicks} ticks/check (budget {budgetTicks}); {fmt usTick} us/tick; check median {fmt (median usAll)} us, max {fmt (maxF usAll)} us; est. worst {fmt (FN worstTicks * usTick / 1000)} ms of 62.5"
  for f in fams do
    let rs := res.filter (·.e.family == f)
    let a := rs.filter (·.accepted)
    IO.println s!"  {f}: {a.size}/{rs.size} accepted, median h* {fmt (median (a.map fun r => r.hstar.getD (F r.e.c.s.h.raw)))} m"
  IO.println s!"  T adversary: {", ".intercalate advLines.toList}"
  IO.println s!"  bench hash ok: {hashOk} ({hash}); static R4 violations: {staticBad}; proofs: {au.rows.length} claimed, laws proved {au.provedLaws}"
  IO.println s!"  runtime {fmt ((tEnd - t0).toFloat / 1000)} s; files in {outDir}"
  IO.println json
  return if valid then 0 else 1
