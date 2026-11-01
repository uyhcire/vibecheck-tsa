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

/-- Lowest commit height on a 0.25 m grid, from 1 m below `clearance + loss`, at which the filter accepts. -/
def hstar (S : Submission) (c : Commit) (loss : Int) : Option (Int × Nat × Nat) := Id.run do
  let q : Int := 16384
  let start := ((clearance + loss + q - 1) / q) * q - 4 * q
  for j in [0:48] do
    let hc := start + j * q
    if let (some (_, r), t) := check S (c.atHeight hc) then return some (hc, r.ticks, t)
  for j in [0:8] do
    let hc := start + 48 * q * 2 ^ j
    if hc ≥ c.s.h.raw then break
    if let (some (_, r), t) := check S (c.atHeight hc) then return some (hc, r.ticks, t)
  return none

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

structure Audit where
  rows : List (String × String × Bool × String × Int)
  provedLaws : List Nat

def audit (nLaws : Nat) : Audit :=
  let rows := Ci.Report.auditRows.map fun l =>
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
    let a := adversary L seeds (if quick then 200 else 2000) (if quick then 8 else 64) (advSeed + li.toUInt64)
    advLines := advLines.push s!"\{\"law\":{jsonStr L.name},\"seeds\":{seeds.size},\"tests\":{a.tests},\"long_tests\":{a.longTests},\"counterexamples\":{a.ces.size}}"
    ces := ces ++ a.ces.map (L.name, ·)
    li := li + 1
  let tAdv ← IO.monoMsNow
  let au := audit S.laws.length
  let provedAll := !S.laws.isEmpty && au.provedLaws.length == S.laws.length
  let valid := hashOk && staticBad.isEmpty && ces.isEmpty && !S.laws.isEmpty && S.horizon > 0
  let P : Float := if provedAll then 1 else 0
  let headline : Float := if valid then 1 + P + 0.5 * Q + 0.4 * R + 0.1 * B else 0
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
