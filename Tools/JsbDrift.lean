import Tools.DumpRun

/-! `jsbdrift RUN [--horizon N]`: drift check of `JsbExact` against a JSBSim dump log (`jsbx::DriftLog`).
Imports each episode's state with `CityJsb.fromDump`, steps it with the logged inputs alongside the log
(re-importing every `N` frames, default never), and reports per field how far the two drift apart. -/

open JsbExact CityJsb DumpRun

structure Stat where
  exact : Nat := 0
  total : Nat := 0
  maxAbs : Float := 0.0
  maxRel : Float := 0.0
  first : Option (Nat × Nat) := none

def fmt (x : Float) : String :=
  if x == 0.0 then "0" else
  let e := (Float.log10 (Float.abs x)).floor
  s!"{((x / Float.pow 10.0 e) * 100.0).round / 100.0}e{e.toInt64}"

def main (args : List String) : IO UInt32 := do
  let some pfx := args.head? | do
    IO.println "usage: jsbdrift RUN [--horizon FRAMES]   (RUN.names + RUN.bin from jsbx::DriftLog or the harness)"
    return 2
  let horizon := match args.idxOf? "--horizon" with
    | some i => (args.getD (i + 1) "0").toNat!
    | none => 0
  let r ← load pfx
  for n in dumpNames do
    if !r.index.contains n then
      IO.println s!"{pfx}: field {n} missing from the log"
      return 2
  let mut stats : Std.HashMap String Stat := {}
  let mut cur : Option (State Float) := none
  let mut since := 0
  let mut steps := 0
  let mut exactSteps := 0
  let mut order : Array String := #[]
  for k in [0:r.records] do
    if !r.continues k then
      cur := none
      continue
    if cur.isNone || (horizon > 0 && since ≥ horizon) then
      let some dump := r.dump k | return 2
      cur := fromDump dump
      since := 0
    let some s := cur | return 2
    let (s', d) := step s (r.input k)
    cur := some s'
    since := since + 1
    steps := steps + 1
    let fs := DumpRun.fields s' d
    if order.isEmpty then order := (fs.map (·.1)).toArray
    let mut all := true
    for (n, x) in fs do
      let ref := r.get (k + 1) n
      let st := stats.getD n {}
      let same := x.toBits == ref.toBits
      if !same then all := false
      let diff := Float.abs (x - ref)
      let rel := if ref == 0.0 then diff else diff / Float.abs ref
      stats := stats.insert n { st with
        exact := st.exact + (if same then 1 else 0), total := st.total + 1,
        maxAbs := max st.maxAbs diff, maxRel := max st.maxRel rel,
        first := if st.first.isNone && !same then some (k, since) else st.first }
    if all then exactSteps := exactSteps + 1
  let hz := if horizon > 0 then s!"re-imported every {horizon} frames" else "each episode from its first record"
  IO.println s!"{pfx}: {exactSteps}/{steps} frames bit-exact in every field ({hz})"
  IO.println "field            bit-exact        max |diff|  max rel     first differing record (frames since import)"
  for n in order do
    let st := stats.getD n {}
    let first := match st.first with
      | some (k, f) => s!"{k} ({f})"
      | none => "-"
    IO.println s!"{n.pushn ' ' (16 - n.length)} {st.exact}/{st.total}  {fmt st.maxAbs}  {fmt st.maxRel}  {first}"
  return if exactSteps == steps then 0 else 1
