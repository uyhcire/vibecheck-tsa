import Tools.DumpRun
import CityJsb.Plant

/-! `cityimporttest RUN...`: every record of each harness run, imported with `CityJsb.fromDump` and stepped
once with its recorded inputs, must equal the next record bit for bit, and `obsFromDump` of the next record
must equal the plant's observation after that step, as must every field `toDump` fills; exits non-zero
otherwise. -/

open JsbExact CityJsb DumpRun

def checkRun (pfx : String) : IO Bool := do
  let r ← load pfx
  let layout := r.names.extract (r.names.size - dumpNames.size) r.names.size
  if layout != dumpNames then
    IO.println s!"{pfx}: dump layout differs from CityJsb.dumpNames"
    return false
  let mut steps := 0
  let mut exact := 0
  let mut bad : Std.HashMap String Nat := {}
  for k in [0:r.records] do
    if !r.continues k then continue
    let some dump := r.dump k | return false
    let some s := fromDump dump | return false
    let (s', d) := step s (r.input k)
    let mut ok := true
    let some next := r.dump (k + 1) | return false
    let some o := obsFromDump next | return false
    if (o.toList.zip (CityJsb.obs s' d).toList).any fun (a, b) => a.toBits != b.toBits then
      ok := false
      bad := bad.insert "obsFromDump" (bad.getD "obsFromDump" 0 + 1)
    if (next.toList.zip (toDump s' d).toList).any fun (a, b) => !b.isNaN && a.toBits != b.toBits then
      ok := false
      bad := bad.insert "toDump" (bad.getD "toDump" 0 + 1)
    for (n, x) in DumpRun.fields s' d do
      if x.toBits != (r.get (k + 1) n).toBits then
        ok := false
        bad := bad.insert n (bad.getD n 0 + 1)
    steps := steps + 1
    if ok then exact := exact + 1
  IO.println s!"{pfx}: {exact}/{steps} imported steps bit-exact in every compared field"
  for (n, c) in bad.toList do IO.println s!"  {n}: {c} mismatches"
  return exact == steps && steps > 0

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "usage: cityimporttest RUN... (harness dumps, e.g. ext/data/bank)"
    return 2
  let mut ok := true
  for pfx in args do
    ok := (← checkRun pfx) && ok
  return if ok then 0 else 1
