import Jsb.Escape
open Vibecheck Jsb

/-! `escapesim RAWDUMP N`: run the escape autopilot from logged states (first 19 raw ints of each line). -/

def parseState (l : String) : Option State :=
  let body := ((l.splitOn "]").head!.drop 1).toString
  let xs := (body.splitOn ", ").filterMap String.toInt?
  if xs.length < 19 then none else
  let f (i : Nat) : Fx := ⟨xs[i]!⟩
  some ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩

def fl (x : Fx) : Float := x.toFloat

def rawOf (c : CLOf Fx) : List Int := [c.s.x, c.s.h, c.s.vx, c.s.vz, c.s.dx, c.s.dz, c.s.q, c.s.rpm, c.s.tmap,
  c.s.udot, c.s.wdot, c.s.stall, c.s.ah, c.s.au, c.s.qd, c.s.ah1, c.s.au1, c.s.pvz, c.s.pvz2, c.elev].map (·.raw)

/-- `--cloud FILE`: from every logged state with vx in [28, 50], fly the escape law and write each visited
closed-loop state with k ≥ 16 as raw ints, followed by the next tick's vz and vx increments. -/
def cloud (lines : Array String) (n : Nat) (out : String) : IO Unit := do
  let starts := (lines.toList.filterMap parseState).filter fun s => 28 < fl s.vx && fl s.vx < 50
  let mut rows : Array String := #[]
  let mut i := 0
  for s0 in starts do
    i := i + 1
    if i % 7 != 0 then continue
    let mut c : CLOf Fx := ⟨s0, s0.dz⟩
    for k in [0:n] do
      let c' := Escape.tick c
      if k ≥ 16 then
        rows := rows.push s!"{",".intercalate ((rawOf c).map toString)},{c'.s.vz.raw - c.s.vz.raw},{c'.s.vx.raw - c.s.vx.raw}"
      c := c'
  IO.FS.writeFile out ("\n".intercalate rows.toList)
  IO.println s!"{rows.size} rows"

def main (args : List String) : IO Unit := do
  let lines ← IO.FS.lines args[0]!
  if args[2]? == some "--cloud" then
    cloud lines (args[1]!).toNat! args[3]!
    return
  let n := (args[1]!).toNat!
  let verbose := args.contains "-v"
  let starts := (lines.toList.filterMap parseState).filter fun s => 33 < fl s.vx && fl s.vx < 47
  let picked := (List.range 40).filterMap fun i => starts[i * (starts.length / 40)]?
  for s0 in picked do
    let mut c : CLOf Fx := ⟨s0, 0⟩
    let mut minDvz : Float := 1e9
    let mut minDvx : Float := 1e9
    let mut minV : Float := 1e9
    for k in [0:n] do
      let c' := Escape.tick c
      if k ≥ 32 then
        minDvz := min minDvz (fl c'.s.vz - fl c.s.vz)
        minDvx := min minDvx (fl c'.s.vx - fl c.s.vx)
      minV := min minV (fl c'.s.vx)
      if verbose && k % 8 == 0 then
        IO.println s!"  k {k} vx {fl c.s.vx} vz {fl c.s.vz} dz {fl c.s.dz} q {fl c.s.q} elev {fl c.elev} rpm {fl c.s.rpm} au {fl c.s.au}"
      c := c'
    IO.println s!"start vx {fl s0.vx} vz {fl s0.vz} dz {fl s0.dz} q {fl s0.q} | end vx {fl c.s.vx} vz {fl c.s.vz} dz {fl c.s.dz} elev {fl c.elev} | min dvz(k≥32) {minDvz} min dvx {minDvx} min vx {minV}"
