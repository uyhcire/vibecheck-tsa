import Tools.EnvConf
open Vibecheck Jsb

/-! `envconf` executable: command-line front end for `Tools.EnvConf`. -/

open Jsb.EnvConf in
def main (args : List String) : IO Unit := do
  match args with
  | ["trim", h, V, gam, thr] =>
    let (s, el) := trim (parseF h) (parseF V) (parseF gam) (parseF thr)
    let r := resid s (inpF el (parseF thr))
    IO.println s!"alpha {Float.atan2 s.dz s.dx - parseF gam} elev {el} rpm {s.rpm} tmap {s.tmap} resid {r.1} {r.2}"
  | "fly" :: out :: n :: rest =>
    let mut rows : Array String := #[s!"tag,{hdr}"]
    let mut xs := rest.map parseF
    let mut i := 0
    while xs.length ≥ 6 do
      let c := commit xs[0]! xs[1]! xs[2]! xs[3]! xs[4]! xs[5]!
      rows := rows ++ fly s!"{i}" c n.toNat!
      xs := xs.drop 6; i := i + 1
    IO.FS.writeFile out ("\n".intercalate rows.toList ++ "\n")
    IO.println s!"{i} runs -> {out}"
  | ["grid", out, n, spec, dals, qs] =>
    let lines ← IO.FS.lines spec
    let h ← IO.FS.Handle.mk out .write
    h.putStrLn s!"tag,{hdr}"
    let dl := (dals.splitOn ",").map parseF
    let ql := (qs.splitOn ",").map parseF
    let mut i := 0
    for l in lines do
      let xs := (l.splitOn " ").filter (· ≠ "") |>.map parseF
      if xs.length < 4 then continue
      let (s, el) := trim xs[0]! xs[1]! xs[2]! xs[3]!
      for dal in dl do
        for q0 in ql do
          let th := Float.atan2 s.dz s.dx + dal
          let s' := { s with dx := Float.cos th, dz := Float.sin th, q := q0 }
          let c : CLOf Fx := ⟨consistent s' ⟨⟨rawF el⟩, ⟨rawF xs[3]!⟩, 0, 0⟩, ⟨rawF el⟩⟩
          for r in fly s!"{i}" c n.toNat! do h.putStrLn r
          i := i + 1
    IO.println s!"{i} runs -> {out}"
  | ["reach", h, V, gam, thr, dV, dg, dal, dq, n] =>
    reach (parseF h) (parseF V) (parseF gam) (parseF thr) (parseF dV) (parseF dg) (parseF dal) (parseF dq) (parseF n)
  | ["qs", out] =>
    let full := settle (mkF 1000 40 0 0.1 0 2400 80) (inpF 0 1) 20000
    let idle := settle (mkF 1000 40 0 0.1 0 900 30) (inpF 0 0) 20000
    let mut rows := #["V,gam,thr,rpm,al,e,n,at,qd"]
    for (thr, st) in [(1.0, full), (0.0, idle)] do
      for i in [0:30] do
        for j in [0:21] do
          let V := 31 + 1.0 * i.toFloat
          let gam := -0.45 + 0.025 * j.toFloat
          let st' := settle (mkF 1000 V gam 0.1 0 st.rpm st.tmap) (inpF 0 thr) 3000
          rows := rows.push (qsRow 1000 V gam thr st'.rpm st'.tmap)
    IO.FS.writeFile out ("\n".intercalate rows.toList ++ "\n")
  | ["onetick", inp, out] =>
    let lines ← IO.FS.lines inp
    let h ← IO.FS.Handle.mk out .write
    h.putStrLn "i,n0,V1,gam1,al1,q1,e1,n1,rpm1,dvz,dV,almax"
    let mut i := 0
    for l in lines do
      let xs := (l.splitOn " ").filter (· ≠ "") |>.map parseF
      if xs.length < 9 then continue
      let V := xs[1]!; let gam := xs[2]!; let al := xs[3]!
      let s00 := mkF xs[0]! V gam (gam + al) xs[4]! xs[6]! xs[7]!
      let s0 := Id.run do
        let mut st := if xs[7]! == 0 then { s00 with tmap := 88 } else s00
        if xs[7]! == 0 then
          for _ in [0:400] do st := { st with tmap := (evaluate 7 (inpF xs[5]! xs[8]!) st).1.tmap }
        return st
      let c : CLOf Fx := ⟨consistent s0 ⟨⟨rawF xs[5]!⟩, ⟨rawF xs[8]!⟩, 0, 0⟩, ⟨rawF xs[5]!⟩⟩
      let r0 := row c.s
      let (c', am, _, _) := tickObs c
      let r1 := row c'.s
      h.putStrLn s!"{i},{r0.n},{r1.V},{r1.gam},{r1.al},{r1.q},{fl c'.elev},{r1.n},{r1.rpm},{r1.vz - r0.vz},{r1.V - r0.V},{am}"
      i := i + 1
  | _ => IO.println "usage: envconf trim h V gam thr | fly OUT N (h V gam thr dal q0)* | grid OUT N SPEC"
