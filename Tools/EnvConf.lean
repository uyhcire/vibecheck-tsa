import Jsb.Escape
import Jsb.Enc
import Jsb.Interval
open Vibecheck Jsb

/-! `envconf`: numerics for docs/ansatz/envelope.md (escape law flown in `Fx` from `Float` trims). -/

namespace Jsb.EnvConf

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

def g0 : Float := 9.80665

def mkF (h V gam th q rpm tmap : Float) : StateOf Float :=
  { x := 0, h, vx := V * Float.cos gam, vz := V * Float.sin gam, dx := Float.cos th, dz := Float.sin th, q,
    rpm, tmap, udot := 0, wdot := 0, stall := 0, ah := 0, au := 0, qd := 0, ah1 := 0, au1 := 0,
    pvz := V * Float.sin gam, pvz2 := V * Float.sin gam }

def inpF (e thr : Float) : InputOf Float := ⟨e, thr, 0, 0⟩

def settle (s : StateOf Float) (u : InputOf Float) (n : Nat) : StateOf Float := Id.run do
  let mut st := s
  for _ in [0:n] do
    let e := (evaluate 7 u st).1
    st := { st with rpm := e.rpm, tmap := e.tmap }
  return st

def resid (s : StateOf Float) (u : InputOf Float) : Float × Float :=
  let e := (evaluate 7 u s).1
  let V := Float.sqrt (s.vx * s.vx + s.vz * s.vz)
  let an := (s.vx * e.au - s.vz * e.ah) / V
  (an, e.qd)

def trim (h V gam thr : Float) : StateOf Float × Float := Id.run do
  let mut al := 0.08
  let mut el := 0.0
  let mut rpm := if thr > 0.5 then 2400.0 else 900.0
  let mut tmap := 60.0
  let mut cap := 1.0
  for _ in [0:60] do
    cap := cap * 0.9
    let s0 := settle (mkF h V gam (gam + al) 0 rpm tmap) (inpF el thr) 800
    rpm := s0.rpm; tmap := s0.tmap
    let f (a e : Float) := resid (mkF h V gam (gam + a) 0 rpm tmap) (inpF e thr)
    let r := f al el
    let d := 1e-4
    let ra := f (al + d) el
    let re := f al (el + d)
    let j11 := (ra.1 - r.1) / d; let j12 := (re.1 - r.1) / d
    let j21 := (ra.2 - r.2) / d; let j22 := (re.2 - r.2) / d
    let det := j11 * j22 - j12 * j21
    let da := (r.1 * j22 - r.2 * j12) / det
    let de := (j11 * r.2 - j21 * r.1) / det
    al := al - max (-0.02 * cap) (min (0.02 * cap) da); el := el - max (-0.05 * cap) (min (0.05 * cap) de)
  let s := settle (mkF h V gam (gam + al) 0 rpm tmap) (inpF el thr) 3000
  return (s, el)

def toFx (s : StateOf Float) : StateOf Fx := s.map fun x => ⟨rawF x⟩
def fl (x : Fx) : Float := x.toFloat

def consistent (s : StateOf Float) (u : Input) : State :=
  let f0 := toFx s
  let e1 := (evaluate 7 u f0).1
  let e2 := (evaluate 7 u { f0 with udot := e1.udot, wdot := e1.wdot }).1
  { f0 with udot := e2.udot, wdot := e2.wdot, ah := e2.ah, au := e2.au, qd := e2.qd, ah1 := e2.ah, au1 := e2.au,
            rpm := e2.rpm, tmap := e2.tmap }

structure Row where
  h : Float
  vx : Float
  vz : Float
  V : Float
  gam : Float
  th : Float
  al : Float
  q : Float
  rpm : Float
  au : Float
  ah : Float
  n : Float
  /-- along-path acceleration (m/s²) -/
  aT : Float
  E : Float

def row (s : State) : Row :=
  let vx := fl s.vx; let vz := fl s.vz
  let V := Float.sqrt (vx * vx + vz * vz)
  let gam := Float.atan2 vz vx
  let th := Float.atan2 (fl s.dz) (fl s.dx)
  let au := fl s.au; let ah := fl s.ah
  let an := (vx * au - vz * ah) / V
  let aT := (vx * ah + vz * au) / V
  { h := fl s.h, vx, vz, V, gam, th, al := th - gam, q := fl s.q, rpm := fl s.rpm, au, ah,
    n := (an + g0 * Float.cos gam) / g0, aT, E := fl s.h + V * V / (2 * g0) }

def hdr : String := "k,h,vx,vz,V,gam,th,al,q,elev,rpm,au,ah,n,at,E,almax,Vmin,hmin"

def csvRow (k : Nat) (c : CLOf Fx) (almax Vmin hmin : Float) : String :=
  let r := row c.s
  s!"{k},{r.h},{r.vx},{r.vz},{r.V},{r.gam},{r.th},{r.al},{r.q},{fl c.elev},{r.rpm},{r.au},{r.ah},{r.n},{r.aT},{r.E},{almax},{Vmin},{hmin}"

def tickObs (c : CLOf Fx) : CLOf Fx × Float × Float × Float := Id.run do
  let u := Escape.input c
  let mut s := c.s
  let mut am := -1e9
  let mut vm := 1e9
  let mut hm := 1e9
  for _ in [0:8] do
    s := step 7 true u s
    let r := row s
    am := max am r.al; vm := min vm r.V; hm := min hm r.h
  return (⟨s, Escape.command c⟩, am, vm, hm)

def fly (tag : String) (c0 : CLOf Fx) (n : Nat) : Array String := Id.run do
  let mut c := c0
  let r0 := row c.s
  let mut out := #[s!"{tag},{csvRow 0 c r0.al r0.V r0.h}"]
  for k in [0:n] do
    let (c', am, vm, hm) := tickObs c
    c := c'
    out := out.push s!"{tag},{csvRow (k + 1) c am vm hm}"
  return out

def commit (h V gam thr dal q0 : Float) : CLOf Fx :=
  let (s, el) := trim h V gam thr
  let th := gam + Float.atan2 s.dz s.dx - gam + dal
  let s' := { s with dx := Float.cos th, dz := Float.sin th, q := q0 }
  ⟨consistent s' ⟨⟨rawF el⟩, ⟨rawF thr⟩, 0, 0⟩, ⟨rawF el⟩⟩

def parseF (s : String) : Float :=
  let neg := s.startsWith "-"
  let t := if neg then (s.drop 1).toString else s
  let parts := t.splitOn "."
  let ip := (parts[0]!.toNat?).getD 0
  let fp := parts[1]?.getD ""
  let fv := if fp.isEmpty then 0.0 else (fp.toNat?.getD 0).toFloat / (10.0 ^ fp.length.toFloat)
  let v := ip.toFloat + fv
  if neg then -v else v


def hull (a b : Iv) : Iv := match a, b with
  | .box l h, .box l' h' => .box (min l l') (max h h')
  | _, _ => .top

def ivPt (x : Fx) : Iv := .box x.raw x.raw

def wdt : Iv → Float
  | .box a b => Float.ofInt (b - a) / S
  | .top => 1e30

def ivMid : Iv → Float
  | .box a b => Float.ofInt (a + b) / (2 * S)
  | .top => 0

def clHull (a : CLOf Iv) (c : CLOf Fx) : CLOf Iv :=
  ⟨{ x := hull a.s.x (ivPt c.s.x), h := hull a.s.h (ivPt c.s.h), vx := hull a.s.vx (ivPt c.s.vx),
     vz := hull a.s.vz (ivPt c.s.vz), dx := hull a.s.dx (ivPt c.s.dx), dz := hull a.s.dz (ivPt c.s.dz),
     q := hull a.s.q (ivPt c.s.q), rpm := hull a.s.rpm (ivPt c.s.rpm), tmap := hull a.s.tmap (ivPt c.s.tmap),
     udot := hull a.s.udot (ivPt c.s.udot), wdot := hull a.s.wdot (ivPt c.s.wdot),
     stall := hull a.s.stall (ivPt c.s.stall), ah := hull a.s.ah (ivPt c.s.ah), au := hull a.s.au (ivPt c.s.au),
     qd := hull a.s.qd (ivPt c.s.qd), ah1 := hull a.s.ah1 (ivPt c.s.ah1), au1 := hull a.s.au1 (ivPt c.s.au1),
     pvz := hull a.s.pvz (ivPt c.s.pvz), pvz2 := hull a.s.pvz2 (ivPt c.s.pvz2) }, hull a.elev (ivPt c.elev)⟩

def clPt (c : CLOf Fx) : CLOf Iv := ⟨c.s.map ivPt, ivPt c.elev⟩

def reach (h V gam thr dV dg dal dq n : Float) : IO Unit := do
  let (s, el) := trim h V gam thr
  let mk (V' g' da q0 : Float) : CLOf Fx :=
    let s1 := { s with vx := V' * Float.cos g', vz := V' * Float.sin g', pvz := V' * Float.sin g',
                       pvz2 := V' * Float.sin g' }
    let th := Float.atan2 s.dz s.dx + (g' - gam) + da
    let s2 := { s1 with dx := Float.cos th, dz := Float.sin th, q := q0 }
    ⟨consistent s2 ⟨⟨rawF el⟩, ⟨rawF thr⟩, 0, 0⟩, ⟨rawF el⟩⟩
  let c0 := mk V gam 0 0
  let mut B := clPt c0
  let mut pts : Array (CLOf Fx) := #[]
  for a in [-1.0, 1.0] do
    for b in [-1.0, 1.0] do
      for c in [-1.0, 1.0] do
        for d in [-1.0, 1.0] do
          let p := mk (V + a * dV) (gam + b * dg) (c * dal) (d * dq)
          pts := pts.push p
          B := clHull B p
  for k in [0:n.toUInt64.toNat] do
    if k < 4 || k % 4 == 0 then
      let spread (f : CLOf Fx → Float) : Float :=
        let vs := pts.map f
        vs.foldl max (-1e30) - vs.foldl min 1e30
      IO.println s!"k {k}: w vz {wdt B.s.vz}/{spread (fl ·.s.vz)} vx {wdt B.s.vx}/{spread (fl ·.s.vx)} dz {wdt B.s.dz}/{spread (fl ·.s.dz)} q {wdt B.s.q}/{spread (fl ·.s.q)} elev {wdt B.elev}/{spread (fl ·.elev)} h {wdt B.s.h}/{spread (fl ·.s.h)} | mid vz {ivMid B.s.vz}"
    B := Escape.tick B
    pts := pts.map Escape.tick


def dzCF (vx : Float) : Float := 0.15 + 0.02 * (vx - 38)

def lawE (V gam al : Float) : Float :=
  max (-1) (min 1 (4 * (dzCF (V * Float.cos gam) - Float.sin (gam + al))))

/-- Fast equilibrium at frozen (V, gam): q = 0, elevator at the law's target, zero pitch acceleration. -/
def fastEq (h V gam thr rpm tmap : Float) : Float × Float × StateOf Float := Id.run do
  let f (al : Float) : Float := (resid (mkF h V gam (gam + al) 0 rpm tmap) (inpF (lawE V gam al) thr)).2
  let mut lo := -0.15
  let mut hi := 0.4
  for _ in [0:60] do
    let mid := (lo + hi) / 2
    if f mid > 0 then lo := mid else hi := mid
  let al := (lo + hi) / 2
  return (al, lawE V gam al, mkF h V gam (gam + al) 0 rpm tmap)

def qsRow (h V gam thr rpm tmap : Float) : String :=
  let (al, e, s) := fastEq h V gam thr rpm tmap
  let r := (evaluate 7 (inpF e thr) s).1
  let an := (s.vx * r.au - s.vz * r.ah) / V
  let aT := (s.vx * r.ah + s.vz * r.au) / V
  s!"{V},{gam},{thr},{rpm},{al},{e},{(an + g0 * Float.cos gam) / g0},{aT},{r.qd}"

end Jsb.EnvConf

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
