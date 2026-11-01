import Ci.Bench
import Tools.EnvConf
open Vibecheck Jsb Jsb.EnvConf Ci

/-! `cigen`: deterministic generator of `Ci/data/bench.csv` (scoreboard-owned). -/

namespace Ci.Gen

def inp (e thr : Float) : Input := clampInput ⟨⟨rawF e⟩, ⟨rawF thr⟩, ⟨0⟩, ⟨0⟩⟩

def residFx (s : State) (u : Input) : Float × Float :=
  let e := (evaluate 7 u s).1
  let vx := fl s.vx; let vz := fl s.vz
  ((vx * fl e.au - vz * fl e.ah) / Float.sqrt (vx * vx + vz * vz), fl e.qd)

def settleFx (s : State) (u : Input) (n : Nat) : State := Id.run do
  let mut st := s
  for _ in [0:n] do
    let e := (evaluate 7 u st).1
    st := { st with rpm := e.rpm, tmap := e.tmap }
  return st

/-- `EnvConf.trim` evaluated on the `Fx` model (the `Float` instance is too slow for a full benchmark). -/
def trimFx (h V gam thr : Float) : State × Float := Id.run do
  let mk (al rpm tmap : Float) : State := toFx (mkF h V gam (gam + al) 0 rpm tmap)
  let mut al := 0.08
  let mut el := 0.0
  let mut rpm := if thr > 0.5 then 2400.0 else 900.0
  let mut tmap := 60.0
  let mut cap := 1.0
  for _ in [0:40] do
    cap := cap * 0.9
    let s0 := settleFx (mk al rpm tmap) (inp el thr) 200
    rpm := fl s0.rpm; tmap := fl s0.tmap
    let f (a e : Float) := residFx (mk a rpm tmap) (inp e thr)
    let r := f al el
    let d := 1e-3
    let ra := f (al + d) el
    let re := f al (el + d)
    let j11 := (ra.1 - r.1) / d; let j12 := (re.1 - r.1) / d
    let j21 := (ra.2 - r.2) / d; let j22 := (re.2 - r.2) / d
    let det := j11 * j22 - j12 * j21
    let da := (r.1 * j22 - r.2 * j12) / det
    let de := (j11 * r.2 - j21 * r.1) / det
    al := al - max (-0.02 * cap) (min (0.02 * cap) da); el := el - max (-0.05 * cap) (min (0.05 * cap) de)
  return (settleFx (mk al rpm tmap) (inp el thr) 800, el)

def trimCommit (h V gam thr : Float) : Option (Commit × Float) :=
  let (s, el) := trimFx h V gam thr
  let u := inp el thr
  let r := residFx s u
  if r.1.abs > 0.01 || r.2.abs > 0.01 then none else some (⟨consistent (s.map fl) u, u⟩, el)

def fly (c : Commit) (n : Nat) (pilot : Nat → State → Input) : Commit := Id.run do
  let mut c := c
  for k in [0:n] do
    let u := clampInput (pilot k c.s)
    c := ⟨tickAB u c.s, u⟩
  return c

def gamOf (s : State) : Float := Float.atan2 (fl s.vz) (fl s.vx)
def vOf (s : State) : Float := Float.sqrt (fl s.vx * fl s.vx + fl s.vz * fl s.vz)
def thOf (s : State) : Float := Float.atan2 (fl s.dz) (fl s.dx)

def holdTheta (e0 thr thT : Float) : Nat → State → Input :=
  fun _ s => inp (e0 + 3 * (thT - thOf s) - 0.6 * fl s.q) thr

def flyUntil (c : Commit) (nMax : Nat) (pilot : Nat → State → Input) (stop : State → Bool) : Option Commit :=
  Id.run do
    let mut c := c
    for k in [0:nMax] do
      if stop c.s then return some c
      let u := clampInput (pilot k c.s)
      c := ⟨tickAB u c.s, u⟩
    return none

def fmt (x : Float) : String := toString ((x * 1000).round / 1000)

def h0 : Float := 1000

def draw (fam : String) (r : Rng) : Option (String × Commit) × Rng := Id.run do
  let thrs := #[0.0, 0.6, 1.0]
  match fam with
  | "push" =>
    let (V, r) := r.unif 35 55; let (g, r) := r.unif (-0.2) 0.1; let (thr, r) := r.pick thrs
    let (d, r) := r.unif 0.2 0.8; let (ramp, r) := r.unif 1 4; let (n, r) := r.unif 3 16
    let some (c, e0) := trimCommit h0 V g thr | return (none, r)
    let c := fly c 16 fun _ _ => inp e0 thr
    let c := fly c n.toUInt64.toNat fun k _ => inp (e0 - d * min 1 ((k + 1).toFloat / ramp)) thr
    if fl c.s.q < 0 then (some (s!"V={fmt V};g={fmt g};thr={thr};d={fmt d};n={n.toUInt64}", c), r) else (none, r)
  | "zoom" =>
    let (V, r) := r.unif 48 60; let (g, r) := r.unif (-0.05) 0.1; let (thr, r) := r.pick #[0.6, 1.0]
    let (thT, r) := r.unif 0.3 0.55; let (vc, r) := r.unif 31 40
    let some (c, e0) := trimCommit h0 V g thr | return (none, r)
    let c := fly c 16 fun _ _ => inp e0 thr
    match flyUntil c 480 (holdTheta e0 0 thT) (fun s => vOf s ≤ vc) with
    | some c => if gamOf c.s > 0 then (some (s!"V={fmt V};g={fmt g};thr={thr};th={fmt thT};vc={fmt vc}", c), r)
                else (none, r)
    | none => (none, r)
  | "fastdive" =>
    let (V, r) := r.unif 45 58; let (g, r) := r.unif (-0.4) (-0.2); let (thr, r) := r.pick #[0.6, 1.0]
    let (dth, r) := r.unif 0 0.2; let (n, r) := r.unif 16 64
    let some (c, e0) := trimCommit h0 V g thr | return (none, r)
    let c := fly c 16 fun _ _ => inp e0 thr
    let c := fly c n.toUInt64.toNat (holdTheta e0 thr (thOf c.s - dth))
    if vOf c.s ≥ 52 && gamOf c.s ≤ -0.25 then
      (some (s!"V={fmt V};g={fmt g};thr={thr};dth={fmt dth};n={n.toUInt64}", c), r) else (none, r)
  | "slowidle" =>
    let (V, r) := r.unif 30 38; let (g, r) := r.unif (-0.1) 0.05
    let (vzT, r) := r.unif (-1.5) 0.5; let (vc, r) := r.unif 28 33
    let some (c, e0) := trimCommit h0 V g 0 | return (none, r)
    let c := fly c 16 fun _ _ => inp e0 0
    let pilot : Nat → State → Input := fun _ s =>
      inp (e0 + 0.15 * (vzT - fl s.vz) + 0.5 * (thOf c.s - thOf s) - 0.6 * fl s.q) 0
    match flyUntil c 320 pilot (fun s => vOf s ≤ vc) with
    | some c => if vOf c.s ≤ 34 && (gamOf c.s).abs ≤ 0.1 then
                  (some (s!"V={fmt V};g={fmt g};vzT={fmt vzT};vc={fmt vc}", c), r) else (none, r)
    | none => (none, r)
  | "elevtrans" =>
    let (V, r) := r.unif 33 58; let (g, r) := r.unif (-0.3) 0.1; let (thr, r) := r.pick thrs
    let (eT, r) := r.unif (-1) 1; let (n, r) := r.unif 1 4
    let some (c, e0) := trimCommit h0 V g thr | return (none, r)
    if (eT - e0).abs < 0.4 then return (none, r)
    let c := fly c 16 fun _ _ => inp e0 thr
    let c := fly c n.toUInt64.toNat fun _ _ => inp eT thr
    (some (s!"V={fmt V};g={fmt g};thr={thr};e={fmt eT};n={n.toUInt64}", c), r)
  | _ => (none, r)

def typical : Array Entry := Id.run do
  let mut out := #[]
  let mut i := 0
  for iv in [0:11] do
    for ig in [0:8] do
      for thr in [0.0, 0.6, 1.0] do
        let V := 30 + 3 * iv.toFloat
        let g := -0.5 + 0.1 * ig.toFloat
        if let some (c, _) := trimCommit h0 V g thr then
         if commitOk c then
          out := out.push ⟨"typical", i, s!"V={fmt V};g={fmt g};thr={thr}", c⟩
          i := i + 1
  return out

def family (fam : String) (seed : UInt64) (count tries : Nat) : Array Entry := Id.run do
  let mut r : Rng := ⟨seed⟩
  let mut out := #[]
  for _ in [0:tries] do
    if out.size ≥ count then break
    let (d, r') := draw fam r
    r := r'
    if let some (p, c) := d then
      if commitOk c then out := out.push ⟨fam, out.size, p, c⟩
  return out

end Ci.Gen

open Ci.Gen in
def main (args : List String) : IO Unit := do
  match args with
  | ["stall"] =>
    for i in [0:12] do
      let V := 32 - 1.0 * i.toFloat
      let (s, el) := trimFx 1000 V 0 0
      let r := residFx s (inp el 0)
      IO.println s!"V {V} alpha {thOf s} elev {el} resid {r.1} {r.2}"
  | ["gen", out, n] =>
    let n := n.toNat!
    let mut all := Ci.Gen.typical
    IO.println s!"typical: {all.size}"
    for (fam, seed) in [("push", 101), ("zoom", 202), ("fastdive", 303), ("slowidle", 404), ("elevtrans", 505)] do
      let es := family fam seed n (20 * n)
      IO.println s!"{fam}: {es.size}"
      all := all ++ es
    let text := "\n".intercalate (benchHeader :: (all.map Entry.toLine).toList) ++ "\n"
    IO.FS.writeFile out text
    IO.println s!"{all.size} entries -> {out}, fnv1a {fnv1a text.toUTF8}"
  | _ => IO.println "usage: cigen stall | cigen gen OUT N_PER_FAMILY"
