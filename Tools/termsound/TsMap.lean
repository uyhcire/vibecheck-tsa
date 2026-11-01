import CityGate

/-! # `tsmap`: the escape closed loop as a frame map in local coordinates

Offline tooling for the informal proof of `TermSoundR` (`docs/termsound-proof.tex`, issue #36). It runs the real
plant (`CityGate.Plane.step`, i.e. `JsbExact.step` with fuel frozen) under the real escape law
(`CityGate.Esc.Law.step`) and exposes one frame of that closed loop in the proof's local coordinates:

* `chart`: closed-loop state ↦ (altitude `h`, 32 local coordinates `y`), the neutral modes (horizontal position, the
  Earth-rotation angle) dropped;
* `place`: (`h`, `y`) ↦ a closed-loop state at a chosen map point, Earth angle and held track; `chart ∘ place = id`
  up to rounding.

Numbers cross the pipe as the decimal `UInt64` bit patterns of `Float`s, so nothing is lost in printing.

Commands, one per stdin line (`b` = a bit pattern):
* `Z 1` / `Z 0`: the smoothed loop (`unitQ` before every frame) for the following `M` and `S` commands, or the
  plain one (the default).
* `M psi north h y1..y32` (all `b`): one frame from `place`, prints `h' y' east north` (the last two: the CG's
  displacement over the frame, m, Earth-fixed).
* `S psi north h y1..y32 N K` (`N`, `K` plain naturals): `N` frames from `place`, prints every `K`-th frame as
  `k east north h y`, plus the airframe-relevant Euler angles (part of `y`).
* `R x y z v gam psi phi n thr N K` (bits, then naturals): the straight escape from `CityGate.startPlane`, `N` frames,
  prints `k turning east north h y` every `K` frames (`y` relative to the held track once it is set, to 0 before).
* `O x y z v gam psi phi n thr N`: as `R`, but prints the largest bit difference between the plant's observation and
  `obsOf` of its state over the law-read and position fields (0 means `obsOf` reproduces it exactly).
-/

open CityGate Esc JsbExact S

namespace TsMap

def ft : Float := 0.3048

/-- The observation `CityJsb.obs` reports after a frame, recomputed from the state that frame ends in: the same
operations as the start of `JsbExact.step` (airborne, no ground contact). Fields 15–17 (load factor, height above
terrain, dynamic pressure), which the straight escape does not read, are 0. -/
def obsOf (s : State Float) : FloatArray :=
  let omega : V3 Float := v3 Gen.omega
  let ce : Float := cosS s.epa
  let se : Float := sinS s.epa
  let ti2ec := M33.mk' ce se zero (-se) ce zero zero zero one
  let locv := ti2ec.mulV s.ri
  let loc := locDerive locv
  let tec2l := loc.tec2l
  let ti2l := tec2l.mul ti2ec
  let tl2i := ti2l.T
  let ti2b := s.q.toM
  let tl2b := ti2b.mul tl2i
  let tb2l := tl2b.T
  let uvw := ti2b.mulV (V3.sub s.vi (V3.cross omega s.ri))
  let pqr := V3.sub s.pqri (ti2b.mulV omega)
  let euler := tl2b.toQuat.toM.euler
  let vned := tb2l.mulV uvw
  let hsl := loc.radius - seaLevelRadius loc
  let totalWind := V3.add (V3.add (V3.add s.wind V3.zero) V3.zero) V3.zero
  let aeroUVW := V3.sub uvw (tl2b.mulV totalWind)
  let u2 := aeroUVW.x * aeroUVW.x
  let v2 := aeroUVW.y * aeroUVW.y
  let w2 := aeroUVW.z * aeroUVW.z
  let mUW := u2 + w2
  let vt2 := mUW + v2
  let vt := sqrt vt2
  let (alpha, beta) : Float × Float :=
    if vt > 0.001 then
      let beta := atan2 aeroUVW.y (sqrt mUW)
      if mUW ≥ 1e-6 then (atan2 aeroUVW.z aeroUVW.x, beta) else (0, beta)
    else (0, 0)
  ⟨#[locv.z * ft, locv.y * ft, hsl * ft, vned.x * ft, vned.y * ft, vned.z * ft, vt * ft,
     euler.x, euler.y, euler.z, pqr.x, pqr.y, pqr.z, alpha, beta, 0, 0, 0, s.rpm, locv.x * ft, locv.y * ft,
     locv.z * ft]⟩

/-- Rotation from local NED axes to track axes (along, right, down) for a track `psi` clockwise from north. -/
def rTrack (psi : Float) : M33 Float :=
  let c := psi.cos
  let s := psi.sin
  M33.mk' c s 0 (-s) c 0 0 0 1

/-- The local-to-inertial rotation of a state (`Tl2i` of `JsbExact.step`). -/
def tl2iOf (s : State Float) : M33 Float :=
  let ce : Float := cosS s.epa
  let se : Float := sinS s.epa
  let ti2ec := M33.mk' ce se zero (-se) ce zero zero zero one
  let loc := locDerive (ti2ec.mulV s.ri)
  (loc.tec2l.mul ti2ec).T

def vec (v : V3 Float) : Array Float := #[v.x, v.y, v.z]

/-- Local coordinates of a closed-loop state for held track `psi`: altitude (m) and 32 coordinates
`[φ, θ, ψ−psi, v_along, v_right, v_down, p_i, q_i, r_i, Δv⁰(3), Δv¹(3), a⁰(3), a¹(3), ṗ_i, q̇_i, ṙ_i, u̇, v̇, ẇ, rpm,
MAP, ia, ib, iphi]` (SI units; the inertial vectors in track axes). -/
def chart (psi : Float) (st : State Float) (l : Law) (ob : FloatArray) : Float × Array Float :=
  let rt := rTrack psi
  let ti2t := rt.mul (tl2iOf st).T
  let tr (v : V3 Float) : V3 Float := V3.smul ft (ti2t.mulV v)
  let vt := V3.smul ft (rt.mulV ⟨ob[3]! / ft, ob[4]! / ft, ob[5]! / ft⟩)
  (ob[2]!,
   #[ob[7]!, ob[8]!, wrap (ob[9]! - psi)] ++ vec vt ++ vec st.pqri ++ vec (tr (V3.sub st.vi st.vih0))
   ++ vec (tr (V3.sub st.vih0 st.vih1)) ++ vec (tr st.uvwidot) ++ vec (tr st.aih0) ++ vec st.pqridot
   ++ vec (V3.smul ft st.uvwdot) ++ #[st.rpm, st.tmap, l.ia, l.ib, l.iphi])

/-- A closed-loop state with local coordinates `(h, y)`: at `north` m north of the map origin (latitude 0),
longitude 0, Earth angle 0, held track `psi`; fields the coordinates do not cover (mass, tanks, engine flags,
gears, wind, stall flag) are copied from `base`. The law is the straight escape past its pull-up. -/
def place (base : State Float) (psi north h : Float) (y : Array Float) : State Float × Law × FloatArray :=
  let ri : V3 Float := ⟨Gen.a + h / ft, 0, north / ft⟩
  let tec2l := (locDerive ri).tec2l
  let tl2i := tec2l.T
  let l2b := CityJsb.tl2bOf y[0]! y[1]! (psi + y[2]!)
  let ti2b := l2b.mul tec2l
  let q := ti2b.toQuat
  let t2i := tl2i.mul (rTrack psi).T
  let un (i : Nat) : V3 Float := t2i.mulV ⟨y[i]! / ft, y[i+1]! / ft, y[i+2]! / ft⟩
  let raw (i : Nat) : V3 Float := ⟨y[i]!, y[i+1]!, y[i+2]!⟩
  let omega : V3 Float := v3 Gen.omega
  let vi := V3.add (un 3) (V3.cross omega ri)
  let vih0 := V3.sub vi (un 9)
  let vih1 := V3.sub vih0 (un 12)
  let pqri := raw 6
  let st : State Float :=
    { base with q, qdot := q.qdot pqri, pqri, ri, vi, vih0, vih1, aih0 := un 18, epa := 0, pqridot := raw 21,
                uvwidot := un 15, uvwdot := V3.smul (1 / ft) (raw 24), rpm := y[27]!, tmap := y[28]! }
  let l : Law := { Law.new 0 with t := 100.0, psiRef := psi, ia := y[29]!, ib := y[30]!, iphi := y[31]! }
  (st, l, obsOf st)

/-- `st` with its quaternion scaled to unit length (and `qdot` recomputed from it). `JsbExact.step` renormalises
only when the norm is off by at least 1e-10, so its quaternion norm is a hidden state in [1, 1 + 1e-10] that makes
the frame map jump by about 1e-10; the smoothed loop (`frame true`) removes it for differentiation. -/
def unitQ (st : State Float) : State Float :=
  let q := st.q
  let n := Float.sqrt (q.q0 * q.q0 + q.q1 * q.q1 + q.q2 * q.q2 + q.q3 * q.q3)
  let q : Quat Float := ⟨q.q0 / n, q.q1 / n, q.q2 / n, q.q3 / n⟩
  { st with q, qdot := q.qdot st.pqri }

/-- One frame of the closed loop (`Law.step`, then `Plane.step`); with `smooth`, the quaternion is first scaled to
unit length (`unitQ`). The law reads only `ob`, which does not depend on the quaternion's norm. -/
def frame (st : State Float) (l : Law) (ob : FloatArray) (smooth : Bool := false) : State Float × Law × FloatArray :=
  let st := if smooth then unitQ st else st
  let p : Plane := { st, ob, ox := 0, oy := 0 }
  let (u, l') := l.step p
  let p' := p.step u
  (p'.st, l', p'.ob)

def bits (f : Float) : String := toString f.toBits.toNat
def ofBits (s : String) : Float := Float.ofBits (s.toNat!.toUInt64)
def line (xs : Array Float) : String := " ".intercalate (xs.toList.map bits)

/-- A settled in-flight state for the fields `place` copies (`base`): the straight escape from 300 m, 40 m/s, 30 s. -/
def mkBase : State Float := Id.run do
  let mut p := startPlane 0 0 300 40 0 0 0 1 1
  let mut l := Law.new 0
  for _ in [0:3840] do
    let (u, l') := l.step p
    p := p.step u
    l := l'
  return p.st

def main : IO Unit := do
  let base := mkBase
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut smooth := false
  repeat
    let ln ← stdin.getLine
    if ln.isEmpty then break
    let w := (ln.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.toArray
    if w.isEmpty then continue
    let cmd := w[0]!
    if cmd == "Z" then
      smooth := w[1]! == "1"
    else if cmd == "M" then
      let psi := ofBits w[1]!; let north := ofBits w[2]!; let h := ofBits w[3]!
      let y := (w.extract 4 36).map ofBits
      let (st, l, ob) := place base psi north h y
      let (st', l', ob') := frame st l ob smooth
      let (h', y') := chart psi st' l' ob'
      stdout.putStrLn (line (#[h'] ++ y' ++ #[ob'[1]!, ob'[0]!]))
    else if cmd == "S" then
      let psi := ofBits w[1]!; let north := ofBits w[2]!; let h := ofBits w[3]!
      let y := (w.extract 4 36).map ofBits
      let n := w[36]!.toNat!; let k := w[37]!.toNat!
      let (st0, l0, ob0) := place base psi north h y
      let mut st := st0; let mut l := l0; let mut ob := ob0
      for i in [0:n+1] do
        if i % k == 0 then
          let (h', y') := chart psi st l ob
          stdout.putStrLn (toString i ++ " " ++ line (#[ob[1]!, ob[0]!, h'] ++ y'))
        let r := frame st l ob smooth
        st := r.1; l := r.2.1; ob := r.2.2
      stdout.putStrLn "END"
    else if cmd == "R" || cmd == "O" then
      let a := (w.extract 1 10).map ofBits
      let n := w[10]!.toNat!
      let k := if cmd == "R" then w[11]!.toNat! else 1
      let mut p := startPlane a[0]! a[1]! a[2]! a[3]! a[4]! a[5]! a[6]! a[7]! a[8]!
      let mut l := Law.new 0
      let mut worst : Nat := 0
      for i in [0:n+1] do
        if cmd == "R" && i % k == 0 then
          let psi := if l.turning then l.psiRef else 0
          let (h', y') := chart psi p.st l p.ob
          let (x, yy, _) := p.pos
          stdout.putStrLn (toString i ++ " " ++ (if l.turning then "1" else "0") ++ " " ++ line (#[x, yy, h'] ++ y'))
        if cmd == "O" then
          let o := obsOf p.st
          for j in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18, 19, 20, 21] do
            let d := (o[j]!.toBits.toNat : Int) - (p.ob[j]!.toBits.toNat : Int)
            worst := max worst d.natAbs
        let (u, l') := l.step p
        p := p.step u
        l := l'
      if cmd == "O" then stdout.putStrLn s!"obs max bit difference {worst}"
      stdout.putStrLn "END"
    stdout.flush

end TsMap

def main : IO Unit := TsMap.main
