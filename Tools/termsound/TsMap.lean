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
* `W wn we wd` (bits): a constant wind (NED, ft/s, JSBSim's `wind` state) for the following `M`, `S`, `D`.
* `D psi north h y1..y32`: the internals of one frame (`diag`).
* `H b`: the candidate level-off at altitude `b` (m) for following `M` and `S` (`H` of NaN: the gate's law).
* `K`: the row keys of the tables the climb reads (`tableKeys`).
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

/-! ### A candidate level-off (not in the gate)

The straight escape with the commanded flight-path gradient capped by an altitude hold:
`gc = min(gc_climb, clamp(K_HOLD · (hRef − h), −GC_HI, GC_HI))`. Below `hRef − gc_climb / K_HOLD` it is the gate's law
exactly; at `hRef` it commands level flight. Everything else is copied from `CityGate.Esc.Law` unchanged. Used only
to evaluate the level-flight trim the proof would need above `zTop` (`docs/termsound-proof.tex`). -/

def K_HOLD : Float := 0.005

def elevHold (hRef : Float) (l : Law) (o : FloatArray) (v g cphi vRef : Float) : Float × Law :=
  let gc := fmin (clamp (GC_REF + KV * (v - vRef)) GC_LO GC_HI) (clamp (K_HOLD * (hRef - o[2]!)) (-GC_HI) GC_HI)
  let nLong := g.cos + v * KG * (gc - g) / G0
  let ncmd := if cphi < 0.35 then NMIN else clamp (nLong / cphi) NMIN NMAX
  let rv2 := rhoOf o[2]! * v * v
  let acmd := fmin (A0 + KA0 * ncmd / rv2) AMAX
  let nAch := (acmd - A0) * rv2 / KA0
  let qcmd := G0 * (nAch - g.cos * cphi) / v
  let sc := if VS > 0.0 then fmin ((VS / v) * (VS / v)) 1.0 else 1.0
  let ea := acmd - o[13]!
  let eRaw := E0 + E1 * acmd + KQF * qcmd * 40.0 / v + sc * (KA * ea - KQ * (o[11]! - qcmd)) + l.ia
  let e := clamp eRaw (-1.0) 1.0
  let ia := if e == eRaw || ea * l.ia < 0.0 then clamp (l.ia + KI_A * ea * DT_JSB) (-0.4) 0.4 else l.ia
  (e, { l with ia })

def controlsHold (hRef : Float) (l : Law) (o : FloatArray) : Surf × Law :=
  let gh := (obN o * obN o + obE o * obE o).sqrt
  let v := fmax o[6]! 10.0
  let g := Float.atan2 (-(obD o)) gh
  let phi := o[7]!
  let sphi := phi.sin
  let cphi := phi.cos
  let dir := ESC_DIR[l.esc]!
  let bank := ESC_BANK[l.esc]!
  let (e, l) := elevHold hRef l o v g cphi V_REF[l.esc]!
  let track := Float.atan2 (obE o) (obN o)
  let l := if !l.turning && l.t ≥ T_PULL_MIN[l.esc]! && (g ≥ GAM_TURN || l.t ≥ T_PULL_MAX) then
      { l with psiRef := track } else l
  let phiT :=
    if l.esc == STREET then
      if l.side != 0.0 then l.side * bank
      else if l.axis.isNaN then 0.0
      else clamp (K_STREET * wrap (l.axis - track)) (-BANK_STREET) BANK_STREET
    else if !l.turning then
      if KEEP_BANK && dir * phi > 0.0 then dir * fmin phi.abs bank else 0.0
    else if dir == 0.0 then clamp (KPSI * wrap (l.psiRef - track)) (-0.15) 0.15
    else dir * bank
  let ephi := phiT - phi
  let (kphi, kp) := if l.esc == STREET then (ROLL_STREET_PHI, ROLL_STREET_P) else (KPHI, KP)
  let ailRaw := kphi * ephi - kp * o[10]! + l.iphi
  let ail := clamp ailRaw (-1.0) 1.0
  let iphi :=
    if l.esc == STREET then
      if ail == ailRaw && ephi.abs < 0.1 then clamp (l.iphi + ROLL_STREET_I * ephi * DT_JSB) (-0.45) 0.45
      else l.iphi
    else if ail == ailRaw || ephi * l.iphi < 0.0 then clamp (l.iphi + KI_PHI * ephi * DT_JSB) (-0.3) 0.3
    else l.iphi
  let rTurn := G0 / v * sphi
  let beta := o[14]!
  let rudRaw := -KB * beta + KR * (o[12]! - rTurn) + l.ib
  let rud := clamp rudRaw (-1.0) 1.0
  let ib := if rud == rudRaw || beta * l.ib > 0.0 then clamp (l.ib - KI_B * beta * DT_JSB) (-0.5) 0.5 else l.ib
  (⟨-e, ail, rud, 1.0⟩, { l with iphi, ib })

/-- `Law.step` with the level-off (straight escape: no capture or street turn). -/
def stepHold (hRef : Float) (l : Law) (p : Plane) : Surf × Law :=
  let (u, l) := controlsHold hRef l p.ob
  (u, { l with t := l.t + DT_JSB })

/-- One frame of the closed loop (`Law.step`, then `Plane.step`); with `smooth`, the quaternion is first scaled to
unit length (`unitQ`). The law reads only `ob`, which does not depend on the quaternion's norm. -/
def frame (st : State Float) (l : Law) (ob : FloatArray) (smooth : Bool := false) (hold : Float := NAN) :
    State Float × Law × FloatArray :=
  let st := if smooth then unitQ st else st
  let p : Plane := { st, ob, ox := 0, oy := 0 }
  let (u, l') := if hold.isNaN then l.step p else stepHold hold l p
  let p' := p.step u
  (p'.st, l', p'.ob)

/-- Discrete-relevant internals of one frame from `(st, l, ob)`, for locating switches: the plant's diagnostics
(alpha, beta, airspeed ft/s, Mach, static pressure psf, density, h/b for ground effect), the propeller's advance
ratio and tip Mach (as `propeller` computes them), the engine's fuel/air ratio (`mdotFuel / mdotAir`), rpm and
manifold pressure, the surface commands, and the law's pre-clamp values (`gc`, `nLong / cos φ`, `acmd`, elevator,
aileron and rudder before clamping, bank target before clamping, gain scheduling factor `sc`). -/
def diag (st : State Float) (l : Law) (ob : FloatArray) : Array Float :=
  let p : Plane := { st, ob, ox := 0, oy := 0 }
  let (u, _) := l.step p
  let i : JsbExact.Input Float := { elev := u.elev, ail := u.ail, rud := u.rud, thr := u.thr, mix := 0.9, brkL := 0, brkR := 0 }
  let (s', d) := JsbExact.step st i (fuelFreeze := true)
  -- propeller advance ratio and tip Mach, as `JsbExact.propeller` with the frame's aero velocities
  let mT : M33 Float := m9 Gen.propT
  let loc : V3 Float := v3 Gen.propXYZ
  let dxyz := structToBody s'.cg loc
  let lv := mT.T.mulV (V3.add d.uvw (V3.cross d.pqr dxyz))
  let rps := st.rpm / 60.0
  let dia := Gen.Diameter
  let vtip := rps * dia * 3.141592653589793
  let tipMach := Float.sqrt (vtip * vtip + lv.x * lv.x) / d.a
  let jAdv := if rps > 0.01 then lv.x / (dia * rps) else lv.x / dia
  let pAmb := d.p * Gen.psftopa
  let far := 1.3 * 0.9 * 101325.0 / pAmb / 14.7
  -- law internals (`Law.elevCegis`, `Law.controls`)
  let o := ob
  let gh := (obN o * obN o + obE o * obE o).sqrt
  let v := fmax o[6]! 10.0
  let g := Float.atan2 (-(obD o)) gh
  let cphi := o[7]!.cos
  let gcRaw := GC_REF + KV * (v - V_REF[0]!)
  let gc := clamp gcRaw GC_LO GC_HI
  let nLong := g.cos + v * KG * (gc - g) / G0
  let nRaw := nLong / cphi
  let ncmd := if cphi < 0.35 then NMIN else clamp nRaw NMIN NMAX
  let rv2 := rhoOf o[2]! * v * v
  let acmdRaw := A0 + KA0 * ncmd / rv2
  let acmd := fmin acmdRaw AMAX
  let nAch := (acmd - A0) * rv2 / KA0
  let qcmd := G0 * (nAch - g.cos * cphi) / v
  let sc := if VS > 0.0 then fmin ((VS / v) * (VS / v)) 1.0 else 1.0
  let ea := acmd - o[13]!
  let eRaw := E0 + E1 * acmd + KQF * qcmd * 40.0 / v + sc * (KA * ea - KQ * (o[11]! - qcmd)) + l.ia
  let track := Float.atan2 (obE o) (obN o)
  let phiTRaw := KPSI * wrap (l.psiRef - track)
  let ailRaw := KPHI * (clamp phiTRaw (-0.15) 0.15 - o[7]!) - KP * o[10]! + l.iphi
  let rudRaw := -KB * o[14]! + KR * (o[12]! - G0 / v * o[7]!.sin) + l.ib
  #[d.alpha, d.beta, d.vt, d.mach, d.p, d.rho, d.hmac, jAdv, tipMach, far, st.rpm, st.tmap, d.thrust, d.hp,
    u.elev, u.ail, u.rud, gcRaw, nRaw, acmdRaw, eRaw, ailRaw, rudRaw, phiTRaw, sc, d.adot, s'.stall]

/-- Row keys of the tables a straight climb reads, one table per line (name, then keys). -/
def tableKeys : List (String × Array Float) :=
  let col0 (t : Table) : Array Float := (List.range t.rows).toArray.map fun r => t.data[(r + 1) * (t.cols + 1)]!
  [("CLwbh", col0 Gen.tab_CLwbh_7), ("CDwbh", col0 Gen.tab_CDwbh_3), ("CYp", col0 Gen.tab_CYp_5),
   ("CYr", col0 Gen.tab_CYr_6), ("Clr", col0 Gen.tab_Clr_10), ("kCLge", col0 Gen.tab_kCLge_1),
   ("kCDge", col0 Gen.tab_kCDge_0), ("cThrust", col0 Gen.tab_cThrust), ("cPower", col0 Gen.tab_cPower),
   ("CtMach", col0 Gen.tab_CtMach), ("CpMach", col0 Gen.tab_CpMach), ("mixEff", col0 Gen.tab_mixEff),
   ("stdTemp", col0 Gen.tab_stdTemp)]

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
  let mut wind : V3 Float := V3.zero
  let mut hold : Float := NAN
  repeat
    let ln ← stdin.getLine
    if ln.isEmpty then break
    let w := (ln.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.toArray
    if w.isEmpty then continue
    let cmd := w[0]!
    if cmd == "Z" then
      smooth := w[1]! == "1"
    else if cmd == "K" then
      for (n, ks) in tableKeys do
        stdout.putStrLn (n ++ " " ++ " ".intercalate (ks.toList.map toString))
      stdout.putStrLn "END"
    else if cmd == "H" then
      hold := ofBits w[1]!
    else if cmd == "W" then
      wind := ⟨ofBits w[1]!, ofBits w[2]!, ofBits w[3]!⟩
    else if cmd == "D" then
      let psi := ofBits w[1]!; let north := ofBits w[2]!; let h := ofBits w[3]!
      let y := (w.extract 4 36).map ofBits
      let (st, l, _) := place base psi north h y
      let st := { st with wind }
      let ob := obsOf st
      stdout.putStrLn (line (diag (if smooth then unitQ st else st) l ob))
    else if cmd == "M" then
      let psi := ofBits w[1]!; let north := ofBits w[2]!; let h := ofBits w[3]!
      let y := (w.extract 4 36).map ofBits
      let (st, l, _) := place base psi north h y
      let st := { st with wind }
      let ob := obsOf st
      let (st', l', ob') := frame st l ob smooth hold
      let (h', y') := chart psi st' l' ob'
      stdout.putStrLn (line (#[h'] ++ y' ++ #[ob'[1]!, ob'[0]!]))
    else if cmd == "S" then
      let psi := ofBits w[1]!; let north := ofBits w[2]!; let h := ofBits w[3]!
      let y := (w.extract 4 36).map ofBits
      let n := w[36]!.toNat!; let k := w[37]!.toNat!
      let (st0, l0, _) := place base psi north h y
      let mut st := { st0 with wind }; let mut l := l0; let mut ob := obsOf { st0 with wind }
      for i in [0:n+1] do
        if i % k == 0 then
          let (h', y') := chart psi st l ob
          stdout.putStrLn (toString i ++ " " ++ line (#[ob[1]!, ob[0]!, h'] ++ y'))
        let r := frame st l ob smooth hold
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
