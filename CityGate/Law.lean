import CityGate.Terminal

/-! The escape law of `flight/src/envfilter.rs` (`Law`, with the default gains `law_params()` = `LAW_CEGIS2`, a
cegis elevator law), ported over `Float` with Rust's operation order. Not trusted: the gate's rollouts fly it
on the plant itself, so nothing about it needs proving. -/

namespace CityGate.Esc

def G0 : Float := 9.80665
def DT_JSB : Float := 0.0078125

/-- Escapes: turn direction (JSBSim sign, +1 = bank right) and bank (rad): straight, left/right at 30° and 40°,
and the street escape. -/
def ESC_DIR : Array Float := #[0.0, -1.0, 1.0, -1.0, 1.0, 0.0]
def ESC_BANK : Array Float := #[0.0, 0.52, 0.52, 0.7, 0.7, 0.7]
def N_ESC : Nat := 6
def STREET : Nat := 5
def STREET_CAPTURE : Float := 25.0 * PI / 180.0
def K_STREET : Float := 2.0
def BANK_STREET : Float := 0.35
def M_TRIGGER : Float := 10.0
def ROLL_STREET_PHI : Float := 4.0
def ROLL_STREET_P : Float := 2.5
def ROLL_STREET_I : Float := 3.0

/-! `LAW_CEGIS2`. -/
def V_REF : Array Float := #[35.0, 35.0, 35.0, 36.0, 36.0, 35.0]
def T_PULL_MIN : Array Float := #[1.5, 1.5, 1.5, 0.0, 0.0, 1.5]
def KEEP_BANK : Bool := true
def NMAX : Float := 3.5
def AMAX : Float := 0.24
def KV : Float := 0.02
def GC_LO : Float := 0.05
def GC_HI : Float := 0.35
def GC_REF : Float := 0.15
def KG : Float := 2.5
def NMIN : Float := 0.3
def A0 : Float := -0.058
def KA0 : Float := 205.0
def KA : Float := 3.0
def KQ : Float := 1.2
def E0 : Float := -0.21
def E1 : Float := 2.49
def KI_A : Float := 2.0
def VS : Float := 50.0
def KQF : Float := 0.6
def KPHI : Float := 2.5
def KI_PHI : Float := 1.0
def KP : Float := 0.8
def KPSI : Float := 1.0
def KB : Float := 2.0
def KI_B : Float := 2.0
def KR : Float := 0.5
def T_PULL_MAX : Float := 6.0
def GAM_TURN : Float := 0.03

/-! The law's numeric literals as constants: a `Float` literal inside a function body is converted from decimal on
every call. -/
def F0_0 : Float := 0.0
def F2_2558em5 : Float := 2.2558e-5
def F0_05 : Float := 0.05
def F0_1 : Float := 0.1
def F0_15 : Float := 0.15
def F0_25 : Float := 0.25
def F0_3 : Float := 0.3
def F0_35 : Float := 0.35
def F0_4 : Float := 0.4
def F0_45 : Float := 0.45
def F0_5 : Float := 0.5
def F1_0 : Float := 1.0
def F1_225 : Float := 1.225
def F4_256 : Float := 4.256
def F10_0 : Float := 10.0
def F40_0 : Float := 40.0

def rhoOf (h : Float) : Float := F1_225 * (fmax (F1_0 - F2_2558em5 * h) F0_5).pow F4_256

/-- The escape law's state (`Law`): which escape, time since it began, integrators, the track held once the
pull-up ends, and the street escape's axis, helix side and next look. -/
structure Law where
  esc : Nat
  t : Float
  ia : Float
  ib : Float
  iphi : Float
  psiRef : Float
  axis : Float
  side : Float
  nextTry : Float
  captured : Bool
  deriving Inhabited

def Law.new (esc : Nat) : Law :=
  { esc, t := F0_0, ia := F0_0, ib := F0_0, iphi := F0_0, psiRef := NAN, axis := NAN, side := F0_0, nextTry := F0_0,
    captured := false }

def Law.turning (l : Law) : Bool := !l.psiRef.isNaN

/-- Turn direction of the terminal set (0 = a straight climb). -/
def Law.dir (l : Law) : Float := if l.esc == STREET then l.side else ESC_DIR[l.esc]!

/-! Observation fields (`CityJsb.obs`). -/
def obN (o : FloatArray) : Float := o[3]!
def obE (o : FloatArray) : Float := o[4]!
def obD (o : FloatArray) : Float := o[5]!

/-- Street escape: capture the nearest street axis from the starting track, once. -/
def Law.capture (l : Law) (o : FloatArray) : Law :=
  if l.captured || l.esc != STREET then l
  else
    let track := Float.atan2 (obE o) (obN o)
    let a := (track / FRAC_PI_2).round * FRAC_PI_2
    { l with captured := true, axis := if (wrap (a - track)).abs ≤ STREET_CAPTURE then a else l.axis }

/-- Street escape, every 0.25 s once the climb is established on the axis: start the helix toward the first side
(left, then right) whose predicted annulus is clear at the current height. -/
def Law.streetTurn (l : Law) (p : Plane) : Law :=
  if l.esc != STREET || l.axis.isNaN || l.side != F0_0 || !l.turning || l.t < l.nextTry then l
  else
    let l := { l with nextTry := l.t + F0_25 }
    let o := p.ob
    if (wrap (l.axis - Float.atan2 (obE o) (obN o))).abs > F0_05 then l
    else
      let (x, y, z) := p.pos
      let psi := Float.atan2 (obN o) (obE o)
      let vh := (obN o * obN o + obE o * obE o).sqrt
      let r := vh * vh / (G0 * (ESC_BANK[STREET]!).tan)
      let c := psi.cos
      let sn := psi.sin
      let sideOK := fun (side : Float) =>
        helixClear (x + vh * c + side * r * sn) (y + vh * sn - side * r * c) r M_TRIGGER z
      if sideOK (-F1_0) then { l with side := -F1_0 } else if sideOK F1_0 then { l with side := F1_0 } else l

/-- Elevator (+1 nose up) from the cegis law, and the updated α integral. -/
def Law.elevCegis (l : Law) (o : FloatArray) (v g cphi vRef : Float) : Float × Law :=
  let gc := clamp (GC_REF + KV * (v - vRef)) GC_LO GC_HI
  let nLong := g.cos + v * KG * (gc - g) / G0
  let ncmd := if cphi < F0_35 then NMIN else clamp (nLong / cphi) NMIN NMAX
  let rv2 := rhoOf o[2]! * v * v
  let acmd := fmin (A0 + KA0 * ncmd / rv2) AMAX
  let nAch := (acmd - A0) * rv2 / KA0
  let qcmd := G0 * (nAch - g.cos * cphi) / v
  let sc := if VS > F0_0 then fmin ((VS / v) * (VS / v)) F1_0 else F1_0
  let ea := acmd - o[13]!
  let eRaw := E0 + E1 * acmd + KQF * qcmd * F40_0 / v + sc * (KA * ea - KQ * (o[11]! - qcmd)) + l.ia
  let e := clamp eRaw (-F1_0) F1_0
  let ia := if e == eRaw || ea * l.ia < F0_0 then clamp (l.ia + KI_A * ea * DT_JSB) (-F0_4) F0_4 else l.ia
  (e, { l with ia })

/-- Surfaces for one frame (elevator positive nose down, aileron positive rolls right, rudder positive yaws left,
throttle), and the updated law state (`Law::controls`). -/
def Law.controls (l : Law) (o : FloatArray) : Surf × Law :=
  let gh := (obN o * obN o + obE o * obE o).sqrt
  let v := fmax o[6]! F10_0
  let g := Float.atan2 (-(obD o)) gh
  let phi := o[7]!
  let sphi := phi.sin
  let cphi := phi.cos
  let dir := ESC_DIR[l.esc]!
  let bank := ESC_BANK[l.esc]!
  let (e, l) := l.elevCegis o v g cphi V_REF[l.esc]!
  let track := Float.atan2 (obE o) (obN o)
  let l := if !l.turning && l.t ≥ T_PULL_MIN[l.esc]! && (g ≥ GAM_TURN || l.t ≥ T_PULL_MAX) then
      { l with psiRef := track } else l
  let phiT :=
    if l.esc == STREET then
      if l.side != F0_0 then l.side * bank
      else if l.axis.isNaN then F0_0
      else clamp (K_STREET * wrap (l.axis - track)) (-BANK_STREET) BANK_STREET
    else if !l.turning then
      if KEEP_BANK && dir * phi > F0_0 then dir * fmin phi.abs bank else F0_0
    else if dir == F0_0 then clamp (KPSI * wrap (l.psiRef - track)) (-F0_15) F0_15
    else dir * bank
  let ephi := phiT - phi
  let (kphi, kp) := if l.esc == STREET then (ROLL_STREET_PHI, ROLL_STREET_P) else (KPHI, KP)
  let ailRaw := kphi * ephi - kp * o[10]! + l.iphi
  let ail := clamp ailRaw (-F1_0) F1_0
  let iphi :=
    if l.esc == STREET then
      if ail == ailRaw && ephi.abs < F0_1 then clamp (l.iphi + ROLL_STREET_I * ephi * DT_JSB) (-F0_45) F0_45
      else l.iphi
    else if ail == ailRaw || ephi * l.iphi < F0_0 then clamp (l.iphi + KI_PHI * ephi * DT_JSB) (-F0_3) F0_3
    else l.iphi
  let rTurn := G0 / v * sphi
  let beta := o[14]!
  let rudRaw := -KB * beta + KR * (o[12]! - rTurn) + l.ib
  let rud := clamp rudRaw (-F1_0) F1_0
  let ib := if rud == rudRaw || beta * l.ib > F0_0 then clamp (l.ib - KI_B * beta * DT_JSB) (-F0_5) F0_5 else l.ib
  (⟨-e, ail, rud, F1_0⟩, { l with iphi, ib })

/-- One frame of the escape (`Law::step`): capture, street turn, surfaces; the clock advances. -/
def Law.step (l : Law) (p : Plane) : Surf × Law :=
  let l := (l.capture p.ob).streetTurn p
  let (u, l) := l.controls p.ob
  (u, { l with t := l.t + DT_JSB })

end CityGate.Esc
