import CityGate.Terminal
import CityGate.Landing

/-! Autoland escapes and the landing funnel: a line-by-line port of `flight/src/autoland.rs` (commit 216930a), over
`Float` in the same operation order. An autoland escape flies from anywhere onto final for the runway
(`CityGate.Landing`), down the glideslope, flares (John's sink-rate barrier), touches down and brakes to a stop. The
gate's check of an escape ends when it enters the landing funnel (`inFunnel`). Variants: 0 direct to the downwind
point `W`; 1 and 2 the same, turning left or right first; 3 a straight full-power climb for `CLIMB_T` first. -/

namespace CityGate.Esc
open CityGate.Landing

def G0 : Float := 9.80665
def DT_JSB : Float := 0.0078125

def rhoOf (h : Float) : Float := 1.225 * (fmax (1.0 - 2.2558e-5 * h) 0.5).pow 4.256

/-- Autoland variants (the gate's escape indices). -/
def N_AUTO : Nat := 4
/-- Longest escape check (s): from anywhere on the map to the funnel. -/
def HORIZON_FUNNEL : Float := 300.0

def RWY_X0 : Float := -100.0
def RWY_YC : Float := -1340.0
def RWY_Z : Float := 9.0
def TCH : Float := 15.0

def WX : Float := RWY_X0 - 1700.0
def WY : Float := RWY_YC + 600.0
def ZP : Float := 150.0
def CITY : Float := 1300.0
def INT_X0 : Float := RWY_X0 - 2600.0
def INT_X1 : Float := RWY_X0 - 1000.0
def INT_Y : Float := 1100.0
def L_INT : Float := 350.0
def L_LOC : Float := 250.0
def L_GND : Float := 60.0
def V_NAV : Float := 40.0
def V_FINAL : Float := 38.0
def V_SHORT : Float := 34.0
def GS : Float := 3.0 * PI / 180.0
def CLIMB_T : Float := 12.0
def GEAR_H : Float := 1.3
def FLARE_H : Float := 12.0
def SINK_MIN : Float := 0.9
def SINK_K : Float := 0.12
def BANK_NAV : Float := 25.0 * PI / 180.0
def BANK_FINAL : Float := 15.0 * PI / 180.0
def BANK_FLARE : Float := 5.0 * PI / 180.0

/-- Rust's `f64::to_radians`: `x * (π / 180)`. -/
def toRadians (x : Float) : Float := x * (PI / 180.0)

/-- `d` m before the threshold: the glideslope's map altitude. -/
def zGs (d : Float) : Float := RWY_Z + TCH + GS.tan * d

/-- Map position (`JsbPlant::state`'s x, y, z): east, north, JSBSim altitude + `mapDatum`. -/
def posOf (p : Plane) : Float × Float × Float := p.pos

/-- Fuel on board (lb, both tanks) if the engine is running, else -1 (`CityJsb.fuelE`). -/
def fuelOf (p : Plane) : Float := if p.st.running then p.st.tank0 + p.st.tank1 else -1

/-- The aircraft is in the landing funnel (`in_funnel`, `flight/src/runway.rs`). -/
def inFunnel (p : Plane) : Bool := Id.run do
  let (x, y, z) := posOf p
  let o := p.ob
  let d := RWY_X0 - x
  if !(funD0 ≤ d && d ≤ funD1) then return false
  if (y - RWY_YC).abs > fmax funLatFloor ((toRadians funLatDeg).tan * d) then return false
  let h := z - RWY_Z - TCH
  if h < (toRadians funGsLoDeg).tan * d || h > (toRadians funGsHiDeg).tan * d then return false
  if o[6]! < funVLo || o[6]! > funVHi then return false
  let chi := Float.atan2 o[4]! o[3]!
  if (wrap (chi - FRAC_PI_2)).abs > toRadians funTrackDeg || (o[7]!).abs > toRadians funBankDeg then return false
  let vz := -o[5]!
  if vz < funVzLo || vz > funVzHi then return false
  return fuelOf p ≥ funFuelLb

inductive Phase where
  | climb | nav | orbit | final | flare | rollout
  deriving BEq, Inhabited, Repr

/-- An autoland escape's state (`Auto`). -/
structure Auto where
  variant : Nat
  phase : Phase
  t : Float
  ia : Float
  iphi : Float
  ib : Float
  iv : Float
  chi0 : Float
  zHold : Float
  turned : Bool
  deriving Inhabited

def Auto.new (variant : Nat) : Auto :=
  { variant, phase := if variant == 3 then .climb else .nav, t := 0.0, ia := 0.0, iphi := 0.0, ib := 0.0,
    iv := 0.0, chi0 := NAN, zHold := NAN, turned := variant == 0 || variant == 3 }

def Auto.reset (a : Auto) : Auto := { a with ia := 0.0, iphi := 0.0, ib := 0.0, iv := 0.0 }

/-- Aileron for bank `phiC` (rad, positive right): roll PI-D (`Auto::roll`). -/
def Auto.roll (a : Auto) (o : FloatArray) (phiC : Float) : Float × Auto :=
  let ephi := phiC - o[7]!
  let raw := 2.5 * ephi - 0.8 * o[10]! + a.iphi
  let ail := clamp raw (-1.0) 1.0
  let iphi := if ail == raw || ephi * a.iphi < 0.0 then clamp (a.iphi + 1.0 * ephi * DT_JSB) (-0.3) 0.3 else a.iphi
  (ail, { a with iphi })

/-- One frame (`Auto::controls`): phase changes, then elevator, aileron, rudder, throttle, brake. -/
def Auto.controls (a0 : Auto) (q : Plane) : Surf × Auto := Id.run do
  let mut a := a0
  let (x, y, z) := posOf q
  let o := q.ob
  let v := fmax o[6]! 10.0
  let gh := (o[3]! * o[3]! + o[4]! * o[4]!).sqrt
  let gam := Float.atan2 (-o[5]!) gh
  let chi := Float.atan2 o[4]! o[3]!
  let hw := o[16]! - GEAR_H
  let d := RWY_X0 - x
  if a.chi0.isNaN then
    a := { a with chi0 := chi, zHold := z }
  -- Phase changes.
  if (a.phase == .climb || a.phase == .nav || a.phase == .orbit) && inFunnel q then
    a := { a with phase := .final }.reset
  if a.phase == .climb && a.t ≥ CLIMB_T then
    a := { a with phase := .nav, zHold := fmax a.zHold z }
  let inCity := x.abs < CITY && y.abs < CITY
  let nearW := ((x - WX) * (x - WX) + (y - WY) * (y - WY)).sqrt < 1500.0
  if a.phase == .nav && !inCity && nearW && z > ZP + 80.0 then
    a := { a with phase := .orbit }
  if a.phase == .orbit && z ≤ ZP + 30.0 then
    a := { a with phase := .nav }
  if a.phase == .final && hw < FLARE_H then
    a := { a with phase := .flare }
  if (a.phase == .final || a.phase == .flare) && hw < 0.25 then
    a := { a with phase := .rollout }
  else if a.phase == .rollout && hw > 0.6 then
    a := { a with phase := .flare }
  -- Guidance: track error, bank limit, flight path, speed, throttle.
  let mut thrFixed : Option Float := none
  let mut eChi := 0.0
  let mut bankMax := 0.0
  let mut gamC := 0.0
  let mut vC := 0.0
  match a.phase with
  | .climb =>
    thrFixed := some 1.0
    eChi := wrap (a.chi0 - chi); bankMax := BANK_NAV; gamC := 0.15; vC := V_NAV
  | .nav =>
    let intercept := (INT_X0 ≤ x && x ≤ INT_X1) && (y - RWY_YC).abs < INT_Y
    let (chiC, zT) :=
      if intercept then
        (FRAC_PI_2 + ((y - RWY_YC) / L_INT).atan, fmax (fmin (zGs d) ZP) (RWY_Z + 40.0))
      else
        let zt := if inCity then fmax ZP a.zHold else ZP
        (Float.atan2 (WX - x) (WY - y), zt)
    let mut e := wrap (chiC - chi)
    if intercept && e.abs > 2.0 then
      e := -(signum (y - RWY_YC)) * e.abs
    if !a.turned then
      if e.abs < 0.5 then
        a := { a with turned := true }
      else if a.variant == 1 && e > 0.0 then
        e := e - 2.0 * PI
      else if a.variant == 2 && e < 0.0 then
        e := e + 2.0 * PI
    eChi := e; bankMax := BANK_NAV; gamC := clamp (0.012 * (zT - z)) (-0.08) 0.12; vC := V_NAV
  | .orbit =>
    thrFixed := some 0.0
    let dir := if a.variant == 2 then 1.0 else -1.0
    eChi := dir * 10.0; bankMax := BANK_NAV; gamC := clamp (-0.08 + 0.02 * (v - V_NAV)) (-0.2) 0.0; vC := V_NAV
  | .final | .flare =>
    let chiC := FRAC_PI_2 + ((y - RWY_YC) / L_LOC).atan
    let gFinal := -GS + clamp (0.02 * (zGs d - z)) (-0.05) 0.05
    let vc := if hw < 30.0 then V_SHORT else V_FINAL
    if a.phase == .flare then
      let vzLim := -(SINK_MIN + SINK_K * fmax hw 0.0)
      if hw < 4.0 then thrFixed := some 0.0
      eChi := wrap (chiC - chi); bankMax := BANK_FLARE; gamC := fmax gFinal (clamp (vzLim / v) (-1.0) 1.0).asin
      vC := vc
    else
      eChi := wrap (chiC - chi); bankMax := BANK_FINAL; gamC := gFinal; vC := vc
  | .rollout =>
    let chiC := FRAC_PI_2 + ((y - RWY_YC) / L_GND).atan
    let e := wrap (chiC - chi)
    let (ail, a') := a.roll o 0.0
    let rud := clamp (-2.0 * e + 0.5 * o[12]!) (-1.0) 1.0
    let brk := if gh < 25.0 then 1.0 else 0.5
    let elev := if gh > 20.0 then 0.0 else -0.2
    return (⟨elev, ail, rud, 0.0, brk⟩, { a' with t := a'.t + DT_JSB })
  -- Lateral: bank toward the track command, roll PI-D, sideslip and coordinated-yaw rudder.
  let phiC := clamp (1.5 * eChi) (-bankMax) bankMax
  let (ail, a1) := a.roll o phiC
  a := a1
  let rTurn := G0 / v * (o[7]!).sin
  let rudRaw := -2.0 * o[14]! + 0.5 * (o[12]! - rTurn) + a.ib
  let rud := clamp rudRaw (-1.0) 1.0
  if rud == rudRaw || o[14]! * a.ib > 0.0 then
    a := { a with ib := clamp (a.ib - 2.0 * o[14]! * DT_JSB) (-0.5) 0.5 }
  -- Longitudinal: load factor for the flight-path command, then the angle-of-attack loop.
  let cphi := (o[7]!).cos
  let nLong := gam.cos + v * 1.0 * (gamC - gam) / G0
  let ncmd := if cphi < 0.35 then 0.3 else clamp (nLong / cphi) 0.3 2.5
  let rv2 := rhoOf o[2]! * v * v
  let acmd := fmin (-0.058 + 205.0 * ncmd / rv2) 0.2
  let nAch := (acmd + 0.058) * rv2 / 205.0
  let qcmd := G0 * (nAch - gam.cos * cphi) / v
  let sc := fmin ((50.0 / v) * (50.0 / v)) 1.0
  let ea := acmd - o[13]!
  let eRaw := -0.21 + 2.49 * acmd + 0.6 * qcmd * 40.0 / v + sc * (3.0 * ea - 1.2 * (o[11]! - qcmd)) + a.ia
  let e := clamp eRaw (-1.0) 1.0
  if e == eRaw || ea * a.ia < 0.0 then
    a := { a with ia := clamp (a.ia + 2.0 * ea * DT_JSB) (-0.4) 0.4 }
  -- Throttle: speed PI (or fixed).
  let mut thr := 0.0
  match thrFixed with
  | some t => thr := t
  | none =>
    let ev := vC - v
    let raw := 0.45 + 0.08 * ev + a.iv
    if (0.0 ≤ raw && raw ≤ 1.0) || ev * a.iv < 0.0 then
      a := { a with iv := clamp (a.iv + 0.04 * ev * DT_JSB) (-0.6) 0.6 }
    thr := clamp raw 0.0 1.0
  return (⟨-e, ail, rud, thr, 0.0⟩, { a with t := a.t + DT_JSB })

end CityGate.Esc
