import Jsb.C172Aero

/-! Longitudinal port of JSBSim's `c172p` (wings level, no sideslip), generic over `Scalar`; `Fx` runs it.

Units: m, s, rad, t, kN, kPa, kW, K.  One JSBSim step is `integrate` (FGPropagate runs first) followed by
`evaluate` (atmosphere, auxiliary, FCS, propulsion, aerodynamics, accelerations).  `tickAB` runs 8 steps of
1/128 s with JSBSim's default integrators; `tickEuler` runs 4 forward-Euler steps of 1/64 s. -/

namespace Jsb
open Vibecheck Jsb.C172

variable {α : Type} [Scalar α]

/-- State at a step boundary, including every value JSBSim carries into the next step. -/
structure StateOf (α : Type) where
  /-- along-track distance, m -/
  x : α
  /-- altitude, m -/
  h : α
  /-- ground speed, m/s -/
  vx : α
  /-- climb rate, m/s -/
  vz : α
  /-- body x axis as (horizontal, up) unit vector: (cos theta, sin theta) -/
  dx : α
  dz : α
  /-- pitch rate, rad/s -/
  q : α
  /-- engine (= propeller) rpm -/
  rpm : α
  /-- manifold pressure after its first-order lag, kPa -/
  tmap : α
  /-- body-axis acceleration of the last step; feeds alpha-dot of the next step -/
  udot : α
  wdot : α
  /-- stall hysteresis bit as 0 or 1 -/
  stall : α
  /-- derivatives from the last step: world horizontal/up acceleration and pitch acceleration -/
  ah : α
  au : α
  qd : α
  /-- world acceleration one step earlier (Adams-Bashforth 2) -/
  ah1 : α
  au1 : α
  /-- climb rate one and two steps earlier (Adams-Bashforth 3 for altitude) -/
  pvz : α
  pvz2 : α
  deriving Inhabited, Repr

abbrev State := StateOf Fx

/-- Elevator in our convention (+1 nose up, JSBSim command = -elev) and throttle in [0, 1].
`beta` and `phi` are optional lateral disturbances (sideslip and bank, rad); 0 is wings level and coordinated. -/
structure InputOf (α : Type) where
  elev : α
  thr : α
  beta : α
  phi : α
  deriving Inhabited, Repr

abbrev Input := InputOf Fx

/-- `1 - x^2/2 + x^4/24`, accurate for |x| < 1. -/
def cosSmall (x : α) : α := let x2 := x * x; 1 - x2 / 2 + (x2 * x2) / 24

/-- `x - x^3/6 + x^5/120`, accurate for |x| < 1. -/
def sinSmall (x : α) : α := let x2 := x * x; x - (x * x2) / 6 + (x * x2 * x2) / 120

/-- Mixture position fixed as in `sysid/collect.py`. -/
def mixPos : α := Scalar.lit 58982

/-- `z` when `a = 0` and `b = 0`, else `e`. -/
def ifZero2 (a b z e : α) : α :=
  Scalar.selLe a 0 (Scalar.selLe 0 a (Scalar.selLe b 0 (Scalar.selLe 0 b z e) e) e) e

/-- Intermediate quantities of one evaluation, for comparison with JSBSim's own properties. -/
structure ProbeOf (α : Type) where
  rho : α
  alpha : α
  adot : α
  qbar : α
  fxA : α
  fzA : α
  mA : α
  fxP : α
  mP : α
  hp : α
  vind : α
  thrustKN : α
  cl : α
  cd : α
  tipMach : α
  ct : α
  adv : α
  deriving Inhabited, Repr

abbrev Probe := ProbeOf Fx

def iter {β : Type} (n : Nat) (f : β → β) (s : β) : β :=
  match n with
  | 0 => s
  | n + 1 => iter n f (f s)

/-- JSBSim FGPropagate: Adams-Bashforth 3 altitude, Adams-Bashforth 2 velocity, rectangular Euler attitude/rate. -/
def integrate (k : Nat) (ab : Bool) (s : StateOf α) : StateOf α :=
  let h' := if ab then s.h + Scalar.shr (Scalar.ab3 s.vz s.pvz s.pvz2) k else s.h + Scalar.shr s.vz k
  let vx' := if ab then s.vx + Scalar.shr (3 * s.ah - s.ah1) (k + 1) else s.vx + Scalar.shr s.ah k
  let vz' := if ab then s.vz + Scalar.shr (3 * s.au - s.au1) (k + 1) else s.vz + Scalar.shr s.au k
  let d := Scalar.shr s.q k
  let c := s.dx - Scalar.mulR s.dz d
  let sn := s.dz + Scalar.mulR s.dx d
  { s with x := s.x + Scalar.shr vx' k, h := h', vx := vx', vz := vz', q := s.q + Scalar.shr s.qd k,
           dx := Scalar.rnC c sn, dz := Scalar.rnS c sn, ah1 := s.ah, au1 := s.au, pvz := s.vz, pvz2 := s.pvz }

/-- Everything JSBSim computes after propagation: forces, moments, engine, derivatives. -/
def evaluate (k : Nat) (inp : InputOf α) (s : StateOf α) : StateOf α × ProbeOf α :=
  let rho := Scalar.atm atmRho s.h
  let pAmb := Scalar.atm atmP s.h
  let tK := Scalar.atm atmT s.h
  let aSnd := Scalar.atm atmA s.h
  let cphi := cosSmall inp.phi
  let sphi := sinSmall inp.phi
  let cbeta := cosSmall inp.beta
  -- body velocity: with bank and sideslip the lateral component b of the horizontal speed follows from beta
  let w0 := s.vx * s.dz - s.vz * s.dx
  let b := ifZero2 inp.beta inp.phi 0 ((Scalar.sqrt (s.vx * s.vx + s.vz * s.vz) * sinSmall inp.beta - sphi * w0) / cphi)
  let a := s.vx - (b * b) / (s.vx + s.vx)
  let u := a * s.dx + s.vz * s.dz
  let w' := a * s.dz - s.vz * s.dx
  let w := cphi * w' - sphi * b
  let vb := cphi * b + sphi * w'
  let mUW := u * u + w * w
  let vt := Scalar.sqrt mUW
  let vtot := Scalar.sqrt (mUW + vb * vb)
  let alpha := Scalar.atan2 w u
  let adot := Scalar.selLt (Scalar.lit 66) mUW ((u * s.wdot - w * s.udot) / mUW) 0
  let qbar := (rho * (mUW + vb * vb)) / 2000
  let mach := vtot / aSnd
  let ci2vel := wingChord / (vtot + vtot)
  -- flight control: pitch trim sum clipped to [-1, 1], then asymmetric travel
  let cmd := max (-1) (min 1 (-inp.elev))
  let elevDeg := Scalar.selLe 0 cmd (cmd * elevTravelDown) (cmd * elevTravelUp)
  let elevRad := (elevDeg * 1745) / 100000
  let stall := Scalar.selLt alphaHystHi alpha 1 (Scalar.selLt alpha alphaHystLo 0 s.stall)
  -- piston engine (FGPiston)
  let y := (mach * mach) / 5
  let pTot := pAmb * (1 + y * (Scalar.lit 229376 + y * (Scalar.lit 286720 + y * (Scalar.lit 71680 + y * Scalar.lit 17918))))
  let zt := (1 - inp.thr) * (1 - inp.thr) * engZThrottle
  let ze := Scalar.selLt (Scalar.lit 6554) s.rpm (engZeNum / s.rpm) 999999
  let coef := ze / (ze + engZAirbox + zt)
  let tmap := s.tmap - Scalar.shr (s.tmap - pTot * coef) k
  let pmep := (tmap - pAmb) * engVolEff
  let mratio := Scalar.selLt 0 tmap (min engCompRatio (pAmb / tmap)) engCompRatio
  let ve := Scalar.lit 15124 + (engCompRatio - mratio) / Scalar.lit 638976
  let mpsM := ((s.rpm * engStrokeIn) / 360) * Scalar.lit 19975
  let vdotL := ((engDispL * s.rpm) / 120) * engVolEff * ve
  let mdotAir := vdotL * ((tmap * Scalar.lit 228110) / tK)
  let fa := (Scalar.lit 85197 * mixPos * Scalar.lit 6640435 / pAmb) / Scalar.lit 963379
  let me := Scalar.tbl1 tblMixEff fa
  let ihp := Scalar.selLe (Scalar.lit 28836) s.rpm ((((mdotAir * fa) * Scalar.lit 520130) / engIsfc) * me - engStaticFriction)
                (0 - engStaticFriction)
  let fmep := 0 - (engFmepDynamic * mpsM + engFmepStatic)
  let hp := ihp + (((pmep + fmep) * engDispL) * (s.rpm / 1000)) / Scalar.lit 5864423
  let powKW := Scalar.selLe s.rpm (Scalar.lit 6554) (max 0 (hp * Scalar.lit 48870)) (hp * Scalar.lit 48870)
  -- fixed-pitch propeller (FGPropeller)
  let rps := s.rpm / 60
  let vel := u + s.q * thrusterBodyZ
  let mt := (rps * propDiameter * Scalar.lit 205887) / aSnd
  let mv := vel / aSnd
  let tipM := Scalar.sqrt (mt * mt + mv * mv)
  let adv := Scalar.selLt (Scalar.lit 655) rps (vel / (propDiameter * rps)) (vel / propDiameter)
  let ct := Scalar.tbl1 tblCT adv * Scalar.tbl1 tblCTMach tipM
  let cp := Scalar.tbl1 tblCP adv * Scalar.tbl1 tblCPMach tipM
  let thrust := ((((ct * propD4) * rho) * rps) * rps) / 1000
  let powReq := ((((cp * propD5) * rho) * rps) * rps / 1000) * rps
  let pav := powKW - powReq
  let rps' := rps + Scalar.shr ((pav / Scalar.selLt (Scalar.lit 655) rps rps 1) * Scalar.lit 733217) k
  let rpm' := max 0 (rps' * 60)
  let v2 := vel * Scalar.abs vel + (2000 * thrust) / (rho * propArea)
  let vind := Scalar.selLt 0 v2 ((Scalar.sqrt v2 - vel) / 2) ((0 - vel - Scalar.sqrt (0 - v2)) / 2)
  -- aerodynamics (generated functions)
  let e : AeroIn α := { adot := adot, alpha := alpha, ci2vel := ci2vel, elevRad := elevRad, flapDeg := 0,
                        hbMac := (s.h + rpBodyX * s.dz - rpBodyZ * s.dx) / wingSpan, magBeta := Scalar.abs inp.beta,
                        magElevRad := Scalar.abs elevRad, qAero := s.q, qbar := qbar, rho := rho,
                        stallHyst := stall, uAero := u, vInd := vind }
  let drag := dragForce e
  let lift := liftForce e
  let cosA := u / vt
  let sinA := w / vt
  let fxA := lift * sinA - drag * cosA * cbeta
  let fzA := 0 - drag * sinA * cbeta - lift * cosA
  let mA := pitchMomentRP e + rpBodyZ * fxA - rpBodyX * fzA
  let axb := (fxA + thrust) / massT
  let azb := fzA / massT
  -- local-frame accelerations on a rotating spherical Earth (equator, eastward track)
  let rKm := earthRadiusKm + s.h / 1000
  let ah := s.dx * axb + s.dz * azb * cphi - ((s.vz * s.vx) / 1000) / rKm - s.vz / omegaInv2
  let au := s.dz * axb - s.dx * azb * cphi - (gravity0 - (s.h / 1000) / gravScaleHKm) + ((s.vx * s.vx) / 1000) / rKm + s.vx / omegaInv2 + omega2R0
  let qd := (mA + thrusterBodyZ * thrust) / iyyT
  let udot := s.dx * ah + s.dz * au - s.q * w
  let wdot := s.dz * ah - s.dx * au + s.q * u
  ({ s with rpm := rpm', tmap := tmap, udot := udot, wdot := wdot, stall := stall, ah := ah, au := au, qd := qd },
   { rho := rho, alpha := alpha, adot := adot, qbar := qbar, fxA := fxA, fzA := fzA, mA := mA, fxP := thrust,
     mP := thrusterBodyZ * thrust, hp := hp, vind := vind, thrustKN := thrust, cl := f_CLwbh e, cd := f_CDwbh e,
     tipMach := tipM, ct := ct, adv := adv })

def step (k : Nat) (ab : Bool) (inp : InputOf α) (s : StateOf α) : StateOf α :=
  (evaluate k inp (integrate k ab s)).1

/-- One 1/16 s tick as JSBSim runs it: 8 steps of 1/128 s, Adams-Bashforth histories carried in the state. -/
def tickAB (inp : InputOf α) (s : StateOf α) : StateOf α := iter 8 (step 7 true inp) s

/-- One 1/16 s tick as 4 forward-Euler steps of 1/64 s (no history used). -/
def tickEuler (inp : InputOf α) (s : StateOf α) : StateOf α := iter 4 (step 6 false inp) s

/-- Quantities JSBSim logs for a state, recomputed by the model for that state (diagnostics only). -/
def probe (inp : InputOf α) (s : StateOf α) : StateOf α × ProbeOf α := evaluate 7 inp s

end Jsb
