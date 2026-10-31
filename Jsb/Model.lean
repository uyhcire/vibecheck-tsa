import Jsb.C172Aero

/-! Longitudinal port of JSBSim's `c172p` (wings level, no sideslip) in `Fx` fixed point.

Units: m, s, rad, t, kN, kPa, kW, K.  One JSBSim step is `integrate` (FGPropagate runs first) followed by
`evaluate` (atmosphere, auxiliary, FCS, propulsion, aerodynamics, accelerations).  `tickAB` runs 8 steps of
1/128 s with JSBSim's default integrators; `tickEuler` runs 4 forward-Euler steps of 1/64 s. -/

namespace Jsb
open Vibecheck Jsb.C172

/-- State at a step boundary, including every value JSBSim carries into the next step. -/
structure State where
  /-- along-track distance, m -/
  x : Fx
  /-- altitude, m -/
  h : Fx
  /-- ground speed, m/s -/
  vx : Fx
  /-- climb rate, m/s -/
  vz : Fx
  /-- body x axis as (horizontal, up) unit vector: (cos theta, sin theta) -/
  dx : Fx
  dz : Fx
  /-- pitch rate, rad/s -/
  q : Fx
  /-- engine (= propeller) rpm -/
  rpm : Fx
  /-- manifold pressure after its first-order lag, kPa -/
  tmap : Fx
  /-- body-axis acceleration of the last step; feeds alpha-dot of the next step -/
  udot : Fx
  wdot : Fx
  /-- stall hysteresis bit as 0 or 1 -/
  stall : Fx
  /-- derivatives from the last step: world horizontal/up acceleration and pitch acceleration -/
  ah : Fx
  au : Fx
  qd : Fx
  /-- world acceleration one step earlier (Adams-Bashforth 2) -/
  ah1 : Fx
  au1 : Fx
  /-- climb rate one and two steps earlier (Adams-Bashforth 3 for altitude) -/
  pvz : Fx
  pvz2 : Fx
  deriving Inhabited, Repr

/-- Elevator in our convention (+1 nose up, JSBSim command = -elev) and throttle in [0, 1].
`beta` and `phi` are optional lateral disturbances (sideslip and bank, rad); 0 is wings level and coordinated. -/
structure Input where
  elev : Fx
  thr : Fx
  beta : Fx := 0
  phi : Fx := 0
  deriving Inhabited, Repr

/-- `1 - x^2/2 + x^4/24`, accurate for |x| < 1. -/
def cosSmall (x : Fx) : Fx := let x2 := x * x; 1 - x2 / 2 + (x2 * x2) / 24

/-- `x - x^3/6 + x^5/120`, accurate for |x| < 1. -/
def sinSmall (x : Fx) : Fx := let x2 := x * x; x - (x * x2) / 6 + (x * x2 * x2) / 120

/-- Mixture position fixed as in `sysid/collect.py`. -/
def mixPos : Fx := (⟨58982⟩ : Fx)

/-- Intermediate quantities of one evaluation, for comparison with JSBSim's own properties. -/
structure Probe where
  rho : Fx
  alpha : Fx
  adot : Fx
  qbar : Fx
  fxA : Fx
  fzA : Fx
  mA : Fx
  fxP : Fx
  mP : Fx
  hp : Fx
  vind : Fx
  thrustKN : Fx
  cl : Fx
  cd : Fx
  tipMach : Fx
  ct : Fx
  adv : Fx
  deriving Inhabited, Repr

/-- `a / 2^k` rounded to nearest. -/
def shr (a : Fx) (k : Nat) : Fx := ⟨(a.raw + (1 <<< (k - 1))) >>> k⟩

def iter (n : Nat) (f : State → State) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 => iter n f (f s)

/-- Linear interpolation in a 50 m spaced raw table starting at 0 m; clamped. -/
def atmLookup (tab : Array Int) (h : Fx) : Fx :=
  let span : Int := 50 * 65536
  let i := (floorDiv (max 0 (min (span * 159) h.raw)) span).toNat
  let f := max 0 (min span (h.raw - i * span))
  ⟨tab[i]! + (floorDiv64 (Int64.ofInt (tab[i + 1]! - tab[i]!) * Int64.ofInt f) (Int64.ofInt span)).toInt⟩

/-- JSBSim FGPropagate: Adams-Bashforth 3 altitude, Adams-Bashforth 2 velocity, rectangular Euler attitude/rate. -/
def integrate (k : Nat) (ab : Bool) (s : State) : State :=
  let h' := if ab then s.h + shr ⟨(23 * s.vz.raw - 16 * s.pvz.raw + 5 * s.pvz2.raw) / 12⟩ k else s.h + shr s.vz k
  let vx' := if ab then s.vx + shr (3 * s.ah - s.ah1) (k + 1) else s.vx + shr s.ah k
  let vz' := if ab then s.vz + shr (3 * s.au - s.au1) (k + 1) else s.vz + shr s.au k
  let d := shr s.q k
  let c := s.dx - mulR s.dz d
  let sn := s.dz + mulR s.dx d
  let n := (3 : Fx) / 2 - (c * c + sn * sn) / 2
  { s with x := s.x + shr vx' k, h := h', vx := vx', vz := vz', q := s.q + shr s.qd k,
           dx := mulR c n, dz := mulR sn n, ah1 := s.ah, au1 := s.au, pvz := s.vz, pvz2 := s.pvz }

/-- Everything JSBSim computes after propagation: forces, moments, engine, derivatives. -/
def evaluate (k : Nat) (inp : Input) (s : State) : State × Probe :=
  let rho := atmLookup atmRho s.h
  let pAmb := atmLookup atmP s.h
  let tK := atmLookup atmT s.h
  let aSnd := atmLookup atmA s.h
  let cphi := cosSmall inp.phi
  let sphi := sinSmall inp.phi
  let cbeta := cosSmall inp.beta
  -- body velocity: with bank and sideslip the lateral component b of the horizontal speed follows from beta
  let w0 := s.vx * s.dz - s.vz * s.dx
  let b : Fx := if inp.beta.raw == 0 && inp.phi.raw == 0 then 0
                else (sqrtFx (s.vx * s.vx + s.vz * s.vz) * sinSmall inp.beta - sphi * w0) / cphi
  let a := s.vx - (b * b) / (s.vx + s.vx)
  let u := a * s.dx + s.vz * s.dz
  let w' := a * s.dz - s.vz * s.dx
  let w := cphi * w' - sphi * b
  let vb := cphi * b + sphi * w'
  let mUW := u * u + w * w
  let vt := sqrtFx mUW
  let vtot := sqrtFx (mUW + vb * vb)
  let alpha := atan2Fx w u
  let adot : Fx := if mUW.raw > 66 then (u * s.wdot - w * s.udot) / mUW else 0
  let qbar := (rho * (mUW + vb * vb)) / 2000
  let mach := vtot / aSnd
  let ci2vel := wingChord / (vtot + vtot)
  -- flight control: pitch trim sum clipped to [-1, 1], then asymmetric travel
  let cmd := max (-1) (min 1 (-inp.elev))
  let elevDeg := if cmd.raw ≥ 0 then cmd * elevTravelDown else cmd * elevTravelUp
  let elevRad := (elevDeg * 1745) / 100000
  let stall : Fx := if alphaHystHi < alpha then 1 else if alpha < alphaHystLo then 0 else s.stall
  -- piston engine (FGPiston)
  let y := (mach * mach) / 5
  let pTot := pAmb * (1 + y * ((⟨229376⟩ : Fx) + y * ((⟨286720⟩ : Fx) + y * ((⟨71680⟩ : Fx) + y * (⟨17918⟩ : Fx)))))
  let zt := (1 - inp.thr) * (1 - inp.thr) * engZThrottle
  let ze : Fx := if s.rpm.raw > 6554 then engZeNum / s.rpm else 999999
  let coef := ze / (ze + engZAirbox + zt)
  let tmap := s.tmap - shr (s.tmap - pTot * coef) k
  let pmep := (tmap - pAmb) * engVolEff
  let mratio := if tmap.raw > 0 then min engCompRatio (pAmb / tmap) else engCompRatio
  let ve : Fx := (⟨15124⟩ : Fx) + (engCompRatio - mratio) / (⟨638976⟩ : Fx)
  let mpsM := ((s.rpm * engStrokeIn) / 360) * (⟨19975⟩ : Fx)
  let vdotL := ((engDispL * s.rpm) / 120) * engVolEff * ve
  let mdotAir := vdotL * ((tmap * (⟨228110⟩ : Fx)) / tK)
  let fa := ((⟨85197⟩ : Fx) * mixPos * (⟨6640435⟩ : Fx) / pAmb) / (⟨963379⟩ : Fx)
  let me := tblMixEff.eval fa
  let ihp : Fx := if s.rpm.raw ≥ 28836 then (((mdotAir * fa) * (⟨520130⟩ : Fx)) / engIsfc) * me - engStaticFriction
                  else 0 - engStaticFriction
  let fmep := 0 - (engFmepDynamic * mpsM + engFmepStatic)
  let hp := ihp + (((pmep + fmep) * engDispL) * (s.rpm / 1000)) / (⟨5864423⟩ : Fx)
  let powKW := if s.rpm.raw ≤ 6554 then max 0 (hp * (⟨48870⟩ : Fx)) else hp * (⟨48870⟩ : Fx)
  -- fixed-pitch propeller (FGPropeller)
  let rps := s.rpm / 60
  let vel := u + s.q * thrusterBodyZ
  let mt := (rps * propDiameter * (⟨205887⟩ : Fx)) / aSnd
  let mv := vel / aSnd
  let tipM := sqrtFx (mt * mt + mv * mv)
  let adv : Fx := if rps.raw > 655 then vel / (propDiameter * rps) else vel / propDiameter
  let ct := tblCT.eval adv * tblCTMach.eval tipM
  let cp := tblCP.eval adv * tblCPMach.eval tipM
  let thrust := ((((ct * propD4) * rho) * rps) * rps) / 1000
  let powReq := ((((cp * propD5) * rho) * rps) * rps / 1000) * rps
  let pav := powKW - powReq
  let rps' := rps + shr ((pav / (if rps.raw > 655 then rps else 1)) * (⟨733217⟩ : Fx)) k
  let rpm' := max 0 (rps' * 60)
  let v2 := vel * Fx.abs vel + (2000 * thrust) / (rho * propArea)
  let vind := if 0 < v2.raw then (sqrtFx v2 - vel) / 2 else (0 - vel - sqrtFx (0 - v2)) / 2
  -- aerodynamics (generated functions)
  let e : AeroIn := { adot := adot, alpha := alpha, ci2vel := ci2vel, elevRad := elevRad, flapDeg := 0,
                      hbMac := (s.h + rpBodyX * s.dz - rpBodyZ * s.dx) / wingSpan, magBeta := Fx.abs inp.beta,
                      magElevRad := Fx.abs elevRad, qAero := s.q, qbar := qbar, rho := rho,
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

def step (k : Nat) (ab : Bool) (inp : Input) (s : State) : State :=
  (evaluate k inp (integrate k ab s)).1

/-- One 1/16 s tick as JSBSim runs it: 8 steps of 1/128 s, Adams-Bashforth histories carried in the state. -/
def tickAB (inp : Input) (s : State) : State := iter 8 (step 7 true inp) s

/-- One 1/16 s tick as 4 forward-Euler steps of 1/64 s (no history used). -/
def tickEuler (inp : Input) (s : State) : State := iter 4 (step 6 false inp) s

/-- Quantities JSBSim logs for a state, recomputed by the model for that state (diagnostics only). -/
def probe (inp : Input) (s : State) : State × Probe := evaluate 7 inp s

end Jsb
