import JsbExact.LinAlg
import JsbExact.C172Gen

/-! One `FGFDMExec::Run` of JSBSim 1.3.3's c172p, in JSBSim's model order and units (ft, slug, lbf). -/

namespace JsbExact
open S

variable {α : Type} [Scalar α]

@[inline] def v3 (a : Array Float) (i : Nat := 0) : V3 α := ⟨lit a[i]!, lit a[i+1]!, lit a[i+2]!⟩
@[inline] def m9 (a : Array Float) (i : Nat := 0) : M33 α :=
  M33.mk' (lit a[i]!) (lit a[i+1]!) (lit a[i+2]!) (lit a[i+3]!) (lit a[i+4]!) (lit a[i+5]!)
    (lit a[i+6]!) (lit a[i+7]!) (lit a[i+8]!)

/-- `FGLGear` values carried between steps; `lm` are the roll, side and dynamic friction multipliers. -/
structure GearState (α : Type) where
  wow : Bool
  lm0 : α
  lm1 : α
  lm2 : α
  slip : α
  steer : α
  act : V3 α
  mT : M33 α
  deriving Inhabited

structure State (α : Type) [Scalar α] where
  q : Quat α
  qdot : Quat α
  pqri : V3 α
  ri : V3 α
  vi : V3 α
  vih0 : V3 α
  vih1 : V3 α
  aih0 : V3 α
  epa : α
  pqridot : V3 α
  uvwidot : V3 α
  uvwdot : V3 α
  stall : α
  cg : V3 α
  tank0 : α
  tank1 : α
  tmap : α
  running : Scalar.Cond α
  fuelflow : α
  starved : Scalar.Cond α
  rpm : α
  act : V3 α
  lastcg : V3 α
  gears : Array (GearState α)
  wind : V3 α
  deriving Inhabited

structure Input (α : Type) where
  elev : α
  ail : α
  rud : α
  thr : α
  mix : α
  brkL : α
  brkR : α
  deriving Inhabited

structure Diag (α : Type) where
  uvw : V3 α
  pqr : V3 α
  loc : V3 α
  euler : V3 α
  hsl : α
  agl : α
  vned : V3 α
  alpha : α
  beta : α
  adot : α
  qbar : α
  vt : α
  mach : α
  pt : α
  hmac : α
  rho : α
  p : α
  t : α
  a : α
  grav : V3 α
  fnat : V3 α
  mmrc : V3 α
  faero : V3 α
  maero : V3 α
  fprop : V3 α
  mprop : V3 α
  ftot : V3 α
  mtot : V3 α
  thrust : α
  hp : α
  mass : α
  de : α
  da : α
  dr : α
  fgear : V3 α
  mgear : V3 α
  ffric : V3 α
  gearFz : Array α

/-! ### FGLocation -/

structure Loc (α : Type) where
  radius : α
  lat : α
  lon : α
  geodLat : α
  geodAlt : α
  tec2l : M33 α

/-- `FGLocation::ComputeDerivedUnconditional` with the ellipse set (Fukushima's geodetic latitude). -/
def locDerive (r : V3 α) : Loc α :=
  let a : α := lit Gen.a
  let ec := lit Gen.b / a
  let ec2 := ec * ec
  let e2 := one - ec2
  let c := a * e2
  let radius := r.mag
  let rxy := sqrt (mac r.x r.x (r.y * r.y))
  let (sinLon, cosLon, lon) :=
    sif eq rxy zero then (zero, one, zero) else (r.y / rxy, r.x / rxy, atan2 r.y r.x)
  let (lat, gLat, gAlt, sinLat, cosLat) :=
    sif eq radius zero then (zero, zero, -a, zero, one) else
    let lat := atan2 r.z rxy
    let s0 := abs r.z
    let zc := ec * s0
    let c0 := ec * rxy
    let c02 := c0 * c0
    let s02 := s0 * s0
    let a02 := c02 + s02
    let a0 := sqrt a02
    let a03 := a02 * a0
    let s1 := mac zc a03 (c * s02 * s0)
    let c1 := msc rxy a03 (c * c02 * c0)
    let cs0c0 := c * c0 * s0
    let b0 := lit 1.5 * cs0c0 * msc (msc rxy s0 (zc * c0)) a0 cs0c0
    let s1 := msc s1 a03 (b0 * s0)
    let cc := ec * msc c1 a03 (b0 * c0)
    let gLat := sign r.z * atan (s1 / cc)
    let s12 := s1 * s1
    let cc2 := cc * cc
    let norm := sqrt (s12 + cc2)
    let gAlt := nmac a (sqrt (mac ec2 s12 cc2)) (mac rxy cc (s0 * s1)) / norm
    (lat, gLat, gAlt, sign r.z * s1 / norm, cc / norm)
  { radius, lat, lon, geodLat := gLat, geodAlt := gAlt,
    tec2l := M33.mk' (-cosLon * sinLat) (-sinLon * sinLat) cosLat (-sinLon) cosLon zero
               (-cosLon * cosLat) (-sinLon * cosLat) (-sinLat) }

/-- `FGLocation::GetSeaLevelRadius` (geocentric latitude). -/
def seaLevelRadius (l : Loc α) : α :=
  let a : α := lit Gen.a
  let ec := lit Gen.b / a
  let e2 := one - ec * ec
  let cl := cos l.lat
  a * ec / sqrt (nmac (e2 * cl) cl one)

/-! ### FGInertial, FGStandardAtmosphere -/

/-- `FGInertial::GetGravityJ2`. -/
def gravityJ2 (r : V3 α) (l : Loc α) : V3 α :=
  let rad := l.radius
  let sinLat := sin l.lat
  let adivr := lit Gen.a / rad
  let pre := lit 1.5 * lit Gen.J2 * adivr * adivr
  let xy := nmac (lit 5.0) (sinLat * sinLat) one
  let z := nmac (lit 5.0) (sinLat * sinLat) (lit 3.0)
  let g := lit Gen.GM / (rad * rad)
  ⟨-g * (mac pre xy one * r.x / rad), -g * (mac pre xy one * r.y / rad), -g * (mac pre z one * r.z / rad)⟩

@[inline] def geopot (h : α) : α := h * lit Gen.EarthRadius / (lit Gen.EarthRadius + h)
@[inline] def geomet (h : α) : α := h * lit Gen.EarthRadius / (lit Gen.EarthRadius - h)

def stdTemperature (alt : α) : α :=
  let gpa := geopot alt
  let fade : α := lit Gen.fadeAlt
  let tg : α := lit Gen.tgrad
  let t := sif ge gpa zero then
      let t := Gen.tab_stdTemp.get1 gpa
      sif le gpa fade then nmac tg gpa t else t
    else mac gpa (lit Gen.lapse[0]!) (Gen.tab_stdTemp.get1 (zero : α))
  let t := t + lit Gen.tbias
  sif le gpa fade then mac tg fade t else t

/-- Lapse rate, base pressure and base altitude of the layer `FGStandardAtmosphere::GetPressure` finds. -/
def pressLayer (gpa : α) (b : Nat) (base : α) : (fuel : Nat) → α × α × α
  | 0 => layer b base
  | fuel + 1 =>
    if b < Gen.tab_stdTemp.rows - 2 then
      let test : α := lit Gen.tab_stdTemp.data[2 * (b + 2)]!
      sif lt gpa test then layer b base else pressLayer gpa (b + 1) test fuel
    else layer b base
where
  layer (b : Nat) (base : α) : α × α × α := (lit Gen.lapse[b]!, lit Gen.pressBreak[b]!, base)

def stdPressure (alt : α) : α :=
  let gpa := geopot alt
  let (lmb, pb, base) := pressLayer gpa 0 (lit Gen.tab_stdTemp.data[2]!) Gen.tab_stdTemp.rows
  let tmb := stdTemperature (geomet base)
  let dh := gpa - base
  let g0 : α := lit Gen.g0
  let rdry : α := lit Gen.Rdry
  sif ne lmb zero then pb * pow (tmb / mac lmb dh tmb) (g0 / (rdry * lmb))
  else pb * exp (-g0 * dh / (rdry * tmb))

structure Atmo (α : Type) where
  t : α
  p : α
  rho : α
  a : α

/-- `FGAtmosphere::Calculate`. -/
def atmosphere (alt : α) : Atmo α :=
  let t := stdTemperature alt
  let p := stdPressure alt
  let t := S.ite (lt t (lit 1.8)) (lit 1.8) t
  let pmin : α := lit (1e-15 * 0.0208854342)
  let p := S.ite (lt p pmin) pmin p
  let reng : α := lit Gen.Reng
  { t, p, rho := p / (reng * t), a := sqrt (lit Gen.SHRatio * reng * t) }

/-- `FGAuxiliary::PitotTotalPressure`. -/
def pitot (mach p : α) : α :=
  let sh : α := lit Gen.SHRatio
  let a := (sh - one) / lit 2.0
  let b := sh / (sh - one)
  let c := lit 2.0 * b
  let d := one / (sh - one)
  sif lt mach zero then p
  else sif lt mach one then p * pow (mac (a * mach) mach one) b
  else
    let coeff := pow (lit 0.5 * (sh + one)) b * pow ((sh + one) / (sh - one)) d
    p * coeff * pow mach c / pow (msc (c * mach) mach one) d

/-! ### FCS -/

/-- `FGSummer` (inputs: command, zero trim; zero bias) followed by its `clipto`. -/
@[inline] def trimSum (cmd : α) (lo hi : Float) : α := constrain (lit lo) (zero + cmd + zero + zero) (lit hi)

/-- Zero-centred `aerosurface_scale` (`FGGain`). -/
@[inline] def surfScale (x : α) (inMin inMax outMin outMax gain : Float) : α :=
  let o := sif eq x zero then zero else sif gt x zero then x / lit inMax * lit outMax else x / lit inMin * lit outMin
  o * lit gain

/-! ### FGMassBalance -/

@[inline] def structToBody (cg r : V3 α) : V3 α :=
  let k : α := lit Gen.inchtoft
  ⟨k * (cg.x - r.x), k * (r.y - cg.y), k * (cg.z - r.z)⟩

/-- `FGMassBalance::GetPointmassInertia` about `cg`. -/
def pmInertia (cg : V3 α) (m : α) (r : V3 α) : M33 α :=
  let v := structToBody cg r
  let sv := V3.smul m v
  let xx := sv.x * v.x
  let yy := sv.y * v.y
  let zz := sv.z * v.z
  let xy := -sv.x * v.y
  let xz := -sv.x * v.z
  let yz := -sv.y * v.z
  M33.mk' (yy + zz) xy xz xy (xx + zz) yz xz yz (xx + yy)

@[inline] def tankCfg (i : Nat) : Array Float := if i == 0 then Gen.tank0 else Gen.tank1

/-- `FGTank::GetXYZ`. -/
@[inline] def tankXYZ (i : Nat) (contents : α) : V3 α :=
  let t := tankCfg i
  let drain : V3 α := v3 t 3
  V3.add drain (V3.smul (contents / lit t[6]!) (V3.sub (v3 t 0) drain))

/-- `FGTank::Drain`. -/
@[inline] def tankDrain (i : Nat) (c used : α) : α :=
  let unusable : α := lit (tankCfg i)[7]!
  sif ge (c - used) unusable then c - used else S.ite (gt c unusable) unusable c

structure Mass (α : Type) where
  mass : α
  cg : V3 α
  j : M33 α
  jinv : M33 α

def massBalance (prevCg : V3 α) (t0 t1 : α) : Mass α :=
  let lbtoslug : α := lit Gen.lbtoslug
  let tanksWeight := zero + t0 + t1
  let tanksMoment := V3.add (V3.add V3.zero (V3.smul t0 (tankXYZ 0 t0))) (V3.smul t1 (tankXYZ 1 t1))
  let tankJ1 := M33.add M33.zero (pmInertia prevCg (lbtoslug * t0) (tankXYZ 0 t0))
  let c0 := tankCfg 0
  let tankJ1 := { tankJ1 with a11 := tankJ1.a11 + lit c0[8]!, a22 := tankJ1.a22 + lit c0[9]!, a33 := tankJ1.a33 + lit c0[10]! }
  let tankJ2 := M33.add tankJ1 (pmInertia prevCg (lbtoslug * t1) (tankXYZ 1 t1))
  let c1 := tankCfg 1
  let tankJ := { tankJ2 with a11 := tankJ2.a11 + lit c1[8]!, a22 := tankJ2.a22 + lit c1[9]!, a33 := tankJ2.a33 + lit c1[10]! }
  let npm := Gen.pmWeight.size
  let pmw := (List.range npm).foldl (fun acc i => acc + lit Gen.pmWeight[i]!) (zero : α)
  let ew : α := lit Gen.emptywt
  let weight := mac zero (lit Gen.slugtolb) (ew + tanksWeight + pmw) + zero
  let mass := lbtoslug * weight
  let pmMoment := (List.range npm).foldl (fun acc i => V3.add acc (V3.smul (lit Gen.pmWeight[i]!) (v3 Gen.pmLoc (3 * i)))) V3.zero
  let base : V3 α := v3 Gen.baseCG
  let cg := V3.sdiv (V3.add (V3.add (V3.add (V3.smul ew base) pmMoment) tanksMoment) V3.zero) weight
  let pmJ := (List.range npm).foldl (fun acc i =>
    M33.add (M33.add acc (pmInertia cg (lbtoslug * lit Gen.pmWeight[i]!) (v3 Gen.pmLoc (3 * i)))) (m9 Gen.pmJ (9 * i))) M33.zero
  let j := M33.add (M33.add (M33.add (M33.add (m9 Gen.baseJ) (pmInertia cg (lbtoslug * ew) base)) pmJ) tankJ) M33.zero
  let ixx := j.a11
  let iyy := j.a22
  let izz := j.a33
  let ixy := -j.a12
  let ixz := -j.a13
  let iyz := -j.a23
  let k1 := msc iyy izz (iyz * iyz)
  let k2 := mac iyz ixz (ixy * izz)
  let k3 := mac ixy iyz (iyy * ixz)
  let denom := one / nmac ixz k3 (msc ixx k1 (ixy * k2))
  let k1 := k1 * denom
  let k2 := k2 * denom
  let k3 := k3 * denom
  let k4 := msc izz ixx (ixz * ixz) * denom
  let k5 := mac ixy ixz (iyz * ixx) * denom
  let k6 := msc ixx iyy (ixy * ixy) * denom
  { mass, cg, j, jinv := M33.mk' k1 k2 k3 k2 k4 k5 k3 k5 k6 }

/-! ### FGPiston and FGPropeller -/

structure EngineOut (α : Type) [Scalar α] where
  tmap : α
  running : Scalar.Cond α
  fuelflow : α
  hp : α
  power : α
  mdotAir : α

/-- `FGPiston::Calculate` up to the thruster call (unboosted, magnetos both, starter off). -/
def piston (pressure totalPressure temperature thr mix rpm tmap0 fuelflow0 dt : α) (running0 starved : Scalar.Cond α) :
    EngineOut α :=
  let psftopa : α := lit Gen.psftopa
  let pAmb := pressure * psftopa
  let p := totalPressure * psftopa
  let pRam := mac (p - pAmb) (lit Gen.RamAir) pAmb
  let tAmb := temperature / lit 1.8
  let mps := rpm * lit Gen.Stroke / lit 360.0
  let idle : α := lit Gen.IdleRPM
  let spark := Gen.Magnetos != 0.0
  let fuel := gt fuelflow0 zero
  let running := cand (cand (cbool spark) fuel)
    (cor (cand running0 (cnot (lt rpm (idle * lit 0.8)))) (cand (cnot running0) (gt rpm (idle * lit 0.8))))
  let zt := (one - thr) * (one - thr) * lit Gen.Z_throttle
  let ze := sif gt mps zero then lit Gen.PeakMPS / mps else lit 999999.0
  let coef := ze / (ze + lit Gen.Z_airbox + zt)
  let dmap := nmac pRam coef tmap0
  let lag : α := lit Gen.MPLag
  let dmap := sif gt lag dt then dmap * (dt / lag) else dmap
  let tmap := tmap0 - dmap
  let ve : α := lit Gen.VE
  let pmep := (tmap - pAmb) * ve
  let map := tmap
  let cr : α := lit Gen.CompressionRatio
  let gamma : α := lit 1.3
  let mratio := sif lt map one then cr else pAmb / map
  let mratio := S.ite (gt mratio cr) cr mratio
  let veff := (gamma - one) / gamma + (cr - mratio) / (gamma * (cr - one))
  let rAir : α := lit Gen.R_air
  let swept := lit Gen.dispSI * (rpm / lit 60.0) / lit 2.0
  let vdot := swept * (ve * veff)
  let mdotAir := vdot * (map / (rAir * tAmb))
  let thi := lit 1.3 * mix
  let equiv := thi * lit 101325.0 / pAmb
  let mdotFuel := mdotAir * equiv / lit 14.7
  let ffr := mdotFuel * lit 2.2046
  let (mdotFuel, ffr) := sif starved then (zero, zero) else (mdotFuel, ffr)
  let pph := ffr * lit 3600.0
  let sf : α := lit Gen.SFHP
  let (ihp, fmep) := sif running then
      let me := Gen.tab_mixEff.get1 (mdotFuel / mdotAir)
      let fmep := msc (-(lit Gen.FMEPDynamic) * mps) (lit Gen.fttom) (lit Gen.FMEPStatic)
      let power : α := if Gen.Magnetos != 3.0 then one * lit Gen.SparkFailDrop else one
      (msc (pph / lit Gen.ISFC * me) power sf, fmep)
    else (-sf, zero)
  let pumping := (pmep + fmep) * lit Gen.dispSI * rpm / (lit Gen.Cycles * lit 22371.0)
  let hp := ihp + pumping - zero
  let running := cand running (cnot (lt ihp (lit 0.125)))
  let power := hp * lit Gen.hptoftlbssec
  let power := sif le rpm (lit 0.1) then max power zero else power
  { tmap, running, fuelflow := ffr, hp, power, mdotAir }

structure PropOut (α : Type) where
  thrust : α
  rpm : α
  act : V3 α
  vmn : V3 α
  vind : α

/-- `FGPropeller::Calculate` for a fixed-pitch propeller without RPM tables. -/
def propeller (cg act0 aeroUVW aeroPQR pqri : V3 α) (rho sound power rpm dt : α) : PropOut α :=
  let pi : α := lit 3.141592653589793
  let mT : M33 α := m9 Gen.propT
  let loc : V3 α := v3 Gen.propXYZ
  let dxyz := structToBody cg loc
  let lv := mT.T.mulV (V3.add aeroUVW (V3.cross aeroPQR dxyz))
  let vel := lv.x
  let rps := rpm / lit 60.0
  let dia : α := lit Gen.Diameter
  let area := lit 0.25 * dia * dia * pi
  let vtip := rps * dia * pi
  let tipMach := sqrt (mac vtip vtip (vel * vel)) / sound
  let j := sif gt rps (lit 0.01) then vel / (dia * rps) else vel / dia
  let cpReq := Gen.tab_cPower.get1 j * lit Gen.CpFactor * Gen.tab_CpMach.get1 tipMach
  let lrps := S.ite (lt rps (lit 0.01)) (lit 0.01) rps
  let powerReq := cpReq * lrps * lrps * lrps * lit Gen.D5 * rho
  let pAvail := power - powerReq
  let ct := Gen.tab_cThrust.get1 j * lit Gen.CtFactor * Gen.tab_CtMach.get1 tipMach
  let thrust := ct * rps * rps * lit Gen.D4 * rho
  let v2 := mac vel (abs vel) (lit 2.0 * thrust / (rho * area))
  let vind := sif gt v2 zero then lit 0.5 * (-vel + sqrt v2) else lit 0.5 * (-vel - sqrt (-v2))
  let sense : α := lit Gen.Sense
  let act := if Gen.PFactor > 0.0001 then
      let tv := lv.magYZ
      sif gt tv (lit 0.0001) then
        let angle := atan2 tv (vel + vind)
        let factor := sense * lit Gen.PFactor * angle / tv
        { act0 with y := mac factor lv.z loc.y, z := mac factor lv.y loc.z }
      else act0
    else act0
  let omega := rps * lit 2.0 * pi
  let torque : V3 α := ⟨-sense * power / max (lit 0.01) omega, zero, zero⟩
  let ixx : α := lit Gen.propIxx
  let vh : V3 α := ⟨ixx * omega * sense * lit Gen.SenseMult, zero, zero⟩
  let excess := sif gt omega (lit 0.01) then pAvail / omega else pAvail / one
  let rpm' := mac (excess / ixx / (lit 2.0 * pi)) dt rps * lit 60.0
  let rpm' := S.ite (lt rpm' zero) zero rpm'
  { thrust, rpm := rpm', act, vmn := V3.add (V3.cross pqri (mT.mulV vh)) (mT.mulV torque), vind }


/-! ### FGLGear, FGGroundReactions and the friction solver of FGAccelerations -/

structure Mult (α : Type) where
  fj : V3 α
  lever : V3 α
  min : α
  max : α
  value : α
  gear : Nat
  slot : Nat
  deriving Inhabited

/-- `gear` and `slot` are taken from the first argument: both sides of a join have the same constraint list. -/
instance : Join α (Mult α) := ⟨fun a b =>
  { a with fj := V3.join a.fj b.fj, lever := V3.join a.lever b.lever, min := Scalar.join a.min b.min,
           max := Scalar.join a.max b.max, value := Scalar.join a.value b.value }⟩

structure GearCtx (α : Type) where
  cg : V3 α
  tb2l : M33 α
  tec2l : M33 α
  tec2b : M33 α
  loc : V3 α
  locTl2ec : M33 α
  pqr : V3 α
  uvw : V3 α
  dt : α
  brkL : α
  brkR : α

/-- `FGLGear::GetBodyForces` (fixed or steerable, non-retractable, no strut function or cornering table). -/
def gearForces (gi : Nat) (c : GearCtx α) (g : GearState α) : GearState α × V3 α × V3 α × Array (Mult α) × α :=
  let cfg := Gen.gears[gi]!
  let bogey := cfg[0]! == 0.0
  let xyz : V3 α := v3 cfg 1
  let mTGear : M33 α := m9 cfg 22
  let ts2b : M33 α := m9 Gen.Ts2b
  let whlBody := ts2b.mulV (V3.sub xyz c.cg)
  let localGear := c.tb2l.mulV whlBody
  let gearLoc := V3.add (c.locTl2ec.mulV localGear) c.loc
  let gl := locDerive gearLoc
  let lat := gl.geodLat
  let cosLat := cosS lat
  let normal : V3 α := ⟨cosLat * cosS gl.lon, cosLat * sinS gl.lon, sinS lat⟩
  let height := gl.geodAlt - lit Gen.terrain
  let height := height - zero
  let sFF : α := lit Gen.staticFFactor
  let rFF : α := lit Gen.rollingFFactor
  let groundNormal := c.tec2b.mulV normal
  let normalZ := (c.tec2l.mulV normal).z
  let lgearProj := -(mTGear.T.mulV groundNormal).z
  let (wow, compress, displ) :=
    if mode (lt height zero) then
      if bogey then
        if Gen.isSolid != 0.0 then
          let cl := sif gt lgearProj zero then height * normalZ / lgearProj else zero
          (true, cl, mTGear.mulV ⟨zero, zero, -cl⟩)
        else (false, zero, V3.zero)
      else
        let cl := height * normalZ / V3.dot normal normal
        (true, cl, V3.smul cl groundNormal)
    else (false, zero, V3.zero)
  if wow then
    let contact := V3.add whlBody displ
    let act := V3.add xyz ((m9 Gen.Tb2s : M33 α).mulV displ)
    let bodyWhlVel := V3.add (V3.cross c.pqr contact) (V3.sub c.uvw (c.tec2b.mulV V3.zero))
    let roll := mTGear.mulV ⟨cosS g.steer, sinS g.steer, zero⟩
    let side := V3.cross groundNormal roll
    let roll := V3.sub roll (V3.smul (V3.dot roll groundNormal) groundNormal)
    let normz (v : V3 α) : V3 α := let m := v.mag; sif ne m zero then V3.smul (one / m) v else v
    let roll := normz roll
    let side := normz side
    let mT := M33.mk' roll.x side.x groundNormal.x roll.y side.y groundNormal.y roll.z side.z groundNormal.z
    let gwv := mT.T.mulV bodyWhlVel
    let cspeed := sif eq c.dt zero then zero else
      let cs := -gwv.z
      let cs := if bogey then cs / lgearProj else cs
      let maxcs := compress / c.dt
      sif gt (abs cs) maxcs then sign cs * maxcs else cs
    let kS : α := lit cfg[4]!
    let spring := -compress * kS
    let damp :=
      sif ge cspeed zero then
        if cfg[7]! == 0.0 then -cspeed * lit cfg[5]! else -cspeed * cspeed * lit cfg[5]!
      else
        if cfg[8]! == 0.0 then -cspeed * lit cfg[6]! else cspeed * cspeed * lit cfg[6]!
    let strut := min (spring + damp) zero
    let strut := S.ite (gt strut (lit Gen.maximumForce)) (lit Gen.maximumForce) strut
    let fz := if bogey then strut / (mTGear.T.mulV groundNormal).z else -strut
    let magXY := sqrt (mac gwv.x gwv.x (gwv.y * gwv.y))
    let slip := if bogey then sif gt magXY (lit 1e-3) then -atan2 gwv.y (abs gwv.x) * lit Gen.radtodeg else g.slip
      else g.slip
    let sFC : α := lit cfg[9]!
    let rFC : α := lit cfg[11]!
    let grp := cfg[14]!
    let brake : α := if grp == 1.0 then c.brkL else if grp == 2.0 then c.brkR else zero
    let brakeF := if grp == 0.0 then rFF * rFC else mac (brake * sFF) (sFC - rFC) (rFF * rFC)
    let stiff := lit cfg[16]! * slip
    let fcoeff := lit cfg[18]! * sin (lit cfg[17]! * atan (nmac (lit cfg[19]!) (stiff - atan stiff) stiff)) * sFF
    let (g', mults) :=
      if !bogey && mode (gt magXY (lit 1e-3)) then
        let vd : V3 α := { gwv with z := zero }
        let vd := normz vd
        let mn := -abs (sFF * lit cfg[10]! * fz)
        let m : Mult α := { fj := mT.mulV vd, lever := contact, min := mn, max := zero,
                            value := constrain mn g.lm2 zero, gear := gi, slot := 2 }
        ({ g with lm2 := m.value }, #[m])
      else
        let mx0 := if bogey then abs (brakeF * fz) else abs (sFF * sFC * fz)
        let mx1 := if bogey then abs (fcoeff * fz) else mx0
        let m0 : Mult α := { fj := mT.mulV ⟨one, zero, zero⟩, lever := contact, min := -mx0, max := mx0,
                             value := constrain (-mx0) g.lm0 mx0, gear := gi, slot := 0 }
        let m1 : Mult α := { fj := mT.mulV ⟨zero, one, zero⟩, lever := contact, min := -mx1, max := mx1,
                             value := constrain (-mx1) g.lm1 mx1, gear := gi, slot := 1 }
        ({ g with lm0 := m0.value, lm1 := m1.value }, #[m0, m1])
    let fb := mT.mulV ⟨zero, zero, fz⟩
    let mom := V3.add V3.zero (V3.cross (structToBody c.cg act) fb)
    ({ g' with wow := true, slip, act, mT }, fb, mom, mults, fz)
  else
    let steer := g.steer * (S.max (one - lit 0.8) zero / lit 0.2)
    let fb := g.mT.mulV V3.zero
    let mom := V3.add V3.zero (V3.cross (structToBody c.cg g.act) fb)
    ({ g with wow := false, lm0 := zero, lm1 := zero, lm2 := zero, slip := zero, steer }, fb, mom, #[], zero)

/-- Projected Gauss-Seidel sweeps of `CalculateFrictionForces`, at most `fuel` of them. -/
def frictionSweeps (a : Array α) (rhs : Array α) (n : Nat) (ms : Array (Mult α)) : (fuel : Nat) → Array (Mult α)
  | 0 => ms
  | fuel + 1 => Id.run do
    let mut ms := ms
    let mut norm : α := zero
    for i in [0:n] do
      let l0 := ms[i]!.value
      let mut dl := rhs[i]!
      for j in [0:n] do
        dl := nmac a[i * n + j]! ms[j]!.value dl
      let v := constrain ms[i]!.min (l0 + dl) ms[i]!.max
      ms := ms.modify i ({ · with value := v })
      norm := norm + abs (v - l0)
    pure (sif lt norm (lit 1e-5) then ms else frictionSweeps a rhs n ms fuel)

/-- `FGAccelerations::CalculateFrictionForces`: friction force and moment, and the solved multipliers. -/
def friction (ms : Array (Mult α)) (mass : α) (jinv : M33 α) (uvwdot pqrdot uvw pqr : V3 α) (tec2b : M33 α) (dt : α) :
    V3 α × V3 α × Array (Mult α) := Id.run do
  let n := ms.size
  if n == 0 then return (V3.zero, V3.zero, ms)
  let mut a : Array α := Array.replicate (n * n) zero
  for i in [0:n] do
    let u := ms[i]!.fj
    let r := ms[i]!.lever
    let v1 := V3.sdiv u mass
    let v2 := jinv.mulV (V3.cross r u)
    for j in [0:i] do
      a := a.set! (i * n + j) a[j * n + i]!
    for j in [i:n] do
      a := a.set! (i * n + j) (V3.dot ms[j]!.fj (V3.add v1 (V3.cross v2 ms[j]!.lever)))
  let vdot := sif gt dt zero then V3.add uvwdot (V3.sdiv (V3.sub uvw (tec2b.mulV V3.zero)) dt) else uvwdot
  let wdot := sif gt dt zero then V3.add pqrdot (V3.sdiv (V3.sub pqr (tec2b.mulV V3.zero)) dt) else pqrdot
  let mut rhs : Array α := Array.replicate n zero
  for i in [0:n] do
    let d := a[i * n + i]!
    rhs := rhs.set! i (-V3.dot ms[i]!.fj (V3.add vdot (V3.cross wdot ms[i]!.lever)) / d)
    for j in [0:n] do
      a := a.set! (i * n + j) (a[i * n + j]! / d)
  let ms := frictionSweeps a rhs n ms 50
  let mut ff : V3 α := V3.zero
  let mut fm : V3 α := V3.zero
  for m in ms do
    let f := V3.smul m.value m.fj
    ff := V3.add ff f
    fm := V3.add fm (V3.cross m.lever f)
  return (ff, fm, ms)

/-! ### The step -/

def step (s : State α) (u : Input α) : State α × Diag α :=
  let dt : α := lit Gen.dt
  let omega : V3 α := v3 Gen.omega
  -- FGPropagate
  let q := (s.q.add (s.qdot.smul dt)).normalize
  let pqri := V3.add s.pqri (V3.smul dt s.pqridot)
  let ab3 := V3.add (V3.sub (V3.smul (lit 23.0) s.vi) (V3.smul (lit 16.0) s.vih0)) (V3.smul (lit 5.0) s.vih1)
  let ri := V3.add s.ri (V3.smul (lit (1.0 / 12.0) * dt) ab3)
  let ab2 := V3.sub (V3.smul (lit 1.5) s.uvwidot) (V3.smul (lit 0.5) s.aih0)
  let vi := V3.add s.vi (V3.smul dt ab2)
  let epa := mac omega.z dt s.epa
  let ce := cosS epa
  let se := sinS epa
  let ti2ec := M33.mk' ce se zero (-se) ce zero zero zero one
  let tec2i := ti2ec.T
  let locv := ti2ec.mulV ri
  let loc := locDerive locv
  let tec2l := loc.tec2l
  let ti2l := tec2l.mul ti2ec
  let tl2i := ti2l.T
  let ti2b := q.toM
  let tb2i := ti2b.T
  let tl2b := ti2b.mul tl2i
  let tb2l := tl2b.T
  let tec2b := ti2b.mul tec2i
  let uvw := ti2b.mulV (V3.sub vi (V3.cross omega ri))
  let pqr := V3.sub pqri (ti2b.mulV omega)
  let qdot := q.qdot pqri
  let euler := tl2b.toQuat.toM.euler
  let vned := tb2l.mulV uvw
  -- FGInertial
  let grav := gravityJ2 locv loc
  -- FGAtmosphere
  let hsl0 := loc.radius - seaLevelRadius loc
  let atm := atmosphere hsl0
  -- FGFCS
  let de := surfScale (trimSum u.elev Gen.fcs_Pitch_Trim_Sum_min Gen.fcs_Pitch_Trim_Sum_max)
    Gen.fcs_fcs_elevator_pos_rad_inMin Gen.fcs_fcs_elevator_pos_rad_inMax Gen.fcs_fcs_elevator_pos_rad_outMin
    Gen.fcs_fcs_elevator_pos_rad_outMax Gen.fcs_fcs_elevator_pos_rad_gain
  let da := surfScale (trimSum u.ail Gen.fcs_Roll_Trim_Sum_min Gen.fcs_Roll_Trim_Sum_max)
    Gen.fcs_fcs_left_aileron_pos_rad_inMin Gen.fcs_fcs_left_aileron_pos_rad_inMax
    Gen.fcs_fcs_left_aileron_pos_rad_outMin Gen.fcs_fcs_left_aileron_pos_rad_outMax Gen.fcs_fcs_left_aileron_pos_rad_gain
  let dr := surfScale (trimSum u.rud Gen.fcs_Yaw_Trim_Sum_min Gen.fcs_Yaw_Trim_Sum_max)
    Gen.fcs_fcs_rudder_pos_rad_inMin Gen.fcs_fcs_rudder_pos_rad_inMax Gen.fcs_fcs_rudder_pos_rad_outMin
    Gen.fcs_fcs_rudder_pos_rad_outMax Gen.fcs_fcs_rudder_pos_rad_gain
  -- FGMassBalance (tank inertia uses the previous step's CG, as JSBSim loads it before MassBalance runs)
  let mb := massBalance s.cg s.tank0 s.tank1
  let dcg := V3.sub (structToBody mb.cg s.lastcg) (structToBody mb.cg mb.cg)
  let wow0 := s.gears.toList.zipIdx.any fun (g, i) => g.wow && Gen.gears[i]![0]! == 0.0
  let (ri, locv) := if wow0 then (V3.sub ri (tb2i.mulV dcg), V3.sub locv (tec2b.T.mulV dcg)) else (ri, locv)
  let locN := if wow0 then locDerive locv else loc
  let hsl := if wow0 then locN.radius - seaLevelRadius locN else hsl0
  -- FGAuxiliary
  let aeroPQR := V3.sub pqr V3.zero
  let totalWind := V3.add (V3.add (V3.add s.wind V3.zero) V3.zero) V3.zero
  let aeroUVW := V3.sub uvw (tl2b.mulV totalWind)
  let u2 := aeroUVW.x * aeroUVW.x
  let v2 := aeroUVW.y * aeroUVW.y
  let w2 := aeroUVW.z * aeroUVW.z
  let mUW := u2 + w2
  let vt2 := mUW + v2
  let vt := sqrt vt2
  let (alpha, beta, adot) :=
    sif gt vt (lit 0.001) then
      let beta := atan2 aeroUVW.y (sqrt mUW)
      sif ge mUW (lit 1e-6) then
        (atan2 aeroUVW.z aeroUVW.x, beta, msc aeroUVW.x s.uvwdot.z (aeroUVW.z * s.uvwdot.x) / mUW)
      else (zero, beta, zero)
    else (zero, zero, zero)
  let ca := cosS alpha
  let sa := sinS alpha
  let cb := cosS beta
  let sb := sinS beta
  let tw2b := M33.mk' (ca * cb) (-ca * sb) (-sa) sb cb zero (sa * cb) (-sa * sb) ca
  let qbar := lit 0.5 * atm.rho * vt2
  let mach := vt / atm.a
  let pt := pitot mach atm.p
  let agl := locN.geodAlt - lit Gen.terrain
  let rpBody := structToBody mb.cg (v3 Gen.XYZrp)
  let hmac := (agl - (tb2l.mulV rpBody).z) / lit Gen.bw
  -- FGPropulsion
  let eng := piston atm.p pt atm.t u.thr u.mix (s.rpm * lit Gen.GearRatio) s.tmap s.fuelflow dt s.running s.starved
  let pr := propeller mb.cg s.act aeroUVW aeroPQR pqri atm.rho atm.a eng.power s.rpm dt
  let unus0 : α := lit Gen.tank0[7]!
  let unus1 : α := lit Gen.tank1[7]!
  let has0 := gt s.tank0 unus0
  let has1 := gt s.tank1 unus1
  let starved := cnot (cor has0 has1)
  -- Divided by the number of feeding tanks; unused when none feeds.
  let perTank := sif cand has0 has1 then eng.fuelflow * dt / lit 2.0 else eng.fuelflow * dt / lit 1.0
  let tank0 := sif cand (cnot starved) has0 then tankDrain 0 s.tank0 perTank else s.tank0
  let tank1 := sif cand (cnot starved) has1 then tankDrain 1 s.tank1 perTank else s.tank1
  let fb := mT_fb pr.thrust
  let mprop := V3.add pr.vmn (V3.cross (structToBody mb.cg pr.act) fb)
  let fprop := V3.add V3.zero fb
  let mprop := V3.add V3.zero mprop
  -- FGAerodynamics
  let twovel := lit 2.0 * vt
  let (bi2vel, ci2vel) := sif ne twovel zero then (lit Gen.bw / twovel, lit Gen.cbar / twovel) else (zero, zero)
  let stall := sif gt alpha (lit Gen.hystmax) then one else S.ite (lt alpha (lit Gen.hystmin)) zero s.stall
  let ai : Gen.AeroIn α := {
    adot, ailL := da, alpha, beta, bi2vel, bw := lit Gen.bw, cbar := lit Gen.cbar, ci2vel, elev := de,
    flapDeg := zero, hbMac := hmac, magBeta := abs beta, magElev := abs de, pAero := aeroPQR.x,
    qAero := aeroPQR.y, qbar, rAero := aeroPQR.z, rho := atm.rho, rud := dr, stall, Sw := lit Gen.Sw,
    uAero := aeroUVW.x, vind := pr.vind }
  let ao := Gen.aero ai
  let m1 : α := lit (-1.0)
  let fnative : V3 α := ⟨ao.drag * m1, ao.side, ao.lift * m1⟩
  let faero := tw2b.mulV fnative
  let faeroCG := tw2b.mulV ⟨zero * m1, zero, zero * m1⟩
  let dxyzcg : V3 α := ⟨rpBody.x - zero, rpBody.y + zero, rpBody.z - zero⟩
  let maero := V3.add ⟨ao.roll, ao.pitch, ao.yaw⟩ (V3.cross dxyzcg faero)
  let faero := V3.add faero faeroCG
  -- FGGroundReactions
  let gctx : GearCtx α := { cg := mb.cg, tb2l, tec2l, tec2b, loc := locv, locTl2ec := locN.tec2l.T, pqr, uvw, dt,
                            brkL := u.brkL, brkR := u.brkR }
  let (gears, fgear, mgear, mults, gearFz) := Id.run do
    let mut gs := s.gears
    let mut fg : V3 α := V3.zero
    let mut mg : V3 α := V3.zero
    let mut ms : Array (Mult α) := #[]
    let mut fzs : Array α := #[]
    for i in [0:s.gears.size] do
      let (g, f, m, mm, fz) := gearForces i gctx s.gears[i]!
      gs := gs.set! i g
      fg := V3.add fg f
      mg := V3.add mg m
      ms := ms ++ mm
      fzs := fzs.push fz
    return (gs, fg, mg, ms, fzs)
  -- FGAircraft
  let ftot := V3.add (V3.add (V3.add (V3.add faero fprop) fgear) V3.zero) V3.zero
  let mtot := V3.add (V3.add (V3.add (V3.add maero mprop) mgear) V3.zero) V3.zero
  -- FGAccelerations
  let pqridot := mb.jinv.mulV (V3.sub mtot (V3.cross pqri (mb.j.mulV pqri)))
  let bodyAccel := V3.sdiv ftot mb.mass
  let uvwdot := V3.sub bodyAccel (V3.cross (V3.add pqr (V3.smul (lit 2.0) (ti2b.mulV omega))) uvw)
  let uvwdot := V3.sub uvwdot (ti2b.mulV (V3.cross omega (V3.cross omega ri)))
  let uvwdot := V3.add uvwdot (tec2b.mulV grav)
  let uvwidot := V3.add (tb2i.mulV bodyAccel) (tec2i.mulV grav)
  let pqrdot := V3.add pqridot (V3.cross pqri (ti2b.mulV omega))
  let (ffric, mfric, mults) := friction mults mb.mass mb.jinv uvwdot pqrdot uvw pqr tec2b dt
  let gears := mults.foldl (fun gs m => gs.modify m.gear fun g =>
    if m.slot == 0 then { g with lm0 := m.value } else if m.slot == 1 then { g with lm1 := m.value }
    else { g with lm2 := m.value }) gears
  let (uvwdot, uvwidot, pqridot) := if mults.isEmpty then (uvwdot, uvwidot, pqridot) else
    let accel := V3.sdiv ffric mb.mass
    let omegadot := mb.jinv.mulV mfric
    (V3.add uvwdot accel, V3.add uvwidot (tb2i.mulV accel), V3.add pqridot omegadot)
  ({ q, qdot, pqri, ri, vi, vih0 := s.vi, vih1 := s.vih0, aih0 := s.uvwidot, epa, pqridot, uvwidot, uvwdot,
     stall, cg := mb.cg, tank0, tank1, tmap := eng.tmap, running := eng.running, fuelflow := eng.fuelflow,
     starved, rpm := pr.rpm, act := pr.act, lastcg := mb.cg, gears, wind := s.wind },
   { uvw, pqr, loc := locv, euler, hsl, agl, vned, alpha, beta, adot, qbar, vt, mach, pt, hmac, rho := atm.rho,
     p := atm.p, t := atm.t, a := atm.a, grav, fnat := fnative, mmrc := ⟨ao.roll, ao.pitch, ao.yaw⟩, faero, maero, fprop, mprop, ftot, mtot, thrust := pr.thrust,
     hp := eng.hp, mass := mb.mass, de, da, dr, fgear, mgear, ffric, gearFz })
where
  mT_fb (thrust : α) : V3 α := (m9 Gen.propT : M33 α).mulV ⟨thrust, zero, zero⟩

end JsbExact
