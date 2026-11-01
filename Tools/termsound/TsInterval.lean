import CityGate

/-! # Interval-dual enclosures of the escape loop's frame map and Jacobian over a box (`docs/termsound-proof.tex`, Section 6). -/

namespace TsInterval
open JsbExact

def LIBM_ULPS : Nat := 4
def NV : Nat := 34
def IW : Nat := 33

/-! ## Outward-rounded intervals -/

def nextUp (x : Float) : Float :=
  if x.isNaN || x == (1.0 / 0.0) then x
  else if x == 0.0 then Float.ofBits 1
  else if x > 0.0 then Float.ofBits (x.toBits + 1) else Float.ofBits (x.toBits - 1)
def nextDown (x : Float) : Float := -(nextUp (-x))
def upN (x : Float) : Nat → Float | 0 => x | n + 1 => upN (nextUp x) n
def downN (x : Float) : Nat → Float | 0 => x | n + 1 => downN (nextDown x) n

structure Iv where
  lo : Float
  hi : Float
  deriving Inhabited

namespace Iv
def pt (x : Float) : Iv := ⟨x, x⟩
def zero : Iv := pt 0
def out (lo hi : Float) : Iv := ⟨nextDown lo, nextUp hi⟩
def outN (n : Nat) (lo hi : Float) : Iv := ⟨downN lo n, upN hi n⟩
def add (a b : Iv) : Iv := out (a.lo + b.lo) (a.hi + b.hi)
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
def sub (a b : Iv) : Iv := add a (neg b)
def mn4 (a b c d : Float) : Float := min (min a b) (min c d)
def mx4 (a b c d : Float) : Float := max (max a b) (max c d)
def mul (a b : Iv) : Iv :=
  if a.lo == 0 && a.hi == 0 || b.lo == 0 && b.hi == 0 then zero else
  let p1 := a.lo * b.lo; let p2 := a.lo * b.hi; let p3 := a.hi * b.lo; let p4 := a.hi * b.hi
  out (mn4 p1 p2 p3 p4) (mx4 p1 p2 p3 p4)
def inf : Float := 1.0 / 0.0
def div (a b : Iv) : Iv :=
  if b.lo > 0 || b.hi < 0 then
    let p1 := a.lo / b.lo; let p2 := a.lo / b.hi; let p3 := a.hi / b.lo; let p4 := a.hi / b.hi
    out (mn4 p1 p2 p3 p4) (mx4 p1 p2 p3 p4)
  else ⟨-inf, inf⟩
def hull (a b : Iv) : Iv := ⟨min a.lo b.lo, max a.hi b.hi⟩
def mid (a : Iv) : Float := 0.5 * a.lo + 0.5 * a.hi
def rad (a : Iv) : Float := nextUp (max (a.hi - mid a) (mid a - a.lo))
def sqrt (a : Iv) : Iv := out (Float.sqrt (max a.lo 0)) (Float.sqrt (max a.hi 0))
def mono (f : Float → Float) (a : Iv) : Iv := outN LIBM_ULPS (f a.lo) (f a.hi)
/-- 1-Lipschitz bounded-by-one library function (`sin`, `cos`): value at the midpoint ± radius. -/
def lip1 (f : Float → Float) (a : Iv) : Iv :=
  let m := mid a; let r := rad a; let c := f m
  let i := outN LIBM_ULPS (c - r) (c + r)
  ⟨max i.lo (-1), min i.hi 1⟩
def abs (a : Iv) : Iv :=
  if a.lo ≥ 0 then a else if a.hi ≤ 0 then neg a else ⟨0, max (-a.lo) a.hi⟩
def asin (a : Iv) : Iv := mono Float.asin ⟨max a.lo (-1), min a.hi 1⟩
def pi : Iv := ⟨3.141592653589793, 3.1415926535897936⟩
/-- `atan2 y x`, enclosed for `x > 0` (via `atan (y / x)`) and for `y > 0` or `y < 0` (via `±π/2 − atan (x / y)`). -/
def atan2 (y x : Iv) : Iv :=
  if x.lo > 0 then mono Float.atan (div y x)
  else if y.lo > 0 then sub (mul ⟨0.5, 0.5⟩ pi) (mono Float.atan (div x y))
  else if y.hi < 0 then sub (neg (mul ⟨0.5, 0.5⟩ pi)) (mono Float.atan (div x y))
  else ⟨-3.1415926535897936, 3.1415926535897936⟩
def log (a : Iv) : Iv := if a.lo > 0 then mono Float.log a else ⟨-inf, inf⟩
def exp (a : Iv) : Iv := mono Float.exp a
end Iv

/-! ## Interval duals -/

/-- An empty `d` is all zeros; `at2` marks an `atan2` result, whose `abs` becomes the input `w` (index `IW`); `lin`
marks an `atan2` result shifted or scaled by constants (see `linRule`). -/
structure ID where
  v : Iv
  d : Array Iv
  at2 : Bool := false
  lin : Bool := false
  deriving Inhabited

namespace ID
def dget (a : ID) (i : Nat) : Iv := a.d.getD i Iv.zero
def zipD (f : Iv → Iv → Iv) (a b : ID) : Array Iv :=
  if a.d.isEmpty && b.d.isEmpty then #[] else (List.range NV).toArray.map fun i => f (a.dget i) (b.dget i)
def mapD (f : Iv → Iv) (a : ID) : Array Iv := a.d.map f
def scaleD (s : Iv) (a : ID) : Array Iv := mapD (Iv.mul s) a
def lin2 (s : Iv) (a : ID) (t : Iv) (b : ID) : Array Iv :=
  if a.d.isEmpty && b.d.isEmpty then #[] else
  (List.range NV).toArray.map fun i => Iv.add (Iv.mul s (a.dget i)) (Iv.mul t (b.dget i))
def const (x : Float) : ID := ⟨Iv.pt x, #[], false, false⟩
def add (a b : ID) : ID := ⟨Iv.add a.v b.v, zipD Iv.add a b, false, false⟩
def isPt (a : ID) : Bool := a.d.isEmpty
def sub (a b : ID) : ID := ⟨Iv.sub a.v b.v, zipD Iv.sub a b, false, a.lin && isPt b⟩
def neg (a : ID) : ID := ⟨Iv.neg a.v, mapD Iv.neg a, false, false⟩
def mul (a b : ID) : ID := ⟨Iv.mul a.v b.v, lin2 b.v a a.v b, false, false⟩
def div (a b : ID) : ID :=
  let q := Iv.div a.v b.v
  let inv := Iv.div (Iv.pt 1) b.v
  ⟨q, lin2 inv a (Iv.neg (Iv.mul q inv)) b, false, a.lin && isPt b⟩
/-- Chain rule with derivative enclosure `f'`. -/
def chain (val f' : Iv) (a : ID) : ID := ⟨val, scaleD f' a, false, false⟩
def sqrt (a : ID) : ID := let s := Iv.sqrt a.v; chain s (Iv.div (Iv.pt 0.5) s) a
def sin (a : ID) : ID := chain (Iv.lip1 Float.sin a.v) (Iv.lip1 Float.cos a.v) a
def cos (a : ID) : ID := chain (Iv.lip1 Float.cos a.v) (Iv.neg (Iv.lip1 Float.sin a.v)) a
def atan (a : ID) : ID := chain (Iv.mono Float.atan a.v) (Iv.div (Iv.pt 1) (Iv.add (Iv.pt 1) (Iv.mul a.v a.v))) a
def asin (a : ID) : ID :=
  chain (Iv.asin a.v) (Iv.div (Iv.pt 1) (Iv.sqrt (Iv.sub (Iv.pt 1) (Iv.mul a.v a.v)))) a
def exp (a : ID) : ID := let e := Iv.exp a.v; chain e e a
def log (a : ID) : ID := chain (Iv.log a.v) (Iv.div (Iv.pt 1) a.v) a
def atan2 (y x : ID) : ID :=
  let r2 := Iv.add (Iv.mul x.v x.v) (Iv.mul y.v y.v)
  ⟨Iv.atan2 y.v x.v, lin2 (Iv.div x.v r2) y (Iv.neg (Iv.div y.v r2)) x, true, true⟩
def pow (a b : ID) : ID := exp (mul b (log a))
def hullD (a b : ID) : ID := ⟨Iv.hull a.v b.v, zipD Iv.hull a b, false, false⟩
def abs (a : ID) : ID :=
  if a.at2 then
    let m := max (-a.v.lo) a.v.hi
    ⟨⟨0, max m 0⟩, (List.range NV).toArray.map fun i => if i == IW then Iv.pt 1 else Iv.zero, false, false⟩
  else if a.v.lo ≥ 0 then { a with at2 := false } else if a.v.hi ≤ 0 then neg a
  else ⟨Iv.abs a.v, a.d.map fun g => Iv.hull g (Iv.neg g), false, false⟩
end ID

structure CI where
  t : Bool
  f : Bool
  deriving Inhabited

/-- The structural fact for the β tables: `CYb`, `Clb` and `Cnb` take antisymmetric values about their row β = 0, so
on |β| ≤ 0.349 each segment's interpolation, unclamped, is the same line. An undecided comparison between the
literal 0 and a `lin` value is therefore settled as "β on the upper segment, not below its start"; it must be
used only where every such comparison comes from those tables (checked by the run's α enclosure). -/
def linRule (a b : ID) : Option Bool :=
  if b.lin && a.v.lo == 0 && a.v.hi == 0 && a.d.isEmpty then some true
  else if a.lin && b.v.lo == 0 && b.v.hi == 0 && b.d.isEmpty then some false
  else none

def ltI (strict : Bool) (a b : ID) : CI :=
  let t := if strict then a.v.lo < b.v.hi else a.v.lo ≤ b.v.hi
  let f := if strict then a.v.hi ≥ b.v.lo else a.v.hi > b.v.lo
  if t && f then match linRule a b with | some r => ⟨r, !r⟩ | none => ⟨t, f⟩ else ⟨t, f⟩

instance : Scalar ID where
  Cond := CI
  ofFloat := ID.const
  add := ID.add
  sub := ID.sub
  mul := ID.mul
  div := ID.div
  neg := ID.neg
  fma a b c := ID.add (ID.mul a b) c
  lt := ltI true
  le := ltI false
  eq a b := ⟨a.v.lo ≤ b.v.hi && b.v.lo ≤ a.v.hi, !(a.v.lo == a.v.hi && b.v.lo == b.v.hi && a.v.lo == b.v.lo)⟩
  ofBool b := ⟨b, !b⟩
  not c := ⟨c.f, c.t⟩
  and a b := ⟨a.t && b.t, a.f || b.f⟩
  or a b := ⟨a.t || b.t, a.f && b.f⟩
  branch join c t e := if c.t && !c.f then t () else if c.f && !c.t then e () else join (t ()) (e ())
  join := ID.hullD
  mode c := if c.t && c.f then panic! "tsbox: undecided mode (ground contact?)" else c.t
  sqrt := ID.sqrt
  sin := ID.sin
  cos := ID.cos
  sinS := ID.sin
  cosS := ID.cos
  atan := ID.atan
  asin := ID.asin
  atan2 := ID.atan2
  pow := ID.pow
  exp := ID.exp
  abs := ID.abs

/-! ## The closed loop over a generic scalar -/

open S

variable {α : Type} [Scalar α]

def ft : Float := 0.3048

def liftV (v : V3 Float) : V3 α := ⟨lit v.x, lit v.y, lit v.z⟩
def liftM (m : M33 Float) : M33 α :=
  ⟨lit m.a11, lit m.a12, lit m.a13, lit m.a21, lit m.a22, lit m.a23, lit m.a31, lit m.a32, lit m.a33⟩
def liftQ (q : Quat Float) : Quat α := ⟨lit q.q0, lit q.q1, lit q.q2, lit q.q3⟩

def liftState (s : State Float) : State α :=
  { q := liftQ s.q, qdot := liftQ s.qdot, pqri := liftV s.pqri, ri := liftV s.ri, vi := liftV s.vi,
    vih0 := liftV s.vih0, vih1 := liftV s.vih1, aih0 := liftV s.aih0, epa := lit s.epa, pqridot := liftV s.pqridot,
    uvwidot := liftV s.uvwidot, uvwdot := liftV s.uvwdot, stall := lit s.stall, cg := liftV s.cg, tank0 := lit s.tank0,
    tank1 := lit s.tank1, tmap := lit s.tmap, running := cbool s.running, fuelflow := lit s.fuelflow,
    starved := cbool s.starved, rpm := lit s.rpm, act := liftV s.act, lastcg := liftV s.lastcg,
    gears := s.gears.map fun g =>
      { wow := g.wow, lm0 := lit g.lm0, lm1 := lit g.lm1, lm2 := lit g.lm2, slip := lit g.slip, steer := lit g.steer,
        act := liftV g.act, mT := liftM g.mT },
    wind := liftV s.wind }

/-- `CityJsb.tl2bOf`, generic. -/
def tl2bOfG (phi tht psi : α) : M33 α :=
  let cf := cos phi; let sf := sin phi; let ct := cos tht; let st := sin tht; let cp := cos psi; let sp := sin psi
  M33.mk' (ct * cp) (ct * sp) (-st)
    (sf * st * cp - cf * sp) (sf * st * sp + cf * cp) (sf * ct)
    (cf * st * cp + sf * sp) (cf * st * sp - sf * cp) (cf * ct)

def rTrackG (psi : Float) : M33 α :=
  let c := psi.cos; let s := psi.sin
  M33.mk' (lit c) (lit s) zero (lit (-s)) (lit c) zero zero zero one

def ti2ecOf (epa : α) : M33 α :=
  let ce := cosS epa; let se := sinS epa
  M33.mk' ce se zero (-se) ce zero zero zero one

/-- `TsMap.obsOf`, fields 0–14. -/
def obsOfG (s : State α) : Array α :=
  let omega : V3 α := v3 Gen.omega
  let ti2ec := ti2ecOf s.epa
  let locv := ti2ec.mulV s.ri
  let loc := locDerive locv
  let ti2l := loc.tec2l.mul ti2ec
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
  let mUW := aeroUVW.x * aeroUVW.x + aeroUVW.z * aeroUVW.z
  let vt2 := mUW + aeroUVW.y * aeroUVW.y
  let vt := sqrt vt2
  let k : α := lit ft
  let alpha := atan2 aeroUVW.z aeroUVW.x
  let beta := atan2 aeroUVW.y (sqrt mUW)
  #[locv.z * k, locv.y * k, hsl * k, vned.x * k, vned.y * k, vned.z * k, vt * k, euler.x, euler.y, euler.z,
    pqr.x, pqr.y, pqr.z, alpha, beta]

/-- The local-to-inertial rotation of a state. -/
def tl2iOfG (s : State α) : M33 α :=
  let ti2ec := ti2ecOf s.epa
  ((locDerive (ti2ec.mulV s.ri)).tec2l.mul ti2ec).T

/-- `TsMap.chart`; the heading difference is not wrapped, so the run must check it stays within ±π. -/
def chartG (psi : Float) (st : State α) (ia ib iphi : α) (ob : Array α) : α × Array α :=
  let rt : M33 α := rTrackG psi
  let ti2t := rt.mul (tl2iOfG st).T
  let k : α := lit ft
  let tr (v : V3 α) : V3 α := V3.smul k (ti2t.mulV v)
  let vt := V3.smul k (rt.mulV ⟨ob[3]! / k, ob[4]! / k, ob[5]! / k⟩)
  let vec (v : V3 α) : Array α := #[v.x, v.y, v.z]
  (ob[2]!,
   #[ob[7]!, ob[8]!, ob[9]! - lit psi] ++ vec vt ++ vec st.pqri ++ vec (tr (V3.sub st.vi st.vih0))
   ++ vec (tr (V3.sub st.vih0 st.vih1)) ++ vec (tr st.uvwidot) ++ vec (tr st.aih0) ++ vec st.pqridot
   ++ vec (V3.smul k st.uvwdot) ++ #[st.rpm, st.tmap, ia, ib, iphi])

def placeG (base : State Float) (psi north : Float) (h : α) (y : Array α) : State α :=
  let k : α := lit ft
  let ri : V3 α := ⟨lit Gen.a + h / k, zero, lit (north / ft)⟩
  let tec2l := (locDerive ri).tec2l
  let tl2i := tec2l.T
  let l2b := tl2bOfG y[0]! y[1]! (lit psi + y[2]!)
  let ti2b := l2b.mul tec2l
  let q := ti2b.toQuat
  let t2i := tl2i.mul (rTrackG psi).T
  let un (i : Nat) : V3 α := t2i.mulV ⟨y[i]! / k, y[i+1]! / k, y[i+2]! / k⟩
  let raw (i : Nat) : V3 α := ⟨y[i]!, y[i+1]!, y[i+2]!⟩
  let omega : V3 α := v3 Gen.omega
  let vi := V3.add (un 3) (V3.cross omega ri)
  let vih0 := V3.sub vi (un 9)
  let vih1 := V3.sub vih0 (un 12)
  let pqri := raw 6
  let b : State α := liftState base
  { b with q, qdot := q.qdot pqri, pqri, ri, vi, vih0, vih1, aih0 := un 18, epa := zero, pqridot := raw 21,
           uvwidot := un 15, uvwdot := V3.smul (one / k) (raw 24), rpm := y[27]!, tmap := y[28]! }

/-! ## The escape law, generic: straight escape, terminal phase and level-off (`docs/escape-law-terminal.md`) -/

structure Term where
  vEas : Float := 35.2
  kv : Float := 0.06
  kiA : Float := 6.0
  gcLo : Float := 0.0
  gcHi : Float := 0.5
  hLevel : Float := 1000.0
  kHold : Float := 0.005

def rhoOfG (h : α) : α := lit 1.225 * pow (S.max (one - lit 2.2558e-5 * h) (lit 0.5)) (lit 4.256)

open CityGate.Esc in
/-- One frame of the law on observation `o` with integrators `(ia, ib, iphi)` and held track `psiRef`: surfaces
(elevator in JSBSim's sign, aileron, rudder), new integrators, and the saturation decisions
`[elevator, α-integrator, aileron, roll-integrator, rudder, yaw-integrator, gc-climb, level cap, n, AMAX, bank
target, v < 10, cphi < 0.35]`, each a decision that must be settled to "inactive" on the box. -/
def lawG (T : Term) (psiRef : Float) (o : Array α) (ia ib iphi : α) :
    (α × α × α) × (α × α × α) × Array (Scalar.Cond α) :=
  let gh := sqrt (o[3]! * o[3]! + o[4]! * o[4]!)
  let vlow := lt o[6]! (lit 10.0)
  let v := S.ite vlow (lit 10.0) o[6]!
  let g := atan2 (-o[5]!) gh
  let phi := o[7]!
  let sphi := sin phi
  let cphi := cos phi
  let vs := v * sqrt (rhoOfG o[2]! / lit 1.225) - lit T.vEas
  let gcRaw := lit GC_REF + lit T.kv * vs
  let gcSat := cor (lt gcRaw (lit T.gcLo)) (gt gcRaw (lit T.gcHi))
  let gcClimb := constrain (lit T.gcLo) gcRaw (lit T.gcHi)
  let capRaw := lit T.kHold * (lit T.hLevel - o[2]!)
  let capSat := cor (lt capRaw (lit (-GC_HI))) (gt capRaw (lit GC_HI))
  let cap := constrain (lit (-GC_HI)) capRaw (lit GC_HI)
  let gc := S.min gcClimb cap
  let nLong := cos g + v * lit KG * (gc - g) / lit G0
  let cphiLow := lt cphi (lit 0.35)
  let nRaw := nLong / cphi
  let nSat := cor (lt nRaw (lit NMIN)) (gt nRaw (lit NMAX))
  let ncmd := sif cphiLow then lit NMIN else constrain (lit NMIN) nRaw (lit NMAX)
  let rv2 := rhoOfG o[2]! * v * v
  let acmdRaw := lit A0 + lit KA0 * ncmd / rv2
  let aSat := lt (lit AMAX) acmdRaw
  let acmd := S.min acmdRaw (lit AMAX)
  let nAch := (acmd - lit A0) * rv2 / lit KA0
  let qcmd := lit G0 * (nAch - cos g * cphi) / v
  let sc := S.min ((lit VS / v) * (lit VS / v)) one
  let ea := acmd - o[13]!
  let eRaw := lit E0 + lit E1 * acmd + lit KQF * qcmd * lit 40.0 / v + sc * (lit KA * ea - lit KQ * (o[11]! - qcmd)) + ia
  let eSat := cor (lt eRaw (lit (-1.0))) (gt eRaw one)
  let e := constrain (lit (-1.0)) eRaw one
  let iaRaw := ia + lit T.kiA * ea * lit DT_JSB
  let iaSat := cor (lt iaRaw (lit (-0.4))) (gt iaRaw (lit 0.4))
  let ia' := sif eSat then ia else constrain (lit (-0.4)) iaRaw (lit 0.4)
  let track := atan2 o[4]! o[3]!
  let phiTRaw := lit KPSI * (lit psiRef - track)
  let phiTSat := cor (lt phiTRaw (lit (-0.15))) (gt phiTRaw (lit 0.15))
  let phiT := constrain (lit (-0.15)) phiTRaw (lit 0.15)
  let ephi := phiT - phi
  let ailRaw := lit KPHI * ephi - lit KP * o[10]! + iphi
  let ailSat := cor (lt ailRaw (lit (-1.0))) (gt ailRaw one)
  let ail := constrain (lit (-1.0)) ailRaw one
  let iphiRaw := iphi + lit KI_PHI * ephi * lit DT_JSB
  let iphiSat := cor (lt iphiRaw (lit (-0.3))) (gt iphiRaw (lit 0.3))
  let iphi' := sif ailSat then iphi else constrain (lit (-0.3)) iphiRaw (lit 0.3)
  let rTurn := lit G0 / v * sphi
  let beta := o[14]!
  let rudRaw := -(lit KB) * beta + lit KR * (o[12]! - rTurn) + ib
  let rudSat := cor (lt rudRaw (lit (-1.0))) (gt rudRaw one)
  let rud := constrain (lit (-1.0)) rudRaw one
  let ibRaw := ib - lit KI_B * beta * lit DT_JSB
  let ibSat := cor (lt ibRaw (lit (-0.5))) (gt ibRaw (lit 0.5))
  let ib' := sif rudSat then ib else constrain (lit (-0.5)) ibRaw (lit 0.5)
  ((-e, ail, rud), (ia', ib', iphi'),
   #[eSat, iaSat, ailSat, iphiSat, rudSat, ibSat, gcSat, capSat, nSat, aSat, phiTSat, vlow, cphiLow])

/-- One frame from local coordinates `(h, y)` at held track `psi` and north offset `north`: the law, the plant with
fuel frozen, then the chart; also the plant's β (the argument of its `|β|`) and α, and the law's saturation decisions. -/
def frameG (T : Term) (base : State Float) (psi north : Float) (h : α) (y : Array α) :
    (α × Array α) × (α × α) × Array (Scalar.Cond α) :=
  let st := placeG base psi north h y
  let ob := obsOfG st
  let ((el, ai, ru), (ia, ib, iphi), sats) := lawG T psi ob y[29]! y[30]! y[31]!
  let i : Input α := { elev := el, ail := ai, rud := ru, thr := one, mix := lit 0.9, brkL := zero, brkR := zero }
  let (s', d) := step st i (fuelFreeze := true)
  (chartG psi s' ia ib iphi (obsOfG s'), (d.beta, d.alpha), sats)

/-- `frameG` on the box `c ± b` (33 inputs: altitude, then the chart's 32), as interval duals. -/
def frameBox (T : Term) (base : State Float) (psi north : Float) (c b : Array Float) :
    (ID × Array ID) × (ID × ID) × Array CI :=
  let x : Array ID := (List.range 33).toArray.map fun i =>
    { v := Iv.out (c[i]! - b[i]!) (c[i]! + b[i]!),
      d := (List.range NV).toArray.map fun j => if j == i then Iv.pt 1 else Iv.zero }
  frameG (α := ID) T base psi north x[0]! (x.extract 1 33)

end TsInterval
