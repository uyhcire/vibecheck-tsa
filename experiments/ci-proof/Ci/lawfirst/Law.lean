import Ci.Rules

/-! lawfirst: an α-command escape law with a load-factor limit, a fast unsaturated inner loop and integral
action on the α error. All arithmetic is on raw `Fx` integers (value = raw / 2^16). -/

namespace Ci.Lawfirst
open ExpVibecheck ExpJsb

/-- Law parameters, all raw (×2^16) unless noted. -/
structure P where
  /-- climb speed target, m/s raw -/
  vC : Int := 40 * 65536
  /-- α at the climb target, rad raw -/
  aRef : Int := 3277
  /-- α per m/s of speed excess (raw rad per raw m/s, ×2^16) -/
  kV : Int := 1311
  /-- α per rad of flight-path deficit below `gC` (×2^16) -/
  kG : Int := 25600
  /-- flight-path target (tan γ raw) -/
  gC : Int := 9830
  /-- α command bounds (tan α raw) -/
  aMax : Int := 15000
  aMin : Int := -6000
  /-- load-factor limit (raw n) and zero-lift α (tan α raw) of the lift-slope estimate -/
  nLim : Int := 3 * 65536
  a0 : Int := -4000
  /-- elevator per rad α error, elevator per rad/s pitch rate, integral gain per tick (×2^16) -/
  kA : Int := 2 * 65536
  kQ : Int := 19661
  kI : Int := 3277
  /-- feedforward elevator per rad of α command (×2^16): the static trim slope -/
  kF : Int := 111411
  /-- integrator init: `eB0 + eB1 · tanα` (eB1 ×2^16); used when `initPilot = false` -/
  eB0 : Int := -5243
  eB1 : Int := 0
  initPilot : Bool := false
  /-- throttle: idle above this speed while descending (raw m/s), else full -/
  vIdle : Int := 1000 * 65536
  /-- α command slew limits per tick (tan α raw) -/
  rUp : Int := 1000000
  rDn : Int := 1000000
  /-- flight-path ceiling (tan γ raw) above which α is cut by `kGL` per unit excess (×2^16) -/
  gMax : Int := 1000000
  kGL : Int := 0
  /-- damp pitch rate relative to the steady pull rate `g (n − 1) / V` instead of relative to 0 -/
  qss : Bool := false
  /-- α per m/s of speed deficit below `vC` (×2^16); negative means "same as `kV`" -/
  kVlo : Int := -1
  /-- load-factor limit once climbing (vz > 0); negative means "same as `nLim`". The altitude loss is decided
  before the bottom, so a gentler pull afterwards costs nothing and keeps the climb-out further from the limits. -/
  nLimUp : Int := -1
  deriving Repr, Inhabited

/-- Law memory: the α-error integrator, which is the elevator's slowly varying part. -/
structure Mem where
  eI : Int
  /-- α command applied on the previous tick (tan α raw) -/
  ac : Int
  deriving Repr, Inhabited, BEq

def clampI (lo hi x : Int) : Int := max lo (min hi x)

/-- tan α (raw) of the body velocity; a large value when u ≤ 0. -/
def tanA (s : State) : Int :=
  let u := s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw
  let w := s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw
  if u > 0 then w * 65536 / u else 1000000

/-- Load factor (raw) from the state's last evaluated accelerations, as `Ci.loadOk` measures it. -/
def nRaw (s : State) : Int := Ci.loadNum s / Ci.gRaw

def speedRaw (s : State) : Int := (Nat.sqrt (s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw).toNat : Int)

/-- tan γ (raw). -/
def tanG (s : State) : Int := if s.vx.raw > 0 then s.vz.raw * 65536 / s.vx.raw else 0

/-- The α command: speed hold plus flight-path term, capped by α bounds and the load-factor estimate. -/
def alphaCmd (p : P) (s : State) : Int :=
  let ta := tanA s
  let v := speedRaw s
  let tg := tanG s
  let kv := if v < p.vC && p.kVlo ≥ 0 then p.kVlo else p.kV
  let raw := p.aRef + kv * (v - p.vC) / 65536 + p.kG * (p.gC - tg) / 65536 - p.kGL * max 0 (tg - p.gMax) / 65536
  let n := nRaw s
  let nL := if s.vz.raw > 0 && p.nLimUp ≥ 0 then p.nLimUp else p.nLim
  let aN := if n > 19661 && ta > p.a0 then p.a0 + (ta - p.a0) * nL / n else p.aMax
  clampI p.aMin (min p.aMax aN) raw

def stepP (p : P) (m : Mem) (s : State) : Input × Mem :=
  let ta := tanA s
  let ac := clampI (m.ac - p.rDn) (m.ac + p.rUp) (alphaCmd p s)
  let err := ac - ta
  let qRef := if p.qss then Ci.gRaw * (nRaw s - 65536) / max 65536 (speedRaw s) else 0
  let e := m.eI + p.kF * ac / 65536 + p.kA * err / 65536 - p.kQ * (s.q.raw - qRef) / 65536
  let eI' := clampI (-65536) 65536 (m.eI + p.kI * err / 65536)
  let thr : Int := if s.vz.raw < 0 && speedRaw s > p.vIdle then 0 else 65536
  (⟨⟨clampI (-65536) 65536 e⟩, ⟨thr⟩, ⟨0⟩, ⟨0⟩⟩, ⟨eI', ac⟩)

def initP (p : P) (c : Ci.Commit) : Mem :=
  ⟨if p.initPilot then c.pilot.elev.raw else clampI (-65536) 65536 (p.eB0 + p.eB1 * tanA c.s / 65536), tanA c.s⟩

def within (x lo hi : Int) : Bool := lo ≤ x && x ≤ hi

def encM (m : Mem) : Array Int := #[m.eI, m.ac]
def decM (a : Array Int) : Option Mem := if a.size == 2 then some ⟨a[0]!, a[1]!⟩ else none

end Ci.Lawfirst
