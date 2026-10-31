import Envelope.Terrain

/-! Abstract state, filter mode and envelope parameters (SI units: m, s, m/s, m/s²). -/

namespace Envelope

/-- Abstract aircraft state in the vertical plane. -/
structure State where
  x : Rat
  h : Rat
  vx : Rat
  vz : Rat
  V : Rat
  deriving Repr, DecidableEq, Inhabited

/-- Filter mode: free flight, or an escape committed `k` ticks ago. -/
inductive Mode where
  | free
  | escape (k : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Mode for the next tick: the escape counter advances. -/
def Mode.advance : Mode → Mode
  | .free => .free
  | .escape k => .escape (k + 1)

/-- Ticks into the escape (0 in free flight: the escape that would start now). -/
def Mode.phase : Mode → Nat
  | .free => 0
  | .escape k => k

/-- Worst per-tick worsening in free flight under one pilot input. -/
structure FreeBound where
  vzDrop : Rat
  vDrop : Rat
  deriving Repr

/-- Escape performance guarantee: vertical acceleration at least `pull` until climbing at least `climb`. -/
structure Perf where
  pull : Rat
  climb : Rat
  deriving Repr

/-- Table row: at airspeed at least `vLo`, the escape guarantees `perf`. -/
structure Band where
  vLo : Rat
  perf : Perf
  deriving Repr

/-- Envelope parameters; `ι` is the pilot input type. -/
structure Params (ι : Type) where
  /-- tick length (s) -/
  dt : Rat
  /-- escape response delay, in ticks -/
  delayTicks : Nat
  /-- worst per-tick vertical-speed drop during the delay -/
  delayVzDrop : Rat
  /-- airspeed floor once the escape is commanded -/
  vMin : Rat
  /-- worst per-tick airspeed drop during the escape -/
  escVDrop : Rat
  /-- escape performance guaranteed at any airspeed (at or above `vMin`) -/
  base : Perf
  /-- better guarantees at higher airspeeds -/
  bands : List Band
  /-- free-flight per-tick worsening for each pilot input -/
  free : ι → FreeBound
  /-- horizontal ground-speed range -/
  vxMin : Rat
  vxMax : Rat
  /-- allowed per-tick shortfall of altitude gain below `dt · min vz vz'` -/
  hSlack : Rat
  /-- allowed dip of altitude below both tick endpoints within a tick -/
  sag : Rat
  /-- required terrain clearance -/
  margin : Rat
  terrain : Terrain
  /-- escape check length, in ticks -/
  horizon : Nat

namespace Params
variable {ι : Type} (P : Params ι)

/-- Fold one table row into a guarantee (rows apply at airspeed ≥ `vLo`; take the best). -/
def addBand (V : Rat) (p : Perf) (b : Band) : Perf :=
  if b.vLo ≤ V then ⟨max p.pull b.perf.pull, max p.climb b.perf.climb⟩ else p

/-- Escape performance guaranteed at airspeed `V`. -/
def perf (V : Rat) : Perf := P.bands.foldl (addBand V) P.base

/-- Side conditions on the parameters used by the proof (`0 ≤ vxMin`: the aircraft only moves forward). -/
def WellFormed : Prop :=
  0 ≤ P.dt ∧ 0 < P.terrain.w ∧ 0 ≤ P.sag ∧ 0 ≤ P.base.pull ∧ P.hSlack ≤ P.dt * P.base.climb ∧
    0 ≤ P.vxMin

instance : Decidable P.WellFormed := by unfold WellFormed; infer_instance

end Params
end Envelope
