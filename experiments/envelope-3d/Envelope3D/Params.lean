import ExpEnvelope.Proofs
import Envelope3D.Grid

/-! Abstract 3D state, filter mode and envelope parameters (SI units: m, s, m/s, m/s², rad). -/

namespace Envelope3D
open ExpEnvelope (Perf Band)

def absR (x : Rat) : Rat := max x (-x)

structure State where
  x : Rat
  y : Rat
  h : Rat
  vx : Rat
  vy : Rat
  vz : Rat
  V : Rat
  bank : Rat
  deriving Repr, DecidableEq, Inhabited

/-- Filter mode: free flight; an escape committed `k` ticks ago at state `ref`; or the climb-out
(a climbing turn held near `c`) that ends an escape. -/
inductive Mode where
  | free
  | escape (k : Nat) (ref : State)
  | climbOut (c : State)
  deriving Repr, DecidableEq, Inhabited

def Mode.advance : Mode → Mode
  | .escape k ref => .escape (k + 1) ref
  | m => m

/-- Worst one-tick change in free flight under one pilot input. -/
structure FreeBound where
  /-- per-component ground-velocity change per second (m/s²) -/
  hAcc : Rat
  vzDrop : Rat
  vzRise : Rat
  vDrop : Rat
  bankStep : Rat
  deriving Repr

/-- ExpEnvelope parameters; `ι` is the pilot input type. -/
structure Params (ι : Type) where
  dt : Rat
  /-- escape response delay, in ticks -/
  delayTicks : Nat
  /-- total vertical-speed loss below the commit value during the delay -/
  delayVzDrop : Rat
  /-- airspeed floor of an escape -/
  vMin : Rat
  /-- total airspeed loss below the commit value during an escape -/
  escVDrop : Rat
  /-- extra airspeed loss per m/s of commit climb rate (s): nose-high escapes bleed speed -/
  noseHighVDrop : Rat
  /-- pull and climb guaranteed at any escape airspeed, once wings are level -/
  base : Perf
  bands : List Band
  /-- vertical acceleration guaranteed while still banked during roll-out (may be negative) -/
  rollPull : Rat
  /-- bank increase allowed during the delay (rad) -/
  bankGrow : Rat
  /-- minimum bank reduction per tick after the delay (rad) -/
  rollStep : Rat
  /-- bank counted as wings level (rad) -/
  bankLevel : Rat
  /-- rows `(φ, a)`: at |bank| ≤ φ, ground speed × track rate ≤ a (m/s²) -/
  turnAcc : List (Rat × Rat)
  accMax : Rat
  /-- per-component ground-velocity deviation allowed at commit, before any turn -/
  velSlack : Rat
  /-- ground speed during an escape is between `gsLo` and `gsHi` times its commit value -/
  gsLo : Rat
  gsHi : Rat
  free : ι → FreeBound
  vgMax : Rat
  /-- allowed per-tick horizontal shortfall/excess beyond `dt · [min v v', max v v']` -/
  pSlack : Rat
  /-- allowed per-tick shortfall of altitude gain below `dt · min vz vz'` -/
  hSlack : Rat
  /-- climb-out: horizontal distance (each axis) the climbing turn stays within of its entry point -/
  climbR : Rat
  /-- climb-out: altitude it may lose below its entry altitude -/
  climbDrop : Rat
  /-- climb-out: vertical speed floor -/
  climbVz : Rat
  /-- allowed dip of altitude below both tick endpoints within a tick -/
  sag : Rat
  /-- required vertical clearance above the grid -/
  margin : Rat
  grid : Grid
  /-- commit guard: escapes are certified only from states with vz ≤ `commitVzMax` -/
  commitVzMax : Rat
  /-- commit guard: and airspeed ≥ `vMin + commitVMargin` -/
  commitVMargin : Rat
  /-- escape check length, in ticks -/
  horizon : Nat

namespace Params
variable {ι : Type} (P : Params ι)

/-- Escape performance guaranteed at airspeed `V` (as in 2D). -/
def perf (V : Rat) : Perf := P.bands.foldl (ExpEnvelope.Params.addBand V) P.base

/-- Bound on ground speed × track rate at |bank| ≤ `φ`: the smallest applicable row. -/
def latAcc (φ : Rat) : Rat :=
  P.turnAcc.foldl (fun a r => if φ ≤ r.1 then min a r.2 else a) P.accMax

/-- Side conditions on the parameters used by the proofs. -/
def WellFormed : Prop :=
  0 ≤ P.dt ∧ 0 < P.grid.wx ∧ 0 < P.grid.wy ∧ 0 ≤ P.sag ∧ 0 ≤ P.noseHighVDrop ∧
    P.rollPull ≤ P.base.pull ∧ 0 ≤ P.gsLo ∧ P.gsLo ≤ P.gsHi ∧ 0 ≤ P.velSlack ∧ 0 ≤ P.accMax ∧
    (∀ r ∈ P.turnAcc, 0 ≤ r.2) ∧ 0 ≤ P.pSlack ∧ 0 ≤ P.climbR ∧ 0 ≤ P.climbDrop

instance : Decidable P.WellFormed := by unfold WellFormed; infer_instance

end Params
end Envelope3D
