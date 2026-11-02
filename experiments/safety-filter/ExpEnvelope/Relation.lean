import ExpEnvelope.Params

/-! The envelope relation: what the closed loop may do in one tick, and its runtime monitor. -/

namespace ExpEnvelope
variable {ι : Type}

/-- Lower bound on next tick's vertical speed, `k` ticks into an escape. -/
def vzEsc (P : Params ι) (k : Nat) (vz V : Rat) : Rat :=
  if k < P.delayTicks then vz - P.delayVzDrop
  else min (vz + (P.perf V).pull * P.dt) (P.perf V).climb

/-- Lower bound on next tick's airspeed during an escape. -/
def VEsc (P : Params ι) (V : Rat) : Rat := max P.vMin (V - P.escVDrop)

/-- Lower bound on next tick's vertical speed. -/
def vzFloor (P : Params ι) : Mode → ι → (vz V : Rat) → Rat
  | .free, u, vz, _ => vz - (P.free u).vzDrop
  | .escape k, _, vz, V => vzEsc P k vz V

/-- Lower bound on next tick's airspeed. -/
def VFloor (P : Params ι) : Mode → ι → (V : Rat) → Rat
  | .free, u, V => V - (P.free u).vDrop
  | .escape _, _, V => VEsc P V

/-- The envelope: one tick from `s` to `s'` in mode `m` (`u` matters only in free flight). -/
def Allowed (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) : Prop :=
  P.vxMin ≤ s'.vx ∧ s'.vx ≤ P.vxMax ∧
  s.x + P.dt * P.vxMin ≤ s'.x ∧ s'.x ≤ s.x + P.dt * P.vxMax ∧
  s.h + P.dt * min s.vz s'.vz - P.hSlack ≤ s'.h ∧
  vzFloor P m u s.vz s.V ≤ s'.vz ∧
  VFloor P m u s.V ≤ s'.V

/-- Runtime monitor: checks one observed transition against `Allowed`. -/
def monitor (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) : Bool :=
  decide (P.vxMin ≤ s'.vx) && decide (s'.vx ≤ P.vxMax) &&
  decide (s.x + P.dt * P.vxMin ≤ s'.x) && decide (s'.x ≤ s.x + P.dt * P.vxMax) &&
  decide (s.h + P.dt * min s.vz s'.vz - P.hSlack ≤ s'.h) &&
  decide (vzFloor P m u s.vz s.V ≤ s'.vz) && decide (VFloor P m u s.V ≤ s'.V)

theorem monitor_iff (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) :
    monitor P m s u s' = true ↔ Allowed P m s u s' := by
  simp [monitor, Allowed, and_assoc]

end ExpEnvelope
