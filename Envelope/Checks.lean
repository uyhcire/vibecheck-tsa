import Envelope.Proofs

/-! Concrete instances: satisfiable hypotheses, the filter passing, overriding and handing back,
checked substeps, spec rejections. -/

namespace Envelope.Checks
open Envelope

/-- Example pilot inputs: hold the current flight path, or push over hard. -/
inductive Stick where
  | hold
  | dive
  deriving DecidableEq, Repr

/-- Example terrain: flat at 0 m, with a 200 m ridge from x = 300 m to x = 800 m. -/
def ridge : Terrain where
  x0 := 0
  w := 50
  cells := #[0, 0, 0, 0, 0, 0, 200, 200, 200, 200, 200, 200, 200, 200, 200, 200, 0, 0, 0, 0]
  beyond := 0

/-- Example envelope (numbers in the range of a light aircraft; not fitted to JSBSim). -/
def P0 : Params Stick where
  dt := 1/8
  delayTicks := 4
  delayVzDrop := 1/2
  vMin := 30
  escVDrop := 1/5
  base := ⟨2, 2⟩
  bands := [⟨50, ⟨3, 4⟩⟩]
  free := fun | .hold => ⟨1/4, 1/10⟩ | .dive => ⟨20, 1/10⟩
  vxMin := 40
  vxMax := 60
  hSlack := 1/100
  sag := 1/2
  margin := 10
  terrain := ridge
  horizon := 400

theorem P0_wf : P0.WellFormed := by decide +kernel

/-- Level flight at 300 m, 50 m/s, short of the ridge. -/
def s0 : State := ⟨0, 300, 50, 0, 55⟩

example : Init P0 s0 := by decide +kernel
/-- The filter passes "hold" here ... -/
example : escapeClear P0 s0 .hold = true := by decide +kernel
/-- ... and overrides "dive". -/
example : escapeClear P0 s0 .dive = false := by decide +kernel
example : (P0.perf 55).pull = 3 ∧ (P0.perf 55).climb = 4 := by decide +kernel
example : (P0.perf 40).pull = 2 ∧ (P0.perf 40).climb = 2 := by decide +kernel

/-! ### `never_hit` with every hypothesis discharged: the pilot dives, the filter escapes, the aircraft climbs -/

def climbPilot : Nat → Stick := fun _ => .dive

/-- Climbing at 4 m/s and 50 m/s from 280 m. -/
def climbTraj (n : Nat) : State := ⟨n * (25/4), 280 + n * (1/2), 50, 4, 55⟩

/-- The climb obeys the envelope whatever mode the filter applies. -/
theorem climb_allowed_any (m : Mode) (n : Nat) :
    Allowed P0 m (climbTraj n) .dive (climbTraj (n + 1)) := by
  have hp : (P0.perf 55).pull = 3 ∧ (P0.perf 55).climb = 4 := by decide +kernel
  cases m with
  | free =>
    simp only [Allowed, vzFloor, VFloor, climbTraj]
    simp only [P0]
    push_cast; grind
  | escape k =>
    simp only [Allowed, vzFloor, VFloor, vzEsc, VEsc, climbTraj, hp]
    simp only [P0]
    by_cases hk : k < 4 <;> simp only [hk, ↓reduceIte] <;> push_cast <;> grind

theorem climb_allowed (n : Nat) :
    Allowed P0 (appliedAt (filter P0) climbTraj climbPilot n) (climbTraj n) (climbPilot n)
      (climbTraj (n + 1)) :=
  climb_allowed_any _ n

/-- The filter overrides the dive at the start of the climb. -/
example : appliedAt (filter P0) climbTraj climbPilot 0 = .escape 0 := by decide +kernel

theorem climb_init : Init P0 (climbTraj 0) := by decide +kernel

/-- `never_hit` applied with every hypothesis discharged. -/
example : ∀ n, TickClear P0 (climbTraj n) (climbTraj (n + 1)) :=
  never_hit P0 P0_wf climbPilot climbTraj climb_init climb_allowed

/-! ### Substeps: the within-tick assumption checked on a discrete plant -/

/-- One substep per tick, halfway along, at the tick's starting altitude. -/
def climbSubs (n : Nat) : List State := [⟨(n + 1/2) * (25/4), 280 + n * (1/2), 50, 4, 55⟩]

/-- `never_hit_substeps` with every hypothesis discharged: each substep clears terrain + margin. -/
example : ∀ n, ∀ p ∈ climbSubs n, P0.terrain.heightAt p.x + P0.margin < p.h :=
  never_hit_substeps P0 P0_wf climbPilot climbTraj climb_init climb_allowed climbSubs fun n => by
    simp only [substepOK, climbSubs, climbTraj, P0, List.all_cons, List.all_nil, Bool.and_true]
    push_cast; grind

/-- `substepOK` rejects a substep that sags more than `sag` below the tick's endpoints. -/
example : substepOK P0 (climbTraj 0) (climbTraj 1) [⟨3, 279, 50, 4, 55⟩] = false := by decide +kernel
/-- ... and one outside the tick's along-track interval. -/
example : substepOK P0 (climbTraj 0) (climbTraj 1) [⟨7, 281, 50, 4, 55⟩] = false := by decide +kernel

/-! ### The specification rejects bad behaviour -/

/-- Descending at 10 m/s towards the ridge, never pulling up. -/
def diveTraj (n : Nat) : State := ⟨n * (25/4), 300 - n * (5/4), 50, -10, 55⟩

/-- A never-triggering filter violates `NeverHits`: this envelope-obeying descent hits the ridge. -/
theorem neverTrigger_unsafe : ¬ NeverHits P0 (fun _ _ _ => .free) := by
  intro h
  have hinit : Init P0 (diveTraj 0) := by decide +kernel
  have hA : ∀ n, Allowed P0 (appliedAt (fun _ _ _ => .free) diveTraj (fun _ => Stick.hold) n)
      (diveTraj n) Stick.hold (diveTraj (n + 1)) := by
    intro n
    simp only [appliedAt, Allowed, vzFloor, VFloor, diveTraj, P0]
    push_cast; grind
  have := h (fun _ => .hold) diveTraj hinit hA 72 450 (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- `TickClear` fails for a tick that passes below the ridge top + margin. -/
example : ¬ TickClear P0 ⟨400, 205, 50, 0, 55⟩ ⟨406, 205, 50, 0, 55⟩ := by
  intro h; have := h 400 (by decide +kernel) (by decide +kernel); revert this; decide +kernel

/-- The monitor rejects sinking faster than the escape allows, and accepts the climb. -/
example : monitor P0 (.escape 10) ⟨0, 300, 50, -2, 55⟩ .hold ⟨6, 299, 50, -3, 55⟩ = false := by
  decide +kernel
example : monitor P0 (.escape 10) (climbTraj 10) .hold (climbTraj 11) = true := by decide +kernel

/-! ### Executable test: the closed loop against a plant that takes every envelope bound with equality -/

/-- Next state of the worst-case plant. -/
def worstStep {ι : Type} (P : Params ι) (m : Mode) (u : ι) (s : State) : State :=
  let vz' := vzFloor P m u s.vz s.V
  ⟨s.x + P.dt * P.vxMax, s.h + P.dt * min s.vz vz' - P.hSlack, s.vx, vz', VFloor P m u s.V⟩

/-- Ticks `(t, applied mode, s, s')` of the closed loop for `n` ticks. -/
def runLoop {ι : Type} (P : Params ι) (pilot : Nat → ι) : Nat → Nat → Mode → State →
    List (Nat × Mode × State × State)
  | 0, _, _, _ => []
  | n + 1, t, m, s =>
    let a := filter P m s (pilot t)
    let s' := worstStep P a (pilot t) s
    (t, a, s, s') :: runLoop P pilot n (t + 1) a.advance s'

/-- Hold for 2 s, then dive. -/
def holdThenDive (t : Nat) : Stick := if t < 16 then .hold else .dive

def demo := runLoop P0 holdThenDive 400 0 .free s0

#guard demo.all fun (t, a, s, s') => monitor P0 a s (holdThenDive t) s' -- every tick obeys the envelope
#guard demo.all fun (_, _, s, s') => tickOK P0 (Box.point s) (Box.point s') -- and clears terrain
#guard (demo.findIdx? fun (_, a, _, _) => a != .free) == some 16 -- the filter overrides the dive
#guard demo.getLast?.map (·.2.2.2.x) |>.any (800 < ·) -- past the ridge

/-! ### Hand-back: the filter returns control once the pilot's input is certified again -/

/-- From an escape, a certified input is passed: here holding level flight at `s0`. -/
example : filter P0 (.escape 5) s0 .hold = .free := by decide +kernel
/-- An uncertified input keeps the escape. -/
example : filter P0 (.escape 5) s0 .dive = .escape 5 := by decide +kernel

/-- Hold, dive for 4 ticks (overridden), then hold again. -/
def diveBriefly (t : Nat) : Stick := if 16 ≤ t ∧ t < 20 then .dive else .hold

def demo2 := runLoop P0 diveBriefly 400 0 .free s0

#guard demo2.all fun (t, a, s, s') => monitor P0 a s (diveBriefly t) s'
#guard demo2.all fun (_, _, s, s') => tickOK P0 (Box.point s) (Box.point s')
#guard (demo2.findIdx? fun (_, a, _, _) => a != .free) == some 16 -- the dive is overridden
#guard (demo2.findIdx? fun (t, a, _, _) => 16 < t && a == .free) == some 20 -- control comes back

end Envelope.Checks
