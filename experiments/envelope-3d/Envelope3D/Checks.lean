import Envelope3D.Proofs

/-! Concrete instances: satisfiable hypotheses, the filter passing, overriding and handing back,
checked substeps, spec rejections. -/

namespace Envelope3D.Checks
open Envelope3D

inductive Stick where
  | hold
  | dive
  deriving DecidableEq, Repr

/-- 400 m × 400 m of flat ground at 0 m (50 m cells) with one 40 m building on
`[200, 250) × [150, 250)`; flat ground beyond. -/
def town : Grid where
  x0 := 0
  y0 := 0
  wx := 50
  wy := 50
  nx := 8
  ny := 8
  cells := #[
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 40, 0, 0, 0,
      0, 0, 0, 0, 40, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0]
  beyond := 0

/-- Example envelope (light-aircraft numbers, not fitted to any model). -/
def P0 : Params Stick where
  dt := 1/4
  delayTicks := 2
  delayVzDrop := 1
  vMin := 30
  escVDrop := 10
  noseHighVDrop := 1
  base := ⟨2, 3⟩
  bands := [⟨45, ⟨3, 4⟩⟩]
  rollPull := 0
  bankGrow := 1/10
  rollStep := 1/4
  bankLevel := 1/20
  turnAcc := [(1/20, 1/2), (3/10, 3), (4/5, 10), (11/10, 20)]
  accMax := 30
  velSlack := 1
  gsLo := 7/10
  gsHi := 11/10
  free := fun | .hold => ⟨1, 1/4, 1/4, 1/10, 1/50⟩ | .dive => ⟨10, 5, 5, 1/2, 1/4⟩
  vgMax := 60
  pSlack := 1/20
  hSlack := 1/20
  climbR := 100
  climbDrop := 5
  climbVz := 1
  sag := 1/2
  margin := 10
  grid := town
  commitVzMax := 10
  commitVMargin := 1/2
  horizon := 200

def sTo : State := ⟨100, 200, 45, 50, 0, 0, 55, 0⟩
def sAway : State := ⟨100, 200, 45, -50, 0, 0, 55, 0⟩
def sFar : State := ⟨-200, 200, 45, 50, 0, 0, 55, 0⟩

theorem P0_wf : P0.WellFormed := by decide +kernel
example : escapeClear P0 sTo .hold = false := by decide +kernel
example : escapeClear P0 sAway .hold = true := by decide +kernel
theorem sFar_init : Init P0 sFar := by decide +kernel

/-! ### A building in the path forces an escape -/

/-- At 45 m, 100 m short of the 40 m building and heading for it, holding course is overridden ... -/
example : escapeClear P0 sTo .hold = false := by decide +kernel
/-- ... while the same state heading away is passed. -/
example : escapeClear P0 sAway .hold = true := by decide +kernel

/-! ### `never_hit3d` with every hypothesis discharged -/

def ModeFrom (s : Nat → State) (n : Nat) (m : Mode) : Prop :=
  m = .free ∨ (∃ k j, j ≤ n ∧ m = .escape k (s j)) ∨ (∃ j, j ≤ n ∧ m = .climbOut (s j))

/-- The filter only ever refers to states already flown. -/
theorem modes_from {ι : Type} (P : Params ι) (s : Nat → State) (pilot : Nat → ι) :
    ∀ n, ModeFrom s n (modeAt (filter P) s pilot n) ∧ ModeFrom s n (appliedAt (filter P) s pilot n) := by
  intro n
  have step : ∀ n, ModeFrom s n (modeAt (filter P) s pilot n) →
      ModeFrom s n (appliedAt (filter P) s pilot n) := by
    intro n h
    simp only [appliedAt, filter]
    split
    · exact Or.inl rfl
    · rcases h with h | ⟨k, j, hj, h⟩ | ⟨j, hj, h⟩ <;> rw [h] <;> simp only [escMode]
      · split
        · exact Or.inr (Or.inr ⟨n, Nat.le_refl _, rfl⟩)
        · exact Or.inr (Or.inl ⟨0, n, Nat.le_refl _, rfl⟩)
      · split
        · exact Or.inr (Or.inr ⟨n, Nat.le_refl _, rfl⟩)
        · exact Or.inr (Or.inl ⟨k, j, hj, rfl⟩)
      · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  induction n with
  | zero => exact ⟨Or.inl rfl, step 0 (Or.inl rfl)⟩
  | succ n ih =>
    have h : ModeFrom s (n + 1) (modeAt (filter P) s pilot (n + 1)) := by
      simp only [modeAt]
      rcases ih.2 with h | ⟨k, j, hj, h⟩ | ⟨j, hj, h⟩
      · exact Or.inl (by rw [show filter P _ _ _ = _ from h]; rfl)
      · exact Or.inr (Or.inl ⟨k + 1, j, by omega, by rw [show filter P _ _ _ = _ from h]; rfl⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, by rw [show filter P _ _ _ = _ from h]; rfl⟩)
    exact ⟨h, step _ h⟩

def climbPilot : Nat → Stick := fun _ => .dive

/-- Climbing at 4 m/s from 30 m, 100 m short of the building, with zero ground speed (a headwind). -/
def climbTraj (n : Nat) : State := ⟨100, 200, 30 + n, 0, 0, 4, 55, 0⟩

theorem climb_init : Init P0 (climbTraj 0) := by decide +kernel

/-- The filter overrides the dive at the start. -/
example : appliedAt (filter P0) climbTraj climbPilot 0 = .escape 0 (climbTraj 0) := by decide +kernel

/-- Commit-state bounds of any state of `climbTraj`. -/
def climbRef : Ref := ⟨4, 4, 55, absR 0, 0, 0, 0, 0⟩

theorem climbRef_eq (j : Nat) : Ref.ofState (climbTraj j) = climbRef := rfl

theorem climb_sched : ∀ k, (sched P0 climbRef k).vz ≤ 3
  | 0 => by decide +kernel
  | k + 1 => by
    have ih := climb_sched k
    have hc : climbOf P0 climbRef = 3 := by decide +kernel
    simp only [sched, schedNext, hc]
    split <;> grind

theorem climb_allowed_from (n : Nat) (m : Mode) (hm : ModeFrom climbTraj n m) :
    Allowed P0 m (climbTraj n) .dive (climbTraj (n + 1)) := by
  have hc : Common P0 (climbTraj n) (climbTraj (n + 1)) := by
    simp only [Common, climbTraj, P0, absR]; push_cast; grind
  refine ⟨hc, ?_⟩
  rcases hm with h | ⟨k, j, _, h⟩ | ⟨j, hj, h⟩ <;> subst h
  · simp only [ModeOK, climbTraj, P0, absR]; grind
  · have h1 := climb_sched (k + 1)
    have h2 := sched_sp_nonneg P0 P0_wf climbRef (k + 1)
    have h3 : VFloor P0 climbRef = 41 := by decide +kernel
    have h4 : 0 ≤ bankCap P0 climbRef (k + 1) := by
      have : (0 : Rat) ≤ P0.bankLevel := by decide +kernel
      simp only [bankCap]; grind
    simp only [ModeOK, climbRef_eq, h3, scaleLo, scaleHi]
    simp only [climbTraj, absR]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  · simp only [ModeOK, climbTraj, P0, absR]
    have : (j : Rat) ≤ n := by exact_mod_cast hj
    grind

theorem climb_allowed (n : Nat) :
    Allowed P0 (appliedAt (filter P0) climbTraj climbPilot n) (climbTraj n) (climbPilot n)
      (climbTraj (n + 1)) :=
  climb_allowed_from n _ (modes_from P0 climbTraj climbPilot n).2

/-- `never_hit3d` applied with every hypothesis discharged. -/
example : ∀ n, TickClear P0 (climbTraj n) (climbTraj (n + 1)) :=
  never_hit3d P0 P0_wf climbPilot climbTraj climb_init climb_allowed

/-! ### Substeps -/

def climbSubs (n : Nat) : List State := [⟨100, 200, 30 + n, 0, 0, 4, 55, 0⟩]

/-- `never_hit3d_substeps` with every hypothesis discharged. -/
example : ∀ n, ∀ p ∈ climbSubs n, P0.grid.heightAt p.x p.y + P0.margin < p.h :=
  never_hit3d_substeps P0 P0_wf climbPilot climbTraj climb_init climb_allowed climbSubs fun n => by
    simp only [substepOK, climbSubs, climbTraj, P0, List.all_cons, List.all_nil, Bool.and_true]
    push_cast; grind

/-- `substepOK` rejects a substep that sags more than `sag` below the tick's endpoints ... -/
example : substepOK P0 (climbTraj 0) (climbTraj 1) [⟨100, 200, 29, 0, 0, 4, 55, 0⟩] = false := by
  decide +kernel
/-- ... and one outside the tick's swept rectangle. -/
example : substepOK P0 (climbTraj 0) (climbTraj 1) [⟨100, 201, 30, 0, 0, 4, 55, 0⟩] = false := by
  decide +kernel

/-! ### The specification rejects bad behaviour -/

/-- Level at 45 m, 50 m/s east, from 400 m west of the 40 m building. -/
def levelTraj (n : Nat) : State := ⟨-200 + n * (25/2), 200, 45, 50, 0, 0, 55, 0⟩

/-- A never-triggering filter violates `NeverHits`: this envelope-obeying flight hits the building. -/
theorem neverTrigger_unsafe : ¬ NeverHits P0 (fun _ _ _ => .free) := by
  intro h
  have hinit : Init P0 (levelTraj 0) := by decide +kernel
  have hA : ∀ n, Allowed P0 (appliedAt (fun _ _ _ => .free) levelTraj (fun _ => Stick.hold) n)
      (levelTraj n) Stick.hold (levelTraj (n + 1)) := by
    intro n
    simp only [appliedAt, Allowed, Common, ModeOK, levelTraj, P0, absR]
    push_cast
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
  have := h (fun _ => .hold) levelTraj hinit hA 33 (425/2) 200 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- The monitor rejects sinking faster than the escape allows, and accepts the climb. -/
example : monitor P0 (.escape 10 (climbTraj 0)) (climbTraj 10) .hold
    ⟨100, 200, 40, 0, 0, -1, 55, 0⟩ = false := by decide +kernel
example : monitor P0 (.escape 10 (climbTraj 0)) (climbTraj 10) .hold (climbTraj 11) = true := by
  decide +kernel
/-- ... and a climb-out that strays beyond `climbR` of its entry point. -/
example : monitor P0 (.climbOut (climbTraj 0)) (climbTraj 10) .hold
    ⟨201, 200, 41, 0, 0, 4, 55, 0⟩ = false := by decide +kernel

/-! ### Executable test: the closed loop against a plant that takes the envelope's bounds -/

/-- Next state of a worst-case plant: it sinks, slows and banks as much as allowed and drifts
sideways at the largest allowed rate. -/
def worstStep {ι : Type} (P : Params ι) (m : Mode) (u : ι) (s : State) : State :=
  match m with
  | .free =>
    let f := P.free u
    ⟨s.x + P.dt * s.vx, s.y + P.dt * s.vy, s.h + P.dt * (s.vz - f.vzDrop) - P.hSlack, s.vx, s.vy,
      s.vz - f.vzDrop, s.V - f.vDrop, s.bank + f.bankStep⟩
  | .escape k ref =>
    let R := Ref.ofState ref
    let σ := sched P R (k + 1)
    let vx' := scaleHi P ref.vx
    let vy' := scaleHi P ref.vy + σ.sp
    let vz' := σ.vz
    ⟨s.x + P.dt * min s.vx vx', s.y + P.dt * min s.vy vy', s.h + P.dt * min s.vz vz' - P.hSlack,
      vx', vy', vz', VFloor P R, bankCap P R (k + 1)⟩
  | .climbOut _ =>
    ⟨s.x, s.y, s.h + P.dt * min s.vz P.climbVz - P.hSlack, 0, 0, P.climbVz, s.V, 0⟩

def runLoop {ι : Type} (P : Params ι) (pilot : Nat → ι) : Nat → Nat → Mode → State →
    List (Nat × Mode × State × State)
  | 0, _, _, _ => []
  | n + 1, t, m, s =>
    let a := filter P m s (pilot t)
    let s' := worstStep P a (pilot t) s
    (t, a, s, s') :: runLoop P pilot n (t + 1) a.advance s'

/-- Hold course from 400 m west of the building at 45 m. -/
def demo := runLoop P0 (fun _ => Stick.hold) 120 0 .free sFar

#guard demo.all fun (_, a, s, s') => monitor P0 a s .hold s' -- every tick obeys the envelope
#guard demo.all fun (_, _, s, s') => tickOK P0 (Box.point s) (Box.point s') -- and clears the grid
#guard (demo.findIdx? fun (_, a, _, _) => a != .free).isSome -- the filter overrides
#guard demo.any fun (_, a, _, _) => match a with | .climbOut _ => true | _ => false -- and climbs out

/-! ### Hand-back -/

/-- From an escape, a certified input is passed. -/
example : filter P0 (.escape 5 sFar) sAway .hold = .free := by decide +kernel
/-- An uncertified input keeps the escape. -/
example : filter P0 (.escape 5 sFar) sTo .hold = .escape 5 sFar := by decide +kernel

end Envelope3D.Checks
