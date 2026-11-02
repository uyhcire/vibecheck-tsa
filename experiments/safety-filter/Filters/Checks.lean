import Filters.Rollout
import Filters.Envelope
import Filters.Conversion

/-! Concrete checks: each instance's hypotheses are satisfiable, the interface used polymorphically,
the interface's guarantee rejects a never-triggering filter, and the double conversion on examples. -/

namespace Filters.Checks
open Filters

/-! ### Rollout instance: hypotheses discharged on a concrete closed loop -/

/-- Full throttle, stick back after 6 s. -/
def takeoff : Nat → ExpVibecheck.Input := fun t => ⟨if t < 96 then 0 else 1/2, 1, false⟩

example : ExpVibecheck.Init ExpVibecheck.initState := by decide

/-- `rollout_guarantee` with every hypothesis discharged: the closed loop obeys `Allowed` by
construction (`traj` is `step` under the filter's command). -/
example (N : Nat) : ∀ n < N, ¬ (ExpVibecheck.traj ExpVibecheck.solution ExpVibecheck.initState takeoff n).crashed ∧
    ¬ (ExpVibecheck.traj ExpVibecheck.solution ExpVibecheck.initState takeoff (n + 1)).crashed :=
  rollout_guarantee takeoff _ N (by decide) fun _ _ => rfl

/-! ### ExpEnvelope instance: the existing `ExpEnvelope.Checks` witnesses -/

open ExpEnvelope.Checks in
theorem climb_cmd_allowed (n : Nat) :
    (envelopeFilter P0 P0_wf).Allowed (climbTraj n) ((envelopeFilter P0 P0_wf).cmd climbPilot climbTraj n)
      (climbTraj (n + 1)) := by
  show ExpEnvelope.Allowed P0 (cmdAt .free (envelopeTick P0) climbTraj climbPilot n).1 (climbTraj n)
    (cmdAt .free (envelopeTick P0) climbTraj climbPilot n).2 (climbTraj (n + 1))
  rw [envelope_cmdAt]
  exact climb_allowed n

open ExpEnvelope.Checks in
/-- The envelope instance's guarantee with every hypothesis discharged. -/
example : ∀ n, ExpEnvelope.TickClear P0 (climbTraj n) (climbTraj (n + 1)) :=
  (envelopeFilter P0 P0_wf).always_safe climbPilot climbTraj climb_init climb_cmd_allowed

open ExpEnvelope.Checks in
/-- The substep strengthening with every hypothesis discharged. -/
example (N : Nat) : ∀ n < N, ∀ p ∈ climbSubs n, P0.terrain.heightAt p.x + P0.margin < p.h :=
  (envelopeSubsteps P0 P0_wf).safe_of_checks climbPilot climbTraj N climb_init
    (fun n _ => climb_cmd_allowed n) climbSubs fun n _ => by
      show ExpEnvelope.substepOK P0 _ _ _ = true
      simp only [ExpEnvelope.substepOK, climbSubs, climbTraj, P0, List.all_cons, List.all_nil,
        Bool.and_true]
      push_cast; grind

/-! ### Polymorphic use: one runner and one theorem for every filter -/

/-- Ticks of a run where the filter's command is not the pilot's own (for any filter whose command
type is its input type, given a way to compare). -/
def overrides (F : SafetyFilter) (toCmd : F.Input → F.Command) [beq : BEq F.Command]
    (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) : List Nat :=
  ((F.run pilot s N).zip (List.range N)).filterMap fun (r, n) =>
    if r.2.1 == toCmd (pilot n) then none else some n

/-- For any filter: on a logged trace that starts in `Init` and passes the monitor on every tick, every
logged tick is safe. -/
example (F : SafetyFilter) (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) (h0 : F.Init (s 0))
    (hM : (F.run pilot s N).all (fun r => F.monitor r.1 r.2.1 r.2.2) = true) :
    ∀ r ∈ F.run pilot s N, F.Safe r.1 r.2.2 :=
  F.run_safe pilot s N h0 hM

open ExpEnvelope.Checks in
/-- `run_safe` on the envelope instance: the logged climb passes the monitor, so its ticks are safe. -/
example : ∀ r ∈ (envelopeFilter P0 P0_wf).run climbPilot climbTraj 8,
    ExpEnvelope.TickClear P0 r.1 r.2.2 :=
  (envelopeFilter P0 P0_wf).run_safe climbPilot climbTraj 8 climb_init
    (((envelopeFilter P0 P0_wf).run_monitor_iff _ _ _).2 fun n _ => climb_cmd_allowed n)

/-- The first `N + 1` states of the rollout filter's closed loop on the takeoff, computed once. -/
def takeoffStates (N : Nat) : Array ExpVibecheck.State :=
  (List.range N).foldl (init := #[ExpVibecheck.initState]) fun a t =>
    let s := a.back!
    a.push (ExpVibecheck.step s (ExpVibecheck.filter s (takeoff t)))

/-- The takeoff roll's first 2 s as a host would log it, replayed through the rollout filter. -/
def takeoffLog : List (ExpVibecheck.State × ExpVibecheck.Input × ExpVibecheck.State) :=
  let states := takeoffStates 32
  rolloutFilter.run takeoff (fun n => states[n]!) 32

#guard takeoffLog.length == 32
#guard takeoffLog.all fun r => rolloutFilter.monitor r.1 r.2.1 r.2.2 -- the log is `step` under the filter
#guard takeoffLog.all fun r => !decide r.1.crashed && !decide r.2.2.crashed -- `Safe` on every tick

-- The same metric on both filters: the takeoff roll is never overridden ...
#guard (let states := takeoffStates 32
  overrides rolloutFilter id takeoff (fun n => states[n]!) 32
    (beq := inferInstanceAs (BEq ExpVibecheck.Input))).isEmpty
-- ... and the dive into the climb below the ridge is overridden on every tick.
open ExpEnvelope.Checks in
#guard overrides (envelopeFilter P0 P0_wf) (fun u => (.free, u)) climbPilot climbTraj 8
    (beq := inferInstanceAs (BEq (ExpEnvelope.Mode × Stick))) == List.range 8

/-! ### The interface's guarantee rejects a filter that never intervenes -/

open ExpEnvelope.Checks in
/-- A tick that always passes the pilot's input: with the envelope's plant model, initial set and
safety predicate, its `guarantee` statement is false (via `neverTrigger_unsafe`). -/
example : ¬ (∀ (pilot : Nat → Stick) (s : Nat → ExpEnvelope.State) (N : Nat), ExpEnvelope.Init P0 (s 0) →
    (∀ n < N, ExpEnvelope.Allowed P0
        (cmdAt (ExpEnvelope.Mode.free) (fun m _ u => (m, (ExpEnvelope.Mode.free, u))) s pilot n).1 (s n)
        (cmdAt (ExpEnvelope.Mode.free) (fun m _ u => (m, (ExpEnvelope.Mode.free, u))) s pilot n).2 (s (n + 1))) →
    ∀ n < N, ExpEnvelope.TickClear P0 (s n) (s (n + 1))) := by
  intro h
  apply neverTrigger_unsafe
  intro pilot s h0 hA n
  exact h pilot s (n + 1) h0 (fun k _ => hA k) n (Nat.lt_succ_self n)

/-! ### Double → `Rat`: `ratOfBits` inverts the reference encoding -/

example : bitsOf false 1019 0x999999999999A = 0x3FB999999999999A := by decide
example : ratOfBits (bitsOf false 1023 0) = some 1 := by decide +kernel
example : ratOfBits (bitsOf false 1023 0) = some (valueOf false 1023 0) := by decide +kernel
/-- The double nearest 0.1 ... -/
example : ratOfBits (bitsOf false 1019 0x999999999999A) = some (3602879701896397 / 36028797018963968) := by
  decide +kernel
example : ratOfBits (bitsOf false 1019 0x999999999999A) = some (valueOf false 1019 0x999999999999A) := by
  decide +kernel
/-- ... is not 1/10: the conversion is exact, not a decimal reading. -/
example : ratOfBits (bitsOf false 1019 0x999999999999A) ≠ some (1 / 10) := by decide +kernel
example : ratOfBits (bitsOf true 1024 0x4000000000000) = some (-5 / 2) := by decide +kernel
example : ratOfBits (bitsOf true 1024 0x4000000000000) = some (valueOf true 1024 0x4000000000000) := by
  decide +kernel
/-- Smallest subnormal, largest finite double, ±0. -/
example : ratOfBits (bitsOf false 0 1) = some (valueOf false 0 1) := by decide +kernel
example : ratOfBits (bitsOf false 2046 (2 ^ 52 - 1)) = some (valueOf false 2046 (2 ^ 52 - 1)) := by
  decide +kernel
example : ratOfBits (bitsOf false 0 0) = some 0 ∧ ratOfBits (bitsOf true 0 0) = some 0 := by
  decide +kernel
/-- ±∞ and NaN have no value. -/
example : ratOfBits (bitsOf false 2047 0) = none ∧ ratOfBits (bitsOf true 2047 0) = none ∧
    ratOfBits (bitsOf false 2047 1) = none := by decide +kernel

-- Against the runtime's own encoding (`Float.toBits`, evaluated, not proved):
#guard (0.1 : Float).toBits == bitsOf false 1019 0x999999999999A
#guard ratOfFloat 0.1 == some (3602879701896397 / 36028797018963968)
#guard ratOfFloat (-2.5) == some (-5 / 2)
#guard ratOfFloat (1.0 / 0.0) == none
#guard ratOfFloat (0.0 / 0.0) == none
#guard envelopeStateOf 0 300 50 0 55 == some ExpEnvelope.Checks.s0

/-- Directed rounding into `Fx` on an example: 0.1 rounds down to 6553/65536 and up to 6554/65536. -/
example : (fxFloor (1 / 10)).raw = 6553 ∧ (fxCeil (1 / 10)).raw = 6554 := by decide +kernel

end Filters.Checks
