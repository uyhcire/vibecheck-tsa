import Filters.Generic
import ExpVibecheck

/-! The toy sim's rollout filter (`ExpVibecheck.solution`) as a `SafetyFilter`: deterministic plant
`s' = step s u`, no filter state. The guarantee is `flight_never_crashes`, re-indexed. -/

namespace Filters
open ExpVibecheck

/-- `ExpVibecheck.solution` behind the common interface. -/
def rolloutFilter : SafetyFilter where
  State := ExpVibecheck.State
  Input := ExpVibecheck.Input
  Command := ExpVibecheck.Input
  FState := Unit
  init := ()
  tick := fun _ s u => ((), ExpVibecheck.filter s u)
  Allowed := fun s u s' => s' = step s u
  monitor := fun s u s' => decide (s' = step s u)
  monitor_iff := fun _ _ _ => decide_eq_true_iff
  Init := ExpVibecheck.Init
  Safe := fun s s' => ¬ s.crashed ∧ ¬ s'.crashed
  guarantee := by
    intro pilot s N h0 hA
    -- On the first `N` ticks the trajectory is `traj solution (s 0) pilot`.
    have htraj : ∀ n, n ≤ N → s n = traj solution (s 0) pilot n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [hA n hn]
        show step (s n) (ExpVibecheck.filter (s n) (pilot n)) = _
        rw [ih (Nat.le_of_succ_le hn)]
        rfl
    intro n hn
    rw [htraj n (Nat.le_of_lt hn), htraj (n + 1) hn]
    exact ⟨flight_never_crashes (s 0) h0 pilot n, flight_never_crashes (s 0) h0 pilot (n + 1)⟩

/-- The rollout filter's guarantee, as a named theorem for the axiom audit. -/
theorem rollout_guarantee : ∀ (pilot : Nat → ExpVibecheck.Input) (s : Nat → ExpVibecheck.State) (N : Nat),
    ExpVibecheck.Init (s 0) →
    (∀ n < N, s (n + 1) = step (s n) (ExpVibecheck.filter (s n) (pilot n))) →
    ∀ n < N, ¬ (s n).crashed ∧ ¬ (s (n + 1)).crashed :=
  rolloutFilter.guarantee

/-- The interface recovers `flight_never_crashes` on the deterministic closed loop `traj`. -/
theorem rollout_recovers_flight_never_crashes (s₀ : ExpVibecheck.State) (h₀ : ExpVibecheck.Init s₀)
    (pilot : Nat → ExpVibecheck.Input) (n : Nat) : ¬ (traj solution s₀ pilot n).crashed :=
  (rolloutFilter.always_safe pilot (traj solution s₀ pilot) h₀ (fun _ => rfl) n).1

end Filters
