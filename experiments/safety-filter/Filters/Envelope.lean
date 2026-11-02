import Filters.Generic
import ExpEnvelope

/-! The performance-envelope filter (`ExpEnvelope.filter`) as a `SafetyFilter`, for well-formed
parameters `P`. The filter state is the mode carried into the tick. The applied command is the pair
(applied mode, pilot input): in free flight the plant flies the pilot's input, in an escape it flies
the escape and `Allowed` ignores the input. The guarantee is `never_hit`'s induction, stopped at `N`;
`never_hit` and `never_hit_substeps` are recovered below. -/

namespace Filters
open ExpEnvelope

variable {ι : Type}

/-- One tick of the envelope filter: the mode it applies, and the mode carried into the next tick. -/
def envelopeTick (P : Params ι) (m : Mode) (s : ExpEnvelope.State) (u : ι) : Mode × (Mode × ι) :=
  let a := ExpEnvelope.filter P m s u
  (a.advance, (a, u))

theorem envelope_fstateAt (P : Params ι) (s : Nat → ExpEnvelope.State) (pilot : Nat → ι) :
    ∀ n, fstateAt .free (envelopeTick P) s pilot n = modeAt (ExpEnvelope.filter P) s pilot n
  | 0 => rfl
  | n + 1 => by
    simp only [fstateAt, modeAt, envelopeTick, envelope_fstateAt P s pilot n]

theorem envelope_cmdAt (P : Params ι) (s : Nat → ExpEnvelope.State) (pilot : Nat → ι) (n : Nat) :
    cmdAt .free (envelopeTick P) s pilot n = (appliedAt (ExpEnvelope.filter P) s pilot n, pilot n) := by
  simp only [cmdAt, envelopeTick, appliedAt, envelope_fstateAt]

/-- `never_hit`'s induction stopped at tick `N`: if the first `N` transitions obey the envelope,
those `N` ticks clear terrain. -/
theorem envelope_guarantee (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι)
    (s : Nat → ExpEnvelope.State) (N : Nat) (h0 : ExpEnvelope.Init P (s 0))
    (hA : ∀ n < N, ExpEnvelope.Allowed P (appliedAt (ExpEnvelope.filter P) s pilot n) (s n) (pilot n)
      (s (n + 1))) :
    ∀ n < N, TickClear P (s n) (s (n + 1)) := by
  have inv : ∀ n, n ≤ N → LoopInv P (modeAt (ExpEnvelope.filter P) s pilot n) (s n) := by
    intro n
    induction n with
    | zero => intro _; exact escapeOK_sound P hP h0
    | succ n ih =>
      intro hn
      exact (filter_tick P hP (ih (Nat.le_of_succ_le hn)) (hA n hn)).2
  exact fun n hn => (filter_tick P hP (inv n (Nat.le_of_lt hn)) (hA n hn)).1

/-- `ExpEnvelope.filter P` behind the common interface. -/
def envelopeFilter (P : Params ι) (hP : P.WellFormed) : SafetyFilter where
  State := ExpEnvelope.State
  Input := ι
  Command := Mode × ι
  FState := Mode
  init := .free
  tick := envelopeTick P
  Allowed := fun s c s' => ExpEnvelope.Allowed P c.1 s c.2 s'
  monitor := fun s c s' => ExpEnvelope.monitor P c.1 s c.2 s'
  monitor_iff := fun s c s' => monitor_iff P c.1 s c.2 s'
  Init := ExpEnvelope.Init P
  Safe := TickClear P
  guarantee := by
    intro pilot s N h0 hA
    refine envelope_guarantee P hP pilot s N h0 fun n hn => ?_
    have := hA n hn
    rw [envelope_cmdAt] at this
    exact this

/-- The substep strengthening: `substepOK` on a clear tick makes every substep clear terrain. -/
def envelopeSubsteps (P : Params ι) (hP : P.WellFormed) : SubstepCheck (envelopeFilter P hP) where
  Sub := ExpEnvelope.State
  check := substepOK P
  SafeSub := fun p => P.terrain.heightAt p.x + P.margin < p.h
  sound := fun _ _ _ hT hS => substep_clear P hT hS

/-- The interface recovers `never_hit`. -/
theorem envelope_recovers_never_hit (P : Params ι) (hP : P.WellFormed) :
    NeverHits P (ExpEnvelope.filter P) := by
  intro pilot s h0 hA
  refine (envelopeFilter P hP).always_safe pilot s h0 fun n => ?_
  show ExpEnvelope.Allowed P (cmdAt .free (envelopeTick P) s pilot n).1 (s n)
    (cmdAt .free (envelopeTick P) s pilot n).2 (s (n + 1))
  rw [envelope_cmdAt]
  exact hA n

/-- The interface recovers `never_hit_substeps`, here up to the first rejected tick. -/
theorem envelope_recovers_never_hit_substeps (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι)
    (s : Nat → ExpEnvelope.State) (N : Nat) (h0 : ExpEnvelope.Init P (s 0))
    (hA : ∀ n < N, ExpEnvelope.Allowed P (appliedAt (ExpEnvelope.filter P) s pilot n) (s n) (pilot n)
      (s (n + 1)))
    (subs : Nat → List ExpEnvelope.State) (hS : ∀ n < N, substepOK P (s n) (s (n + 1)) (subs n) = true) :
    ∀ n < N, ∀ p ∈ subs n, P.terrain.heightAt p.x + P.margin < p.h :=
  (envelopeSubsteps P hP).safe_of_checks pilot s N h0
    (fun n hn => by
      show ExpEnvelope.Allowed P (cmdAt .free (envelopeTick P) s pilot n).1 (s n)
        (cmdAt .free (envelopeTick P) s pilot n).2 (s (n + 1))
      rw [envelope_cmdAt]
      exact hA n hn)
    subs hS

end Filters
