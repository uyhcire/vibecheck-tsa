import ExpVibecheck.Model

/-! The safety specification. -/

namespace ExpVibecheck

structure Certificate where
  inS : State → Bool
  filter : State → Input → Input
  init_sub : ∀ s, Init s → inS s
  safe : ∀ s, inS s → ¬ s.crashed
  admissible : ∀ s u, (filter s u).Admissible
  invariant : ∀ s u, inS s → inS (step s (filter s u))
  passthrough : ∀ s u, inS s → u.Admissible → inS (step s u) → filter s u = u

def traj (C : Certificate) (s₀ : State) (pilot : Nat → Input) : Nat → State
  | 0 => s₀
  | n + 1 => let s := traj C s₀ pilot n; step s (C.filter s (pilot n))

theorem traj_inS (C : Certificate) (s₀ : State) (h₀ : Init s₀) (pilot : Nat → Input) :
    ∀ n, C.inS (traj C s₀ pilot n) = true
  | 0 => C.init_sub s₀ h₀
  | n + 1 => C.invariant _ _ (traj_inS C s₀ h₀ pilot n)

theorem never_crash (C : Certificate) (s₀ : State) (h₀ : Init s₀) (pilot : Nat → Input) :
    ∀ n, ¬ (traj C s₀ pilot n).crashed :=
  fun n => C.safe _ (traj_inS C s₀ h₀ pilot n)

end ExpVibecheck
