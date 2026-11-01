import Ci.Rules

/-! Scoreboard-owned. -/

namespace Ci.Goals
open Vibecheck Jsb Ci

def traj (L : Law) : Nat → State × L.σ → State × L.σ
  | 0, p => p
  | k + 1, p => let q := traj L k p; ((tickT L q.1 q.2).s, (tickT L q.1 q.2).m)

def TSafe (L : Law) : Prop :=
  ∀ s m, L.inT (s, m) = true →
    (∀ k, (tickT L (traj L k (s, m)).1 (traj L k (s, m)).2).safe = true) ∧
    ∃ K, ∀ k, K ≤ k → (tickT L (traj L k (s, m)).1 (traj L k (s, m)).2).climb = true

def TInvariant (L : Law) : Prop :=
  ∀ s m, L.inT (s, m) = true →
    (tickT L s m).safe = true ∧ (tickT L s m).climb = true ∧ L.inT ((tickT L s m).s, (tickT L s m).m) = true

theorem traj_succ (L : Law) (k : Nat) (p : State × L.σ) :
    traj L (k + 1) p = (let q := traj L k p; ((tickT L q.1 q.2).s, (tickT L q.1 q.2).m)) := by
  rfl

theorem traj_mem (L : Law) (h : TInvariant L) (s : State) (m : L.σ) (hT : L.inT (s, m) = true) :
    ∀ k, L.inT (traj L k (s, m)) = true := by
  intro k
  induction k with
  | zero => exact hT
  | succ k ih =>
    rw [traj_succ]
    exact (h _ _ ih).2.2

theorem tSafe_of_tInvariant (L : Law) (h : TInvariant L) : TSafe L := by
  intro s m hT
  refine ⟨fun k => (h _ _ (traj_mem L h s m hT k)).1, 0, fun k _ => (h _ _ (traj_mem L h s m hT k)).2.1⟩

end Ci.Goals
