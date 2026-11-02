import Ci.Rules
import Ci.Init

/-! Scoreboard-owned. -/

namespace Ci.Goals
open ExpVibecheck ExpJsb Ci

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

/-! ### Reachability semantics

Only states that can occur count. They are those reachable from `Init`, a small explicit set of trims
(`Ci/Init.lean`), by ticks of the plant under clamped inputs. A law's closed-loop pairs are those it starts
from a reachable state, closed under its own ticks. The R goals quantify over these pairs only. -/

/-- State of a `Ci.Init.rows` row (the 19 raw fields in `Ci.stateRaw` order). -/
def initState (v : Array Int) : State :=
  let f (i : Nat) : Fx := ⟨v[i]!⟩
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩

/-- Trim input of a `Ci.Init.rows` row (elevator, throttle). -/
def initInput (v : Array Int) : Input := ⟨⟨v[19]!⟩, ⟨v[20]!⟩, ⟨0⟩, ⟨0⟩⟩

def Init (s : State) : Prop := ∃ v ∈ Ci.Init.rows.toList, s = initState v

/-- Plant states reachable from `Init` under any clamped pilot input, one formal-model tick at a time. The
filter's escape inputs are clamped inputs too, so this covers its own interventions. -/
inductive PlantReach : State → Prop
  | init {s : State} : Init s → PlantReach s
  | step {s : State} (u : Input) : PlantReach s → PlantReach (ExpJsb.tickAB (clampInput u) s)

/-- Closed-loop pairs of law `L`: started at any reachable state (with any clamped last pilot input), then
closed under the law's own ticks. -/
inductive ReachCL (L : Law) : State × L.σ → Prop
  | init {s : State} (u : Input) : PlantReach s → ReachCL L (s, L.init ⟨s, clampInput u⟩)
  | step {p : State × L.σ} : ReachCL L p → ReachCL L ((tickT L p.1 p.2).s, (tickT L p.1 p.2).m)

/-- `TSafe` restricted to reachable closed-loop pairs. -/
def TSafeR (L : Law) : Prop :=
  ∀ s m, ReachCL L (s, m) → L.inT (s, m) = true →
    (∀ k, (tickT L (traj L k (s, m)).1 (traj L k (s, m)).2).safe = true) ∧
    ∃ K, ∀ k, K ≤ k → (tickT L (traj L k (s, m)).1 (traj L k (s, m)).2).climb = true

/-- `TInvariant` restricted to reachable closed-loop pairs. -/
def TInvariantR (L : Law) : Prop :=
  ∀ s m, ReachCL L (s, m) → L.inT (s, m) = true →
    (tickT L s m).safe = true ∧ (tickT L s m).climb = true ∧ L.inT ((tickT L s m).s, (tickT L s m).m) = true

theorem tSafeR_of_tSafe (L : Law) (h : TSafe L) : TSafeR L := fun s m _ hT => h s m hT

theorem tInvariantR_of_tInvariant (L : Law) (h : TInvariant L) : TInvariantR L := fun s m _ hT => h s m hT

theorem traj_reach (L : Law) (p : State × L.σ) (hp : ReachCL L p) : ∀ k, ReachCL L (traj L k p) := by
  intro k
  induction k with
  | zero => exact hp
  | succ k ih => rw [traj_succ]; exact ReachCL.step ih

theorem traj_memR (L : Law) (h : TInvariantR L) (s : State) (m : L.σ) (hR : ReachCL L (s, m))
    (hT : L.inT (s, m) = true) : ∀ k, L.inT (traj L k (s, m)) = true := by
  intro k
  induction k with
  | zero => exact hT
  | succ k ih =>
    rw [traj_succ]
    exact (h _ _ (traj_reach L (s, m) hR k) ih).2.2

theorem tSafeR_of_tInvariantR (L : Law) (h : TInvariantR L) : TSafeR L := by
  intro s m hR hT
  refine ⟨fun k => (h _ _ (traj_reach L (s, m) hR k) (traj_memR L h s m hR hT k)).1, 0,
    fun k _ => (h _ _ (traj_reach L (s, m) hR k) (traj_memR L h s m hR hT k)).2.1⟩

/-- A reachable state: every `Init` row is in `Init`. -/
example : Init (initState Ci.Init.r0) := ⟨Ci.Init.r0, List.mem_cons_self .., rfl⟩

end Ci.Goals
