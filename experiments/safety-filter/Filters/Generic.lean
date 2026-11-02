import Filters.Interface

/-! Filter-agnostic consequences of the interface: the unbounded guarantee, a runner that threads
the filter state over an observed trace the way a host does, and its monitored guarantee. -/

namespace Filters.SafetyFilter
variable (F : SafetyFilter)

/-- Command `F` applies during tick `n` of the closed loop. -/
abbrev cmd (pilot : Nat → F.Input) (s : Nat → F.State) (n : Nat) : F.Command :=
  cmdAt F.init F.tick s pilot n

/-- The guarantee for an unbounded run: if every transition obeys `Allowed`, every tick is safe. -/
theorem always_safe (pilot : Nat → F.Input) (s : Nat → F.State) (h0 : F.Init (s 0))
    (hA : ∀ n, F.Allowed (s n) (F.cmd pilot s n) (s (n + 1))) :
    ∀ n, F.Safe (s n) (s (n + 1)) :=
  fun n => F.guarantee pilot s (n + 1) h0 (fun k _ => hA k) n (Nat.lt_succ_self n)

/-- The runtime guarantee: while the monitor accepts every transition, every tick is safe. -/
theorem safe_while_monitored (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat)
    (h0 : F.Init (s 0)) (hM : ∀ n < N, F.monitor (s n) (F.cmd pilot s n) (s (n + 1)) = true) :
    ∀ n < N, F.Safe (s n) (s (n + 1)) :=
  F.guarantee pilot s N h0 fun n hn => (F.monitor_iff _ _ _).1 (hM n hn)

/-- Run `F` for `k` ticks from tick `t` with filter state `fs`, over an observed trace `s`: one
record `(s t, applied command, s (t + 1))` per tick. -/
def runFrom (pilot : Nat → F.Input) (s : Nat → F.State) :
    Nat → Nat → F.FState → List (F.State × F.Command × F.State)
  | 0, _, _ => []
  | k + 1, t, fs =>
    let r := F.tick fs (s t) (pilot t)
    (s t, r.2, s (t + 1)) :: runFrom pilot s k (t + 1) r.1

/-- Run `F` over the first `N` ticks of an observed trace (a logged flight, or a live one). -/
def run (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) :
    List (F.State × F.Command × F.State) :=
  F.runFrom pilot s N 0 F.init

theorem runFrom_eq (pilot : Nat → F.Input) (s : Nat → F.State) :
    ∀ k t, F.runFrom pilot s k t (fstateAt F.init F.tick s pilot t) =
      (List.range' t k).map fun n => (s n, F.cmd pilot s n, s (n + 1))
  | 0, _ => rfl
  | k + 1, t => by
    simp only [runFrom, List.range'_succ, List.map_cons]
    rw [show (F.tick (fstateAt F.init F.tick s pilot t) (s t) (pilot t)).1 =
      fstateAt F.init F.tick s pilot (t + 1) from rfl, runFrom_eq pilot s k (t + 1)]
    rfl

/-- The runner computes the closed loop's commands: record `n` is tick `n`. -/
theorem run_eq (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) :
    F.run pilot s N = (List.range N).map fun n => (s n, F.cmd pilot s n, s (n + 1)) := by
  rw [run, show F.init = fstateAt F.init F.tick s pilot 0 from rfl, runFrom_eq, List.range_eq_range']

/-- The monitor accepts every record of a run iff the trace obeys `Allowed` on those ticks. -/
theorem run_monitor_iff (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) :
    (F.run pilot s N).all (fun r => F.monitor r.1 r.2.1 r.2.2) = true ↔
      ∀ n < N, F.Allowed (s n) (F.cmd pilot s n) (s (n + 1)) := by
  simp [run_eq, List.all_eq_true, F.monitor_iff]

/-- Every record of a run whose transitions all pass the monitor is a safe tick. -/
theorem run_safe (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) (h0 : F.Init (s 0))
    (hM : (F.run pilot s N).all (fun r => F.monitor r.1 r.2.1 r.2.2) = true) :
    ∀ r ∈ F.run pilot s N, F.Safe r.1 r.2.2 := by
  have hsafe := F.guarantee pilot s N h0 ((F.run_monitor_iff pilot s N).1 hM)
  intro r hr
  rw [run_eq] at hr
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hr
  exact hsafe n (List.mem_range.1 hn)

end Filters.SafetyFilter

namespace Filters.SubstepCheck

/-- The substep strengthening along the closed loop: while every transition obeys `Allowed` and
the host's check accepts every tick's substeps, every substep is safe. -/
theorem safe_of_checks {F : SafetyFilter} (X : SubstepCheck F)
    (pilot : Nat → F.Input) (s : Nat → F.State) (N : Nat) (h0 : F.Init (s 0))
    (hA : ∀ n < N, F.Allowed (s n) (F.cmd pilot s n) (s (n + 1)))
    (subs : Nat → List X.Sub) (hS : ∀ n < N, X.check (s n) (s (n + 1)) (subs n) = true) :
    ∀ n < N, ∀ p ∈ subs n, X.SafeSub p :=
  fun n hn => X.sound _ _ _ (F.guarantee pilot s N h0 hA n hn) (hS n hn)

end Filters.SubstepCheck
