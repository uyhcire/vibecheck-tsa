import GateSafety.Proofs

/-! A toy instance: `safe` with every assumption discharged, and with an unsound end-of-escape test, a crash. -/

namespace GateSafety.Checks

/-- Altitude and climb rate; the input sets the climb rate. Controllers: `some u` flies `u` for one frame, then
the escape; `none` is the escape, which adds 1 to the climb rate each frame. The pilot is the only candidate. -/
def toy : Gate (Int × Int) Int (Option Int) Unit where
  step s u := (s.1 + u, u)
  ctl l s := match l with | some u => (u, none) | none => (s.2 + 1, none)
  clear x := decide (0 < x.2.1)
  term x := decide (x.1 = none ∧ 0 < x.2.1 ∧ 0 ≤ x.2.2)
  horizon := 20
  propose _ _ _ u := [some u]
  update _ _ _ _ _ := ()
  start _ := none
  m₀ := ()

abbrev crash (s : Int × Int) : Prop := s.1 ≤ 0
abbrev init (s : Int × Int) : Prop := s = (5, 0)

theorem toy_term : TermSound toy crash := by
  intro x hx k
  induction k generalizing x with
  | zero => obtain ⟨l, h, v⟩ := x; simp [toy, crash, Gate.flyN] at hx ⊢; omega
  | succ k ih =>
    obtain ⟨l, h, v⟩ := x
    simp [toy] at hx
    obtain ⟨rfl, hh, hv⟩ := hx
    exact ih _ (by simp [toy, Gate.fly]; omega)

example : Safe toy crash init :=
  safe toy crash init (fun x h => by simp [toy, crash] at h ⊢; omega) toy_term (fun _ h => by subst h; decide)

/-- With an end-of-escape test that accepts everything, a pilot diving at 4 per frame crashes on frame 2. -/
example : ¬ Safe { toy with term := fun _ => true } crash init :=
  fun h => h _ (.step (-4) (.step (-4) (.init (s := (5, 0)) rfl))) (by decide)

end GateSafety.Checks
