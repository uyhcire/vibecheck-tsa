import Ci.proof.SafeCells

/-! The band part of the side conditions at the image: from every state in T, the tick's end state and memory pass
`bandOk` (altitude band, stall bit, stored α command). -/

namespace Ci.Proof.SafeIv
open Vibecheck Jsb Ci.Lawfirst

/-- A substep sequence that ends with its safety flag up ends in a `safeOk` state. -/
theorem subT_final_safe (u : Input) : ∀ (n : Nat) (s : State) (ok cl : Bool),
    (Ci.subT u (n + 1) s ok cl).2.1 = true → Ci.safeOk (Ci.subT u (n + 1) s ok cl).1 = true := by
  intro n
  induction n with
  | zero =>
    intro s ok cl h
    simp only [Ci.subT, Bool.and_eq_true] at h ⊢
    exact h.2
  | succ n ih =>
    intro s ok cl h
    exact ih _ _ _ h

theorem alphaCmd_bounds (s : State) : -6000 ≤ alphaCmd p1 s ∧ alphaCmd p1 s ≤ 15000 := by
  have k : ∀ aN raw : Int, -6000 ≤ max p1.aMin (min (min p1.aMax aN) raw) ∧
      max p1.aMin (min (min p1.aMax aN) raw) ≤ 15000 := by
    intro aN raw
    have e3 : p1.aMin = -6000 := rfl
    have e4 : p1.aMax = 15000 := rfl
    rw [e3, e4]; omega
  exact k _ _

theorem ac_next (s : State) (m : Mem) (hm : -900000 ≤ m.ac ∧ m.ac ≤ 900000) :
    -900000 ≤ (lawT.step m s).2.ac ∧ (lawT.step m s).2.ac ≤ 900000 := by
  have hb := alphaCmd_bounds s
  have e1 : p1.rDn = 1000000 := rfl
  have e2 : p1.rUp = 1000000 := rfl
  show -900000 ≤ clampI (m.ac - p1.rDn) (m.ac + p1.rUp) (alphaCmd p1 s) ∧
    clampI (m.ac - p1.rDn) (m.ac + p1.rUp) (alphaCmd p1 s) ≤ 900000
  rw [e1, e2]
  unfold clampI
  constructor <;> omega

/-- From every state in T, the image passes `bandOk`. -/
theorem band_next (s : State) (m : Mem) (hT : lawT.inT (s, m) = true) :
    bandOk ((Ci.tickT lawT s m).s, (Ci.tickT lawT s m).m) = true := by
  have hh := tick_band_h s m hT
  have hsafe := (tick_safe_climb s m hT).1
  have hb0 : bandOk (s, m) = true := by
    have : inT (s, m) = true := hT
    unfold inT restOk at this; simp only [Bool.and_eq_true] at this; exact this.1.1.1
  unfold bandOk at hb0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb0
  have hac := ac_next s m ⟨hb0.1.2, hb0.2⟩
  have hfin : (Ci.subT (Ci.clampInput (lawT.step m s).1) 8 s true true).2.1 = true →
      Ci.safeOk (Ci.subT (Ci.clampInput (lawT.step m s).1) 8 s true true).1 = true :=
    subT_final_safe _ 7 s true true
  dsimp only [Ci.tickT] at hh hsafe ⊢
  generalize Ci.subT (Ci.clampInput (lawT.step m s).1) 8 s true true = res at hh hsafe hfin ⊢
  obtain ⟨s', ok', cl'⟩ := res
  dsimp only at hh hsafe hfin ⊢
  have hf := hfin hsafe
  unfold Ci.safeOk Ci.envOk at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  unfold bandOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨hh.1, hh.2⟩, hf.1.1.2⟩, hac.1⟩, hac.2⟩

end Ci.Proof.SafeIv
