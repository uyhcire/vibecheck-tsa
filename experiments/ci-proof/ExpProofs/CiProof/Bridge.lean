import ExpProofs.CiProof.NodePsd

/-! The integer/real bridges of `tickInT_of_obligations`: `quadOk` (integer, with floors in the altitude
interpolation) against the real form `qf (P p) (z p)` and the radii `rIn`, `rOut`. -/

namespace ExpProofs.CiProof.Skel
open Matrix Ci.Proof

theorem quad_eq (Q : Array (Array Int)) (d : Array Int) :
    quad Q d = ∑ i : Fin 7, ∑ j : Fin 7, (Q[i.val]!)[j.val]! * d[i.val]! * d[j.val]! := by
  simp [quad, List.range_succ, Fin.sum_univ_seven]
  ring

theorem qf_pNode (j : Nat) (x : Fin 7 → ℝ) :
    qf (pNode j) x = ∑ a : Fin 7, ∑ b : Fin 7, ((((TData.pTab[j]!)[a.val]!)[b.val]! : Int) : ℝ) * x a * x b := by
  simp only [qf, dotProduct, mulVec, pNode, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem dSlow_get (p : ExpJsb.State × Ci.Lawfirst.Mem) (i : Fin 7) : (dSlow p)[i.val]! = dev p i.val := by
  fin_cases i <;> simp [dSlow, TData.nSlow, List.range_succ]

theorem qf_pNode_quad (j : Nat) (p : ExpJsb.State × Ci.Lawfirst.Mem) :
    qf (pNode j) (z p) = ((quad TData.pTab[j]! (dSlow p) : Int) : ℝ) := by
  rw [qf_pNode, quad_eq]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [dSlow_get, dSlow_get]; rfl

theorem qf_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) (x : Fin 7 → ℝ) :
    qf (a • A + b • B) x = a * qf A x + b * qf B x := by
  unfold qf; rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp [smul_eq_mul]

theorem qf_smul (A : Matrix (Fin 7) (Fin 7) ℝ) (a : ℝ) (x : Fin 7 → ℝ) : qf (a • A) x = a * qf A x := by
  unfold qf; rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem nodeF_range {h : Int} (h0 : 0 ≤ h) : 0 ≤ nodeF h ∧ nodeF h < 100 * 65536 := by
  unfold nodeF nodeJ
  have hq : 0 ≤ h / (100 * 65536) := Int.ediv_nonneg h0 (by decide)
  rw [Int.toNat_of_nonneg hq]
  constructor <;> omega

/-- The real form, scaled by 2^K, is the exact interpolation of the two node forms. -/
theorem qf_P_scaled (p : ExpJsb.State × Ci.Lawfirst.Mem) (h0 : 0 ≤ p.1.h.raw) :
    (2 : ℝ) ^ TData.pK * qf (P p) (z p) =
      (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p) : ℝ) +
        ((quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p) : ℝ) - (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p) : ℝ)) *
          ((nodeF p.1.h.raw : ℝ) / (100 * 65536)) := by
  obtain ⟨f0, f1⟩ := nodeF_range h0
  have hw : wt p.1.h.raw = (nodeF p.1.h.raw : ℝ) / (100 * 65536) := by
    unfold wt
    have a : (0 : ℝ) ≤ (nodeF p.1.h.raw : ℝ) / (100 * 65536) := by
      apply div_nonneg <;> [exact_mod_cast f0; norm_num]
    have b : (nodeF p.1.h.raw : ℝ) / (100 * 65536) ≤ 1 := by
      rw [div_le_one (by norm_num)]; exact_mod_cast f1.le
    rw [min_eq_right b, max_eq_right a]
  unfold P
  rw [qf_smul, qf_smul_add, qf_pNode_quad, qf_pNode_quad, hw]
  have : (2 : ℝ) ^ TData.pK ≠ 0 := by positivity
  field_simp
  ring

/-- Floor of an interpolation against its real value. -/
theorem lerp_floor (a b f : Int) (S : Int) (hS : 0 < S) :
    (lerp a b f S : ℝ) ≤ (a : ℝ) + ((b : ℝ) - a) * ((f : ℝ) / S) ∧
      (a : ℝ) + ((b : ℝ) - a) * ((f : ℝ) / S) < (lerp a b f S : ℝ) + 1 := by
  unfold lerp
  have h1 := Int.ediv_mul_le ((b - a) * f) (show S ≠ 0 by omega)
  have h2 := Int.lt_ediv_add_one_mul_self ((b - a) * f) hS
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have e1 : (((b - a) * f / S : Int) : ℝ) * S ≤ ((b - a) * f : Int) := by exact_mod_cast h1
  have e2 : (((b - a) * f : Int) : ℝ) < ((((b - a) * f / S : Int) : ℝ) + 1) * S := by exact_mod_cast h2
  push_cast at e1 e2 ⊢
  constructor
  · rw [show ((b : ℝ) - a) * (f / S) = ((b - a) * f) / S by ring]
    have := (le_div_iff₀ hS').mpr e1
    linarith
  · rw [show ((b : ℝ) - a) * (f / S) = ((b - a) * f) / S by ring]
    have := (div_lt_iff₀ hS').mpr e2
    linarith

theorem r2Tab_pos : ∀ j, j < 28 → (0 : Int) < TData.r2Tab[j]! := by decide

theorem band_h {p : ExpJsb.State × Ci.Lawfirst.Mem} (hb : bandOk p = true) : hLoT ≤ p.1.h.raw ∧ p.1.h.raw < hHiT := by
  unfold bandOk at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨hb.1.1.1.1, hb.1.1.1.2⟩

theorem nodeJ_le {h : Int} (h0 : 0 ≤ h) (h1 : h < hHiT) : nodeJ h ≤ 26 := by
  unfold nodeJ hHiT at *
  have hq : 0 ≤ h / (100 * 65536) := Int.ediv_nonneg h0 (by decide)
  omega

theorem lerp_ge_min (a b f S : Int) (hS : 0 < S) (f0 : 0 ≤ f) (f1 : f ≤ S) : min a b ≤ lerp a b f S := by
  unfold lerp
  rcases le_total a b with h | h
  · have h1 : 0 ≤ (b - a) * f := Int.mul_nonneg (by omega) f0
    have : 0 ≤ (b - a) * f / S := Int.ediv_nonneg h1 hS.le
    omega
  · have h2 : (b - a) * S ≤ (b - a) * f := Int.mul_le_mul_of_nonpos_left (by omega) f1
    have h3 : (b - a) * S / S ≤ (b - a) * f / S := Int.ediv_le_ediv hS h2
    rw [Int.mul_ediv_cancel _ (by omega)] at h3
    omega

/-- The interpolated radius² is positive in the band. -/
theorem r2At_pos {p : ExpJsb.State × Ci.Lawfirst.Mem} (hb : bandOk p = true) : 0 ≤ r2At p := by
  obtain ⟨hl, hh⟩ := band_h hb
  have h0 : 0 ≤ p.1.h.raw := le_trans (by unfold hLoT; decide) hl
  have hj := nodeJ_le h0 hh
  have r0 := r2Tab_pos (nodeJ p.1.h.raw) (by omega)
  have r1 := r2Tab_pos (nodeJ p.1.h.raw + 1) (by omega)
  obtain ⟨f0, f1⟩ := nodeF_range h0
  have := lerp_ge_min TData.r2Tab[nodeJ p.1.h.raw]! TData.r2Tab[nodeJ p.1.h.raw + 1]! (nodeF p.1.h.raw) (100 * 65536)
    (by decide) f0 f1.le
  unfold r2At
  omega

/-- The real form scaled by 2^K lies within one of the integer interpolation `quadOk` compares. -/
theorem quad_real (p : ExpJsb.State × Ci.Lawfirst.Mem) (hb : bandOk p = true) :
    (lerp (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
        (nodeF p.1.h.raw) (100 * 65536) : ℝ) ≤ (2 : ℝ) ^ TData.pK * qf (P p) (z p) ∧
      (2 : ℝ) ^ TData.pK * qf (P p) (z p) <
        (lerp (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
          (nodeF p.1.h.raw) (100 * 65536) : ℝ) + 1 := by
  obtain ⟨hl, _⟩ := band_h hb
  have h0 : 0 ≤ p.1.h.raw := le_trans (by unfold hLoT; decide) hl
  rw [qf_P_scaled p h0]
  have hf := lerp_floor (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
    (nodeF p.1.h.raw) (100 * 65536) (by decide)
  have e : (((100 * 65536 : Int)) : ℝ) = 100 * 65536 := by norm_num
  rw [e] at hf
  exact hf

theorem bridge_in (p : ExpJsb.State × Ci.Lawfirst.Mem) (hT : L.inT p = true) : side p ∧ qf (P p) (z p) ≤ rIn p ^ 2 := by
  have h : inT p = true := hT
  unfold inT restOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hb, hq⟩, hf⟩, hx⟩ := h
  refine ⟨⟨hb, hf, hx⟩, ?_⟩
  have hq' := hq
  unfold quadOk at hq'
  simp only [decide_eq_true_eq] at hq'
  have hr := r2At_pos hb
  have qr := (quad_real p hb).2
  have hq'' : (lerp (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
      (nodeF p.1.h.raw) (100 * 65536) : ℝ) ≤ (r2At p : ℝ) := by exact_mod_cast hq'
  unfold rIn
  rw [Real.sq_sqrt (by positivity)]
  rw [le_div_iff₀ (by positivity)]
  push_cast
  linarith

theorem bridge_out (p : ExpJsb.State × Ci.Lawfirst.Mem) (hs : side p) (hq : qf (P p) (z p) ≤ rOut p ^ 2) :
    L.inT p = true := by
  obtain ⟨hb, hf, hx⟩ := hs
  have hr := r2At_pos hb
  have qr := (quad_real p hb).1
  unfold rOut at hq
  rw [Real.sq_sqrt (by positivity), le_div_iff₀ (by positivity)] at hq
  have : (lerp (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
      (nodeF p.1.h.raw) (100 * 65536) : ℝ) ≤ (r2At p : ℝ) := by linarith
  have hq2 : quadOk p = true := by
    unfold quadOk
    simp only [decide_eq_true_eq]
    exact_mod_cast this
  show inT p = true
  unfold inT restOk
  simp [hb, hq2, hf, hx]

/-- `TInvariant lawT` from the two dynamics obligations alone: the image satisfies the side conditions, and the
tick has an affine enclosure in T's coordinates with a contraction certificate. -/
theorem tInvariant_of_dynamics
    (hside : ∀ s m, L.inT (s, m) = true → side ((Ci.tickT L s m).s, (Ci.tickT L s m).m))
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (e : Fin 7 → ℝ) (ρ ε : ℝ),
      z ((Ci.tickT L s m).s, (Ci.tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((Ci.tickT L s m).s, (Ci.tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((Ci.tickT L s m).s, (Ci.tickT L s m).m)) e ≤ ε ^ 2 ∧
      ρ * rIn (s, m) + ε ≤ rOut ((Ci.tickT L s m).s, (Ci.tickT L s m).m)) :
    Ci.Goals.TInvariant L :=
  tInvariant_of_obligations' bridge_in bridge_out hside henc

end ExpProofs.CiProof.Skel
