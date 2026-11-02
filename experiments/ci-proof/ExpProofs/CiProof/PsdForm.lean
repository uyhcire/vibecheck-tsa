import Mathlib

/-! Quadratic forms of positive semidefinite real matrices: Cauchy–Schwarz, the triangle inequality of the
induced seminorm, and the one-step contraction lemma used to prove a Lyapunov sublevel set invariant.

`contract_step`: if `ρ² P − Aᵀ P' A ⪰ 0`, `zᵀ P z ≤ r²` and `eᵀ P' e ≤ ε²` with `ρ r + ε ≤ r`, then
`(A z + e)ᵀ P' (A z + e) ≤ r²`. This is the whole linear-algebra content of a barrier argument for a map
`z ↦ A z + e(z)` whose nonlinear and rounding remainder `e` is bounded. -/

namespace ExpProofs.CiProof
open Matrix

variable {n : Type*} [Fintype n]

/-- The quadratic form `xᵀ P x`. -/
def qf (P : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

theorem qf_nonneg {P : Matrix n n ℝ} (hP : P.PosSemidef) (x : n → ℝ) : 0 ≤ qf P x := by
  have := hP.dotProduct_mulVec_nonneg x
  simpa [qf] using this

/-- Symmetry of the bilinear form of a symmetric matrix. -/
theorem bil_symm {P : Matrix n n ℝ} (hS : Pᵀ = P) (x y : n → ℝ) : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hS]

theorem qf_add (P : Matrix n n ℝ) (hS : Pᵀ = P) (x y : n → ℝ) :
    qf P (x + y) = qf P x + 2 * (x ⬝ᵥ (P *ᵥ y)) + qf P y := by
  unfold qf
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, bil_symm hS y x]
  ring

theorem qf_smul (P : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) : qf P (t • x) = t * t * qf P x := by
  unfold qf
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Cauchy–Schwarz for a symmetric positive semidefinite form. -/
theorem bil_sq_le {P : Matrix n n ℝ} (hP : P.PosSemidef) (hS : Pᵀ = P) (x y : n → ℝ) :
    (x ⬝ᵥ (P *ᵥ y)) ^ 2 ≤ qf P x * qf P y := by
  have h : ∀ t : ℝ, 0 ≤ qf P y * (t * t) + (2 * (x ⬝ᵥ (P *ᵥ y))) * t + qf P x := by
    intro t
    have h0 := qf_nonneg hP (x + t • y)
    rw [qf_add P hS, qf_smul, mulVec_smul, dotProduct_smul, smul_eq_mul] at h0
    nlinarith [h0]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

/-- Triangle inequality for the seminorm `√(xᵀ P x)`. -/
theorem sqrt_qf_add_le {P : Matrix n n ℝ} (hP : P.PosSemidef) (hS : Pᵀ = P) (x y : n → ℝ) :
    Real.sqrt (qf P (x + y)) ≤ Real.sqrt (qf P x) + Real.sqrt (qf P y) := by
  have hx := qf_nonneg hP x
  have hy := qf_nonneg hP y
  have hb : x ⬝ᵥ (P *ᵥ y) ≤ Real.sqrt (qf P x) * Real.sqrt (qf P y) := by
    rw [← Real.sqrt_mul hx]
    exact Real.le_sqrt_of_sq_le (bil_sq_le hP hS x y)
  rw [Real.sqrt_le_left (by positivity)]
  rw [qf_add P hS]
  have := Real.sq_sqrt hx
  have := Real.sq_sqrt hy
  nlinarith [hb]

/-- `(A z)ᵀ P' (A z) = zᵀ (Aᵀ P' A) z`. -/
theorem qf_mulVec (P' A : Matrix n n ℝ) (z : n → ℝ) : qf P' (A *ᵥ z) = qf (Aᵀ * P' * A) z := by
  unfold qf
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z Aᵀ, vecMul_transpose]

/-- One-step contraction of a Lyapunov sublevel set, with a bounded remainder. -/
theorem contract_step {P P' A : Matrix n n ℝ} (hP' : P'.PosSemidef) (hS' : P'ᵀ = P') {ρ r ε : ℝ}
    (hcert : (ρ ^ 2 • P - Aᵀ * P' * A).PosSemidef) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (z e : n → ℝ) (hz : qf P z ≤ r ^ 2) (he : qf P' e ≤ ε ^ 2) (hε : 0 ≤ ε) (hm : ρ * r + ε ≤ r) :
    qf P' (A *ᵥ z + e) ≤ r ^ 2 := by
  have hA : qf P' (A *ᵥ z) ≤ (ρ * r) ^ 2 := by
    have h1 := qf_nonneg hcert z
    have h2 : qf (ρ ^ 2 • P - Aᵀ * P' * A) z = ρ ^ 2 * qf P z - qf (Aᵀ * P' * A) z := by
      unfold qf; rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [qf_mulVec]
    nlinarith [h1, h2, hz, sq_nonneg ρ]
  have hsA : Real.sqrt (qf P' (A *ᵥ z)) ≤ ρ * r := Real.sqrt_le_iff.mpr ⟨by positivity, hA⟩
  have hse : Real.sqrt (qf P' e) ≤ ε := Real.sqrt_le_iff.mpr ⟨hε, he⟩
  have ht := sqrt_qf_add_le hP' hS' (A *ᵥ z) e
  have hsum : Real.sqrt (qf P' (A *ᵥ z + e)) ≤ r := by linarith
  have h0 := qf_nonneg hP' (A *ᵥ z + e)
  calc qf P' (A *ᵥ z + e) = Real.sqrt (qf P' (A *ᵥ z + e)) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ r ^ 2 := by gcongr

end ExpProofs.CiProof
