import ExpProofs.CiProof.PsdForm

/-! Generic per-substep Lyapunov lemmas for the ODE-style argument: the exact quadratic step identity, a one-step
decrease bound from pointwise bounds on the increment, recentring, and composition over several substeps with
additive errors (no enclosure of composed maps). -/

namespace ExpProofs.CiProof
open Matrix

variable {n : Type*} [Fintype n]

/-- Exact identity: `V(x + h d) = V(x) + 2 h ⟨x, P d⟩ + h² V(d)` for symmetric `P` (`x` already centred). -/
theorem step_identity (P : Matrix n n ℝ) (hS : Pᵀ = P) (x d : n → ℝ) (h : ℝ) :
    qf P (x + h • d) = qf P x + 2 * h * (x ⬝ᵥ (P *ᵥ d)) + h ^ 2 * qf P d := by
  rw [qf_add P hS, qf_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- One substep: if the increment satisfies `⟨x, P d⟩ ≤ −λ V(x) + β` and `V(d) ≤ γ`, then
`V(x + h d) ≤ (1 − 2 h λ) V(x) + 2 h β + h² γ` (`h ≥ 0`). -/
theorem step_decrease (P : Matrix n n ℝ) (hS : Pᵀ = P) (x d : n → ℝ) {h lam β γ : ℝ} (hh : 0 ≤ h)
    (hb : x ⬝ᵥ (P *ᵥ d) ≤ -lam * qf P x + β) (hg : qf P d ≤ γ) :
    qf P (x + h • d) ≤ (1 - 2 * h * lam) * qf P x + 2 * h * β + h ^ 2 * γ := by
  rw [step_identity P hS]
  have h1 : 2 * h * (x ⬝ᵥ (P *ᵥ d)) ≤ 2 * h * (-lam * qf P x + β) := by
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have h2 : h ^ 2 * qf P d ≤ h ^ 2 * γ := mul_le_mul_of_nonneg_left hg (by positivity)
  nlinarith

/-- Recentring: moving the centre by `c` costs at most `√V(c)` in the seminorm. -/
theorem recentre_le {P : Matrix n n ℝ} (hP : P.PosSemidef) (hS : Pᵀ = P) (x c : n → ℝ) :
    Real.sqrt (qf P (x + c)) ≤ Real.sqrt (qf P x) + Real.sqrt (qf P c) :=
  sqrt_qf_add_le hP hS x c

/-- Composition over `N` substeps: `V_{k+1} ≤ a V_k + b` for `k < N` gives `V_N ≤ a^N V_0 + b Σ_{k<N} a^k`. -/
theorem compose_steps (V : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (N : ℕ) (hstep : ∀ k, k < N → V (k + 1) ≤ a * V k + b) :
    V N ≤ a ^ N * V 0 + b * ∑ k ∈ Finset.range N, a ^ k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun k hk => hstep k (by omega))
    have hs := hstep N (by omega)
    have hgeo : ∑ k ∈ Finset.range (N + 1), a ^ k = a * ∑ k ∈ Finset.range N, a ^ k + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, mul_comm]
    rw [hgeo, pow_succ]
    have : a * V N ≤ a * (a ^ N * V 0 + b * ∑ k ∈ Finset.range N, a ^ k) := mul_le_mul_of_nonneg_left ih' ha
    nlinarith

end ExpProofs.CiProof
