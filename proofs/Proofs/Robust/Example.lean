import Proofs.Robust.Invariance

/-! A 3-state instance of `robust_of_taylor` with every hypothesis discharged: `λ = 7/10 + 1/15`, `r = 1`, `δ = 1/5`. -/

namespace Proofs.Robust.Example

noncomputable section
open Matrix Proofs.Robust ContinuousLinearMap

def Q : Matrix (Fin 3) (Fin 3) ℝ := !![2, 1, 0; 1, 2, 0; 0, 0, 1]
def J : Matrix (Fin 3) (Fin 3) ℝ := !![1 / 2, 1 / 10, 0; 0, 1 / 2, 0; 0, 1 / 10, 1 / 2]
def R (ξ : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 0, ξ 0 ^ 2 / 10]
def Φ (ξ : Fin 3 → ℝ) : Fin 3 → ℝ := J *ᵥ ξ + R ξ

theorem qf_Q (x : Fin 3 → ℝ) : qf Q x = 2 * x 0 ^ 2 + 2 * x 0 * x 1 + 2 * x 1 ^ 2 + x 2 ^ 2 := by
  simp [qf, Q, dotProduct, mulVec, Fin.sum_univ_three]; ring

theorem Q_sym : Sym Q where
  symm := by ext i j; fin_cases i <;> fin_cases j <;> simp [Q]
  nonneg x := by rw [qf_Q]; nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem J_cert (ξ : Fin 3 → ℝ) : 0 ≤ qf ((7 / 10 : ℝ) ^ 2 • Q - Jᵀ * Q * J) ξ := by
  have e : qf ((7 / 10 : ℝ) ^ 2 • Q - Jᵀ * Q * J) ξ =
      12 / 25 * (ξ 0 + 7 / 24 * ξ 1) ^ 2 + 371 / 1200 * (ξ 1 - 60 / 371 * ξ 2) ^ 2 + 2151 / 9275 * ξ 2 ^ 2 := by
    simp [qf, Q, J, dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_three, transpose_apply]; ring
  rw [e]; positivity

theorem hJ (ξ : Fin 3 → ℝ) : qn Q (J *ᵥ ξ) ≤ 7 / 10 * qn Q ξ :=
  lin_bound_of_cert Q_sym (by norm_num) J_cert ξ

theorem hR (ξ : Fin 3 → ℝ) : qn Q (Φ ξ - J *ᵥ ξ) ≤ (2 / 15) / 2 * qn Q ξ ^ 2 := by
  have e : Φ ξ - J *ᵥ ξ = R ξ := by simp [Φ]
  rw [e, qn_sq Q_sym, qn_le_iff Q (by have := Q_sym.nonneg ξ; positivity), qf_Q, qf_Q]
  simp only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h1 : 0 ≤ ξ 0 ^ 2 / 10 := by positivity
  have h2 : ξ 0 ^ 2 / 10 ≤ 2 / 15 / 2 * (2 * ξ 0 ^ 2 + 2 * ξ 0 * ξ 1 + 2 * ξ 1 ^ 2 + ξ 2 ^ 2) := by
    nlinarith [sq_nonneg (ξ 0 + 2 * ξ 1), sq_nonneg (ξ 2)]
  have := pow_le_pow_left₀ h1 h2 2
  nlinarith [this]

theorem invariant {ξ ξ' : Fin 3 → ℝ} (hξ : qn Q ξ ≤ 1) (hres : qn Q (ξ' - Φ ξ) ≤ 1 / 5) : qn Q ξ' ≤ 1 :=
  robust_of_taylor Q_sym (lamLin := 7 / 10) (L2 := 2 / 15) (by norm_num) (by norm_num) (by norm_num) hJ
    (fun ξ _ => hR ξ) (by norm_num) hξ hres

def ξ₀ : Fin 3 → ℝ := ![1 / 2, 0, 0]

theorem qn_ξ₀ : qn Q ξ₀ ≤ 1 := by
  rw [qn_le_iff Q (by norm_num), qf_Q]; norm_num [ξ₀]

example : qn Q (Φ ξ₀ + ![0, 0, 1 / 5]) ≤ 1 :=
  invariant qn_ξ₀ (by rw [add_sub_cancel_left, qn_le_iff Q (by norm_num), qf_Q]; norm_num)

example : ¬ qn Q ![1, 0, 0] ≤ 1 := by
  rw [qn_le_iff Q (by norm_num), qf_Q]; norm_num

example : ¬ ∀ ξ', qn Q (ξ' - Φ 0) ≤ 2 → qn Q ξ' ≤ 1 := by
  intro h
  have hΦ : Φ 0 = 0 := by ext i; fin_cases i <;> simp [Φ, R]
  have := h ![0, 0, 2] (by rw [hΦ, sub_zero, qn_le_iff Q (by norm_num), qf_Q]; norm_num)
  rw [qn_le_iff Q (by norm_num), qf_Q] at this; norm_num at this

def Rd (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 0, 0; 0, 0, 0; x 0 / 5, 0, 0])
def D (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' J) + Rd x

theorem Rd_apply (x η : Fin 3 → ℝ) : Rd x η = ![0, 0, x 0 / 5 * η 0] := by
  ext i; fin_cases i <;> simp [Rd, mulVec, dotProduct, Fin.sum_univ_three]

theorem hasFDeriv_R (x : Fin 3 → ℝ) : HasFDerivAt R (Rd x) x := by
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · have e : (fun η => R η 0) = fun _ => (0 : ℝ) := by funext η; simp [R]
    simp only [Fin.zero_eta, Fin.isValue, e]
    convert hasFDerivAt_const (0 : ℝ) x using 1
    ext η; simp [Rd_apply]
  · have e : (fun η => R η 1) = fun _ => (0 : ℝ) := by funext η; simp [R]
    simp only [Fin.mk_one, Fin.isValue, e]
    convert hasFDerivAt_const (0 : ℝ) x using 1
    ext η; simp [Rd_apply]
  · have e : (fun η => R η 2) = fun η => 1 / 10 * η 0 ^ 2 := by funext η; simp [R]; ring
    simp only [Fin.reduceFinMk, Fin.isValue, e]
    have h := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x).pow 2).const_mul (1 / 10 : ℝ)
    convert h using 1
    ext η; simp [Rd_apply]; ring

theorem hasFDeriv_Φ (x : Fin 3 → ℝ) : HasFDerivAt Φ (D x) x :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' J)).hasFDerivAt.add (hasFDeriv_R x)

theorem x0_sq (x : Fin 3 → ℝ) : 3 * x 0 ^ 2 ≤ 2 * qf Q x := by
  rw [qf_Q]; nlinarith [sq_nonneg (x 0 + 2 * x 1), sq_nonneg (x 2)]

theorem hLip (x : Fin 3 → ℝ) (η : Fin 3 → ℝ) : qn Q (D x η - J *ᵥ η) ≤ 2 / 15 * qn Q x * qn Q η := by
  have e : D x η - J *ᵥ η = ![0, 0, x 0 / 5 * η 0] := by
    rw [← Rd_apply]; simp [D]
  have hx := Q_sym.nonneg x
  have hη := Q_sym.nonneg η
  rw [e, qn_le_iff Q (by have := qn_nonneg Q x; have := qn_nonneg Q η; positivity), mul_pow, mul_pow,
    qn_sq Q_sym, qn_sq Q_sym, qf_Q]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h := mul_le_mul (x0_sq x) (x0_sq η) (by positivity) (by positivity)
  nlinarith [h]

theorem Φ_zero : Φ 0 = 0 := by ext i; fin_cases i <;> simp [Φ, R]

theorem hR_of_deriv (ξ : Fin 3 → ℝ) (hξ : qn Q ξ ≤ 1) : qn Q (Φ ξ - J *ᵥ ξ) ≤ (2 / 15) / 2 * qn Q ξ ^ 2 :=
  remainder_of_deriv Q_sym (r := 1) (by norm_num) Φ_zero (fun x _ => hasFDeriv_Φ x) (fun x _ η => hLip x η) ξ hξ

theorem invariant_of_deriv {ξ ξ' : Fin 3 → ℝ} (hξ : qn Q ξ ≤ 1) (hres : qn Q (ξ' - Φ ξ) ≤ 1 / 5) : qn Q ξ' ≤ 1 :=
  robust_of_taylor Q_sym (lamLin := 7 / 10) (L2 := 2 / 15) (by norm_num) (by norm_num) (by norm_num) hJ
    hR_of_deriv (by norm_num) hξ hres

theorem obs_x0 {ξ : Fin 3 → ℝ} (hξ : qn Q ξ ≤ 1) : |ξ 0| ≤ 1 := by
  have h := abs_dot_le_of_cert Q_sym (c := ![1, 0, 0]) (L := 1) (by norm_num)
    (fun ξ => by have := x0_sq ξ; simp [dotProduct, Fin.sum_univ_three]; nlinarith [Q_sym.nonneg ξ]) ξ
  have e : ![1, 0, 0] ⬝ᵥ ξ = ξ 0 := by simp [dotProduct, Fin.sum_univ_three]
  rw [e] at h; linarith

end

end Proofs.Robust.Example
