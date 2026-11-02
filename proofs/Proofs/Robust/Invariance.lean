import Mathlib

/-! Robust invariance of `{ξ | ‖ξ‖_Q ≤ r}` (`r = √ρ`) on `ℝⁿ`, the Taylor route to the contraction, and observables. -/

namespace Proofs.Robust
open Matrix

variable {n : Type*} [Fintype n]

def qf (Q : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (Q *ᵥ x)

noncomputable def qn (Q : Matrix n n ℝ) (x : n → ℝ) : ℝ := Real.sqrt (qf Q x)

structure Sym (Q : Matrix n n ℝ) : Prop where
  symm : Qᵀ = Q
  nonneg : ∀ x, 0 ≤ qf Q x

theorem Sym.of_posSemidef {Q : Matrix n n ℝ} (h : Q.PosSemidef) : Sym Q where
  symm := by have h1 := h.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h1
  nonneg x := by simpa [qf] using h.dotProduct_mulVec_nonneg x

theorem bil_symm {Q : Matrix n n ℝ} (hS : Qᵀ = Q) (x y : n → ℝ) : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hS]

theorem qf_add {Q : Matrix n n ℝ} (hS : Qᵀ = Q) (x y : n → ℝ) :
    qf Q (x + y) = qf Q x + 2 * (x ⬝ᵥ (Q *ᵥ y)) + qf Q y := by
  unfold qf
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, bil_symm hS y x]
  ring

theorem qf_smul (Q : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) : qf Q (t • x) = t * t * qf Q x := by
  unfold qf
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem bil_sq_le {Q : Matrix n n ℝ} (hQ : Sym Q) (x y : n → ℝ) :
    (x ⬝ᵥ (Q *ᵥ y)) ^ 2 ≤ qf Q x * qf Q y := by
  have h : ∀ t : ℝ, 0 ≤ qf Q y * (t * t) + (2 * (x ⬝ᵥ (Q *ᵥ y))) * t + qf Q x := by
    intro t
    have h0 := hQ.nonneg (x + t • y)
    rw [qf_add hQ.symm, qf_smul, mulVec_smul, dotProduct_smul, smul_eq_mul] at h0
    nlinarith [h0]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

theorem qn_nonneg (Q : Matrix n n ℝ) (x : n → ℝ) : 0 ≤ qn Q x := Real.sqrt_nonneg _

theorem qn_sq {Q : Matrix n n ℝ} (hQ : Sym Q) (x : n → ℝ) : qn Q x ^ 2 = qf Q x := Real.sq_sqrt (hQ.nonneg x)

theorem bil_le {Q : Matrix n n ℝ} (hQ : Sym Q) (x y : n → ℝ) : x ⬝ᵥ (Q *ᵥ y) ≤ qn Q x * qn Q y := by
  rw [qn, qn, ← Real.sqrt_mul (hQ.nonneg x)]
  exact Real.le_sqrt_of_sq_le (bil_sq_le hQ x y)

theorem qn_add_le {Q : Matrix n n ℝ} (hQ : Sym Q) (x y : n → ℝ) : qn Q (x + y) ≤ qn Q x + qn Q y := by
  have hb := bil_le hQ x y
  rw [qn, Real.sqrt_le_left (by positivity [qn_nonneg Q x, qn_nonneg Q y]), qf_add hQ.symm, ← qn_sq hQ x,
    ← qn_sq hQ y]
  nlinarith [hb]

theorem qn_smul (Q : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) : qn Q (t • x) = |t| * qn Q x := by
  rw [qn, qn, qf_smul, ← abs_mul_abs_self t, Real.sqrt_mul (mul_self_nonneg |t|), Real.sqrt_mul_self (abs_nonneg t)]

theorem qn_le_iff (Q : Matrix n n ℝ) {r : ℝ} (hr : 0 ≤ r) (x : n → ℝ) : qn Q x ≤ r ↔ qf Q x ≤ r ^ 2 := by
  rw [qn, Real.sqrt_le_left hr]

theorem qn_le_sqrt_iff (Q : Matrix n n ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : n → ℝ) : qn Q x ≤ Real.sqrt ρ ↔ qf Q x ≤ ρ := by
  rw [qn_le_iff Q (Real.sqrt_nonneg ρ), Real.sq_sqrt hρ]

/-! ## (a) Robust invariance -/

/-- One step: `ξ` in the set, `Φ` contracts by `λ` there, residual at most `δ ≤ (1 − λ) r`. -/
theorem robust_step {Q : Matrix n n ℝ} (hQ : Sym Q) {Φ : (n → ℝ) → (n → ℝ)} {lam r δ : ℝ} (hlam : 0 ≤ lam)
    (hΦ : ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ) ≤ lam * qn Q ξ) (hδ : δ ≤ (1 - lam) * r)
    {ξ ξ' : n → ℝ} (hξ : qn Q ξ ≤ r) (hres : qn Q (ξ' - Φ ξ) ≤ δ) : qn Q ξ' ≤ r := by
  have e : ξ' = Φ ξ + (ξ' - Φ ξ) := by abel
  have h1 := qn_add_le hQ (Φ ξ) (ξ' - Φ ξ)
  rw [← e] at h1
  have h2 := hΦ ξ hξ
  have h3 : lam * qn Q ξ ≤ lam * r := mul_le_mul_of_nonneg_left hξ hlam
  linarith

theorem robust_forever {Q : Matrix n n ℝ} (hQ : Sym Q) {Φ : (n → ℝ) → (n → ℝ)} {lam r δ : ℝ} (hlam : 0 ≤ lam)
    (hΦ : ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ) ≤ lam * qn Q ξ) (hδ : δ ≤ (1 - lam) * r)
    (ξ : ℕ → n → ℝ) (h0 : qn Q (ξ 0) ≤ r) (hres : ∀ k, qn Q (ξ (k + 1) - Φ (ξ k)) ≤ δ) :
    ∀ k, qn Q (ξ k) ≤ r
  | 0 => h0
  | k + 1 => robust_step hQ hlam hΦ hδ (robust_forever hQ hlam hΦ hδ ξ h0 hres k) (hres k)

/-- Invariance of `{x | ‖π x‖_Q ≤ r}` for a system `fly` read through coordinates `π`. -/
theorem sublevel_inv {S : Type*} (fly : S → S) (π : S → n → ℝ) {Q : Matrix n n ℝ} (hQ : Sym Q)
    {Φ : (n → ℝ) → (n → ℝ)} {lam r δ : ℝ} (hlam : 0 ≤ lam)
    (hΦ : ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ) ≤ lam * qn Q ξ) (hδ : δ ≤ (1 - lam) * r)
    (hres : ∀ x, qn Q (π x) ≤ r → qn Q (π (fly x) - Φ (π x)) ≤ δ) :
    ∀ x, qn Q (π x) ≤ r → qn Q (π (fly x)) ≤ r :=
  fun x hx => robust_step hQ hlam hΦ hδ hx (hres x hx)

/-! ## (b) The Taylor route -/

theorem lin_bound_of_qf {Q J : Matrix n n ℝ} (hQ : Sym Q) {lamLin : ℝ} (hl : 0 ≤ lamLin)
    (h : ∀ ξ, qf Q (J *ᵥ ξ) ≤ lamLin ^ 2 * qf Q ξ) (ξ : n → ℝ) : qn Q (J *ᵥ ξ) ≤ lamLin * qn Q ξ := by
  rw [qn_le_iff Q (mul_nonneg hl (qn_nonneg Q ξ)), mul_pow, qn_sq hQ]
  exact h ξ

theorem qf_mulVec (Q J : Matrix n n ℝ) (ξ : n → ℝ) : qf Q (J *ᵥ ξ) = qf (Jᵀ * Q * J) ξ := by
  unfold qf
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec ξ Jᵀ, vecMul_transpose]

/-- The linear part's contraction from the certificate `λ_lin² Q − Jᵀ Q J ⪰ 0`. -/
theorem lin_bound_of_cert {Q J : Matrix n n ℝ} (hQ : Sym Q) {lamLin : ℝ} (hl : 0 ≤ lamLin)
    (hcert : ∀ ξ, 0 ≤ qf (lamLin ^ 2 • Q - Jᵀ * Q * J) ξ) (ξ : n → ℝ) : qn Q (J *ᵥ ξ) ≤ lamLin * qn Q ξ := by
  refine lin_bound_of_qf hQ hl (fun ξ => ?_) ξ
  have h := hcert ξ
  unfold qf at h
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  rw [qf_mulVec]; unfold qf; linarith

/-- `Φ = J ξ + R ξ` with `‖R ξ‖_Q ≤ (L₂/2) ‖ξ‖²_Q` contracts by `λ_lin + (L₂/2) r` on the set. -/
theorem contract_of_taylor {Q J : Matrix n n ℝ} (hQ : Sym Q) {Φ : (n → ℝ) → (n → ℝ)} {lamLin L2 r : ℝ}
    (hL2 : 0 ≤ L2) (hJ : ∀ ξ, qn Q (J *ᵥ ξ) ≤ lamLin * qn Q ξ)
    (hR : ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ - J *ᵥ ξ) ≤ L2 / 2 * qn Q ξ ^ 2) :
    ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ) ≤ (lamLin + L2 / 2 * r) * qn Q ξ := by
  intro ξ hξ
  have e : Φ ξ = J *ᵥ ξ + (Φ ξ - J *ᵥ ξ) := by abel
  have h1 := qn_add_le hQ (J *ᵥ ξ) (Φ ξ - J *ᵥ ξ)
  rw [← e] at h1
  have h2 := hJ ξ
  have h3 := hR ξ hξ
  have h0 := qn_nonneg Q ξ
  have h4 : L2 / 2 * qn Q ξ ^ 2 ≤ L2 / 2 * r * qn Q ξ := by
    have : qn Q ξ ^ 2 ≤ r * qn Q ξ := by nlinarith
    nlinarith
  nlinarith

/-- The remainder bound from a Lipschitz bound `‖(DΦ x − J) η‖_Q ≤ L₂ ‖x‖_Q ‖η‖_Q` on the set, `Φ 0 = 0`. -/
theorem remainder_of_deriv {Q J : Matrix n n ℝ} (hQ : Sym Q) {Φ : (n → ℝ) → (n → ℝ)}
    {D : (n → ℝ) → (n → ℝ) →L[ℝ] (n → ℝ)} {L2 r : ℝ} (hL2 : 0 ≤ L2) (hΦ0 : Φ 0 = 0)
    (hD : ∀ x, qn Q x ≤ r → HasFDerivAt Φ (D x) x)
    (hLip : ∀ x, qn Q x ≤ r → ∀ η, qn Q (D x η - J *ᵥ η) ≤ L2 * qn Q x * qn Q η) :
    ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ - J *ᵥ ξ) ≤ L2 / 2 * qn Q ξ ^ 2 := by
  intro ξ hξ
  set v := Φ ξ - J *ᵥ ξ with hv
  set w := Q *ᵥ v
  let g : ℝ → n → ℝ := fun t => Φ (t • ξ) - t • (J *ᵥ ξ)
  let g' : ℝ → n → ℝ := fun t => D (t • ξ) ξ - J *ᵥ ξ
  have hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, qn Q (t • ξ) ≤ r := by
    intro t ht
    rw [qn_smul, abs_of_nonneg ht.1]
    nlinarith [qn_nonneg Q ξ, ht.2]
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t • ξ) ξ t := by simpa using (hasDerivAt_id t).smul_const ξ
    have h2 := (hD _ (hx t ht)).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • (J *ᵥ ξ)) (J *ᵥ ξ) t := by
      simpa using (hasDerivAt_id t).smul_const (J *ᵥ ξ)
    exact h2.sub h3
  let C := qn Q v * (L2 * qn Q ξ ^ 2)
  let k : ℝ → ℝ := fun t => w ⬝ᵥ g t - C * t ^ 2 / 2
  let k' : ℝ → ℝ := fun t => w ⬝ᵥ g' t - C * t
  have hk : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt k (k' t) t := by
    intro t ht
    have hc := hasDerivAt_pi.1 (hg t ht)
    have hs : HasDerivAt (fun t => ∑ i, w i * g t i) (∑ i, w i * g' t i) t :=
      HasDerivAt.fun_sum (fun i _ => (hc i).const_mul (w i))
    have hq : HasDerivAt (fun t : ℝ => C * t ^ 2 / 2) (C * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul C).div_const 2
      convert this using 1; push_cast; ring
    exact hs.sub hq
  have hk'le : ∀ t ∈ Set.Icc (0 : ℝ) 1, k' t ≤ 0 := by
    intro t ht
    have h1 : w ⬝ᵥ g' t ≤ qn Q (g' t) * qn Q v := by
      rw [dotProduct_comm]; exact bil_le hQ _ _
    have h2 : qn Q (g' t) ≤ L2 * qn Q (t • ξ) * qn Q ξ := hLip _ (hx t ht) ξ
    rw [qn_smul, abs_of_nonneg ht.1] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (qn_nonneg Q v)
    show w ⬝ᵥ g' t - C * t ≤ 0
    have : C * t = L2 * (t * qn Q ξ) * qn Q ξ * qn Q v := by ring
    linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope k k' (zero_lt_one' ℝ)
    (fun t ht => (hk t ht).continuousAt.continuousWithinAt)
    (fun t ht => hk t (Set.Ioo_subset_Icc_self ht))
  have hle := hk'le c (Set.Ioo_subset_Icc_self hc)
  rw [hslope] at hle
  have hk0 : k 0 = 0 := by simp [k, g, hΦ0]
  have hk1 : k 1 = qn Q v ^ 2 - C / 2 := by
    simp only [k, g, one_smul, one_pow, mul_one]
    rw [qn_sq hQ, qf, ← hv, dotProduct_comm]
  rw [hk0, hk1] at hle
  have hC : qn Q v ^ 2 ≤ qn Q v * (L2 / 2 * qn Q ξ ^ 2) := by
    have : C / 2 = qn Q v * (L2 / 2 * qn Q ξ ^ 2) := by ring
    linarith [show qn Q v ^ 2 - C / 2 ≤ 0 by simpa using hle]
  have h0 := qn_nonneg Q v
  have hK : 0 ≤ L2 / 2 * qn Q ξ ^ 2 := by positivity
  nlinarith

theorem robust_of_taylor {Q J : Matrix n n ℝ} (hQ : Sym Q) {Φ : (n → ℝ) → (n → ℝ)} {lamLin L2 r δ : ℝ}
    (hl : 0 ≤ lamLin) (hL2 : 0 ≤ L2) (hr : 0 ≤ r) (hJ : ∀ ξ, qn Q (J *ᵥ ξ) ≤ lamLin * qn Q ξ)
    (hR : ∀ ξ, qn Q ξ ≤ r → qn Q (Φ ξ - J *ᵥ ξ) ≤ L2 / 2 * qn Q ξ ^ 2)
    (hδ : δ ≤ (1 - (lamLin + L2 / 2 * r)) * r)
    {ξ ξ' : n → ℝ} (hξ : qn Q ξ ≤ r) (hres : qn Q (ξ' - Φ ξ) ≤ δ) : qn Q ξ' ≤ r :=
  robust_step hQ (by positivity) (contract_of_taylor hQ hL2 hJ hR) hδ hξ hres

/-! ## (c) Bounded observables -/

theorem obs_bound {Q : Matrix n n ℝ} (f : (n → ℝ) → ℝ) {L r : ℝ} (hL : 0 ≤ L)
    (hf : ∀ ξ, qn Q ξ ≤ r → |f ξ - f 0| ≤ L * qn Q ξ) : ∀ ξ, qn Q ξ ≤ r → |f ξ - f 0| ≤ L * r :=
  fun ξ hξ => (hf ξ hξ).trans (mul_le_mul_of_nonneg_left hξ hL)

theorem obs_bound_lip {Q : Matrix n n ℝ} (f : (n → ℝ) → ℝ) {L r : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * qn Q (x - y)) : ∀ ξ, qn Q ξ ≤ r → |f ξ - f 0| ≤ L * r :=
  obs_bound f hL fun ξ _ => by simpa using hf ξ 0

/-- A linear observable `c ⬝ ξ` from the certificate `L² Q − c cᵀ ⪰ 0`. -/
theorem abs_dot_le_of_cert {Q : Matrix n n ℝ} (hQ : Sym Q) {c : n → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hcert : ∀ ξ, (c ⬝ᵥ ξ) ^ 2 ≤ L ^ 2 * qf Q ξ) (ξ : n → ℝ) : |c ⬝ᵥ ξ| ≤ L * qn Q ξ := by
  apply abs_le_of_sq_le_sq' _ (mul_nonneg hL (qn_nonneg Q ξ)) |> fun h => abs_le.mpr h
  rw [mul_pow, qn_sq hQ]; exact hcert ξ

end Proofs.Robust
