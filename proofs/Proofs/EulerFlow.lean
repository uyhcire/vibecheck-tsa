import Proofs.Lemmas

namespace Vibecheck.Ideal

/-- Bound on `|u − u'|` and `|alphaV − alphaV'|` from coordinate perturbations `η`. -/
noncomputable def dV (b : Box) (η : Fin 7 → ℝ) : ℝ :=
  b.D * η 2 + b.V * η 4 + b.D * η 3 + b.V * η 5

/-- Bound on `|aN − aN'|` from coordinate perturbations `η`. -/
noncomputable def dAN (b : Box) (η : Fin 7 → ℝ) : ℝ :=
  b.A * (kN * dV b η) + kN * b.U * (dV b η + 2 * (tauStall * dV b η))

/-- Componentwise Lipschitz bound: `|F y i − F y' i| ≤ lipF b η i` when `|y j − y' j| ≤ η j`. -/
noncomputable def lipF (b : Box) (η : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![η 2, η 3,
    5 * η 4 + b.D * dAN b η + kN * b.U * b.A * η 5 + (b.V * (kD * dV b η) + kD * b.U * η 2),
    5 * η 5 + b.D * dAN b η + kN * b.U * b.A * η 4 + (b.V * (kD * dV b η) + kD * b.U * η 3),
    b.D * η 6 + b.Q * η 5, b.D * η 6 + b.Q * η 4,
    (b.U * (kElev * dV b η) + kElev * b.U * dV b η)
      + (b.A * (kAlpha * dV b η) + kAlpha * b.U * dV b η)
      + (b.Q * (kQ * dV b η) + kQ * b.U * η 6)]

/-- Bound on `|F y i|` over the box. -/
noncomputable def maxF (b : Box) : Fin 7 → ℝ :=
  ![b.V, b.V, 5 * b.D + kN * b.U * b.A * b.D + kD * b.U * b.V,
    5 * b.D + kN * b.U * b.A * b.D + kD * b.U * b.V + g, b.Q * b.D, b.Q * b.D,
    kElev * b.U * b.U + kAlpha * b.U * b.A + kQ * b.U * b.Q]

/-- The Euler-vs-flow error bound on the box: `lipF b (maxF b) i · Δt² / 2`. -/
noncomputable def eFlow (b : Box) (i : Fin 7) : ℝ := lipF b (maxF b) i * Δt ^ 2 / 2

section

variable {b : Box} {y y' : Fin 7 → ℝ} {e θ : ℝ}

theorem dV_u (hy : InBox b y) (hy' : InBox b y') {η : Fin 7 → ℝ} (hη : ∀ j, |y j - y' j| ≤ η j) :
    |upR (y 2) (y 3) (y 4) (y 5) - upR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ dV b η := by
  refine near_max0 ?_
  have h1 := near_mul (hη 2) (hη 4) hy'.vx hy.dx
  have h2 := near_mul (hη 3) (hη 5) hy'.vz hy.dz
  have := near_add h1 h2
  simp only [uR, dV] at *
  linarith

theorem dV_alpha (hy : InBox b y) (hy' : InBox b y') {η : Fin 7 → ℝ}
    (hη : ∀ j, |y j - y' j| ≤ η j) :
    |alphaVR (y 2) (y 3) (y 4) (y 5) - alphaVR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ dV b η := by
  have h1 := near_mul (hη 2) (hη 5) hy'.vx hy.dz
  have h2 := near_mul (hη 3) (hη 4) hy'.vz hy.dx
  have := near_sub h1 h2
  simp only [alphaVR, dV] at *
  linarith

theorem dAN_aN (hy : InBox b y) (hy' : InBox b y') {η : Fin 7 → ℝ}
    (hη : ∀ j, |y j - y' j| ≤ η j) :
    |aNR (y 2) (y 3) (y 4) (y 5) - aNR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ dAN b η := by
  obtain ⟨hkN, htau, -, -, -, -, -⟩ := kcoef_nonneg
  have hu := dV_u hy hy' hη
  have ha := dV_alpha hy hy' hη
  have hku : |kN * upR (y 2) (y 3) (y 4) (y 5) - kN * upR (y' 2) (y' 3) (y' 4) (y' 5)|
      ≤ kN * dV b η := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hkN]; exact mul_le_mul_of_nonneg_left hu hkN
  have hku' : |kN * upR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ kN * b.U := by
    rw [abs_mul, abs_of_nonneg hkN]; exact mul_le_mul_of_nonneg_left hy'.up hkN
  have htu : |tauStall * upR (y 2) (y 3) (y 4) (y 5) - tauStall * upR (y' 2) (y' 3) (y' 4) (y' 5)|
      ≤ tauStall * dV b η := by
    rw [← mul_sub, abs_mul, abs_of_nonneg htau]; exact mul_le_mul_of_nonneg_left hu htau
  have hL := liftShapeR_lip (a := alphaVR (y 2) (y 3) (y 4) (y 5))
    (a' := alphaVR (y' 2) (y' 3) (y' 4) (y' 5))
    (t := tauStall * upR (y 2) (y 3) (y 4) (y 5)) (t' := tauStall * upR (y' 2) (y' 3) (y' 4) (y' 5))
    (mul_nonneg htau (upR_nonneg _ _ _ _))
  have hL' : |liftShapeR (alphaVR (y 2) (y 3) (y 4) (y 5)) (tauStall * upR (y 2) (y 3) (y 4) (y 5))
      - liftShapeR (alphaVR (y' 2) (y' 3) (y' 4) (y' 5)) (tauStall * upR (y' 2) (y' 3) (y' 4) (y' 5))|
      ≤ dV b η + 2 * (tauStall * dV b η) := by linarith
  have := near_mul hku hL' hku' hy.lift
  simpa only [aNR, dAN] using this

theorem lipF_spec (hy : InBox b y) (hy' : InBox b y') (he : |e| ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    {η : Fin 7 → ℝ} (hη : ∀ j, |y j - y' j| ≤ η j) (i : Fin 7) :
    |F e θ y i - F e θ y' i| ≤ lipF b η i := by
  obtain ⟨hkN, htau, hkD, hkE, hkA, hkQ, hT⟩ := kcoef_nonneg
  have hu := dV_u hy hy' hη
  have ha := dV_alpha hy hy' hη
  have haN := dAN_aN hy hy' hη
  have hD := hy.D_nonneg
  have hU := hy.U_nonneg
  have cu : ∀ c : ℝ, 0 ≤ c →
      |c * upR (y 2) (y 3) (y 4) (y 5) - c * upR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ c * dV b η := by
    intro c hc; rw [← mul_sub, abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hu hc
  have cu' : ∀ c : ℝ, 0 ≤ c → |c * upR (y' 2) (y' 3) (y' 4) (y' 5)| ≤ c * b.U := by
    intro c hc; rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hy'.up hc
  have hthr : |thrustMax * θ| ≤ 5 := by
    rw [hT, abs_of_nonneg (by linarith [hθ.1])]; linarith [hθ.2]
  have h0 : |thrustMax * θ - thrustMax * θ| ≤ 0 := by simp
  fin_cases i
  · simpa [F, lipF] using hη 2
  · simpa [F, lipF] using hη 3
  · have t1 := near_mul h0 (hη 4) hthr hy.dx
    have t2 := near_mul haN (hη 5) hy'.aN hy.dz
    have t3 := near_mul (cu kD hkD) (hη 2) (cu' kD hkD) hy.vx
    have := near_sub (near_sub t1 t2) t3
    simp only [F, lipF, axR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at this ⊢
    linarith
  · have t1 := near_mul h0 (hη 5) hthr hy.dz
    have t2 := near_mul haN (hη 4) hy'.aN hy.dx
    have t3 := near_mul (cu kD hkD) (hη 3) (cu' kD hkD) hy.vz
    have := near_sub (near_sub (near_add t1 t2) t3) (show |g - g| ≤ 0 by simp)
    simp only [F, lipF, azR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at this ⊢
    linarith
  · have := near_mul (hη 6) (hη 5) hy'.q hy.dz
    simp only [F, lipF, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, neg_sub_neg] at this ⊢
    rw [abs_sub_comm]; linarith
  · have := near_mul (hη 6) (hη 4) hy'.q hy.dx
    simp only [F, lipF, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at this ⊢
    linarith
  · have k1 := near_mul (cu kElev hkE) hu (cu' kElev hkE) hy.up
    have k1' : |kElev * upR (y' 2) (y' 3) (y' 4) (y' 5) * upR (y' 2) (y' 3) (y' 4) (y' 5)|
        ≤ kElev * b.U * b.U := by
      rw [abs_mul]; exact mul_le_mul (cu' kElev hkE) hy'.up (abs_nonneg _) (mul_nonneg hkE hU)
    have k2 := near_mul k1 (show |e - e| ≤ 0 by simp) k1' he
    have k3 := near_mul (cu kAlpha hkA) ha (cu' kAlpha hkA) hy.alpha
    have k4 := near_mul (cu kQ hkQ) (hη 6) (cu' kQ hkQ) hy.q
    have := near_sub (near_sub k2 k3) k4
    simp only [F, lipF, qdotR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at this ⊢
    nlinarith

theorem maxF_spec (hy : InBox b y) (he : |e| ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) (i : Fin 7) :
    |F e θ y i| ≤ maxF b i := by
  obtain ⟨hkN, htau, hkD, hkE, hkA, hkQ, hT⟩ := kcoef_nonneg
  have hD := hy.D_nonneg
  have hU := hy.U_nonneg
  have hV := hy.V_nonneg
  have hg : 0 ≤ g := by rw [g_eq]; norm_num
  have hthr : |thrustMax * θ| ≤ 5 := by
    rw [hT, abs_of_nonneg (by linarith [hθ.1])]; linarith [hθ.2]
  have prod : ∀ {a b A B : ℝ}, |a| ≤ A → |b| ≤ B → |a * b| ≤ A * B := fun ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have cu : ∀ c : ℝ, 0 ≤ c → |c * upR (y 2) (y 3) (y 4) (y 5)| ≤ c * b.U := by
    intro c hc; rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hy.up hc
  fin_cases i
  · simpa [F, maxF] using hy.vx
  · simpa [F, maxF] using hy.vz
  · have t1 := prod hthr hy.dx
    have t2 := prod hy.aN hy.dz
    have t3 := prod (cu kD hkD) hy.vx
    simp only [F, maxF, axR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    have := abs_sub (thrustMax * θ * y 4 - aNR (y 2) (y 3) (y 4) (y 5) * y 5)
      (kD * upR (y 2) (y 3) (y 4) (y 5) * y 2)
    have := abs_sub (thrustMax * θ * y 4) (aNR (y 2) (y 3) (y 4) (y 5) * y 5)
    linarith
  · have t1 := prod hthr hy.dz
    have t2 := prod hy.aN hy.dx
    have t3 := prod (cu kD hkD) hy.vz
    simp only [F, maxF, azR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    have := abs_sub (thrustMax * θ * y 5 + aNR (y 2) (y 3) (y 4) (y 5) * y 4
      - kD * upR (y 2) (y 3) (y 4) (y 5) * y 3) g
    have := abs_sub (thrustMax * θ * y 5 + aNR (y 2) (y 3) (y 4) (y 5) * y 4)
      (kD * upR (y 2) (y 3) (y 4) (y 5) * y 3)
    have := abs_add_le (thrustMax * θ * y 5) (aNR (y 2) (y 3) (y 4) (y 5) * y 4)
    rw [abs_of_nonneg hg] at *
    linarith
  · have := prod hy.q hy.dz
    simp only [F, maxF, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, abs_neg]
    linarith
  · have := prod hy.q hy.dx
    simp only [F, maxF, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    linarith
  · have t1 := prod (prod (cu kElev hkE) hy.up) he
    have t2 := prod (cu kAlpha hkA) hy.alpha
    have t3 := prod (cu kQ hkQ) hy.q
    simp only [F, maxF, qdotR, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    have := abs_sub (kElev * upR (y 2) (y 3) (y 4) (y 5) * upR (y 2) (y 3) (y 4) (y 5) * e
      - kAlpha * upR (y 2) (y 3) (y 4) (y 5) * alphaVR (y 2) (y 3) (y 4) (y 5))
      (kQ * upR (y 2) (y 3) (y 4) (y 5) * y 6)
    have := abs_sub (kElev * upR (y 2) (y 3) (y 4) (y 5) * upR (y 2) (y 3) (y 4) (y 5) * e)
      (kAlpha * upR (y 2) (y 3) (y 4) (y 5) * alphaVR (y 2) (y 3) (y 4) (y 5))
    linarith

theorem lipF_scale (η : Fin 7 → ℝ) (c : ℝ) (i : Fin 7) :
    lipF b (fun j => η j * c) i = lipF b η i * c := by
  fin_cases i <;> simp [lipF, dAN, dV] <;> ring

end

/-- If `f 0 = 0` and `|f' t| ≤ C t` on `[0, T]`, then `|f T| ≤ C T² / 2`. -/
theorem quad_bound {f f' : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hf0 : f 0 = 0)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t)
    (hb : ∀ t ∈ Set.Icc 0 T, |f' t| ≤ C * t) : |f T| ≤ C * T ^ 2 / 2 := by
  have hq : ∀ t, HasDerivAt (fun t : ℝ => C * t ^ 2 / 2) (C * t) t := fun t => by
    have := ((hasDerivAt_pow 2 t).const_mul C).div_const 2
    convert this using 1; ring
  have hint : ∀ t ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt f (f' t) (interior (Set.Icc 0 T)) t := fun t ht =>
    (hf t (interior_subset ht)).mono interior_subset
  have hcont : ContinuousOn f (Set.Icc 0 T) := fun t ht => (hf t ht).continuousWithinAt
  have hcq : Continuous (fun t : ℝ => C * t ^ 2 / 2) := by continuity
  have h1 : AntitoneOn (fun t => f t - C * t ^ 2 / 2) (Set.Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => f' t - C * t) (convex_Icc 0 T)
      (hcont.sub hcq.continuousOn) (fun t ht => (hint t ht).sub (hq t).hasDerivWithinAt)
      (fun t ht => ?_)
    have := (abs_le.1 (hb t (interior_subset ht))).2; linarith
  have h2 : MonotoneOn (fun t => f t + C * t ^ 2 / 2) (Set.Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => f' t + C * t) (convex_Icc 0 T)
      (hcont.add hcq.continuousOn) (fun t ht => (hint t ht).add (hq t).hasDerivWithinAt)
      (fun t ht => ?_)
    have := (abs_le.1 (hb t (interior_subset ht))).1; linarith
  have m0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have mT : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  have a1 := h1 m0 mT hT
  have a2 := h2 m0 mT hT
  simp only [hf0] at a1 a2
  rw [abs_le]; constructor <;> nlinarith

/-- **Theorem B (generic box).** Along any exact solution staying in the box `b` on `[0, Δt]`,
each coordinate after one step is within `eFlow b i` of the Euler step from `y 0`. -/
theorem flow_near_euler_box (b : Box) {e θ : ℝ} (he : |e| ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (y : ℝ → Fin 7 → ℝ)
    (hy : ∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt y (F e θ (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox b (y t)) (i : Fin 7) :
    |y Δt i - euler e θ (y 0) i| ≤ eFlow b i := by
  have hΔ : (0 : ℝ) ≤ Δt := by norm_num [Δt]
  have m0 : (0 : ℝ) ∈ Set.Icc 0 Δt := ⟨le_rfl, hΔ⟩
  have hb0 := hbox 0 m0
  have drift : ∀ t ∈ Set.Icc 0 Δt, ∀ j, |y t j - y 0 j| ≤ maxF b j * t := by
    intro t ht j
    have := (convex_Icc (0 : ℝ) Δt).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => y t j) (f' := fun t => F e θ (y t) j)
      (fun s hs => hasDerivWithinAt_pi.1 (hy s hs) j)
      (fun s hs => by rw [Real.norm_eq_abs]; exact maxF_spec (hbox s hs) he hθ j) m0 ht
    simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using this
  have hder : ∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt
      (fun t => y t i - y 0 i - t * F e θ (y 0) i)
      (F e θ (y t) i - F e θ (y 0) i) (Set.Icc 0 Δt) t := by
    intro t ht
    have h1 := hasDerivWithinAt_pi.1 (hy t ht) i
    have h2 := ((hasDerivWithinAt_id t (Set.Icc 0 Δt)).mul_const (F e θ (y 0) i))
    have := (h1.sub_const (y 0 i)).sub h2
    convert this using 1
    · funext t; simp
    · ring
  have hbd : ∀ t ∈ Set.Icc 0 Δt, |F e θ (y t) i - F e θ (y 0) i| ≤ lipF b (maxF b) i * t := by
    intro t ht
    rw [← lipF_scale]
    exact lipF_spec (hbox t ht) hb0 he hθ (drift t ht) i
  have := quad_bound hΔ (by simp) hder hbd
  have e1 : euler e θ (y 0) i = y 0 i + Δt * F e θ (y 0) i := by simp [euler]
  rw [e1]
  have e2 : y Δt i - (y 0 i + Δt * F e θ (y 0) i) = y Δt i - y 0 i - Δt * F e θ (y 0) i := by ring
  rw [e2]
  simpa [eFlow] using this

end Vibecheck.Ideal
