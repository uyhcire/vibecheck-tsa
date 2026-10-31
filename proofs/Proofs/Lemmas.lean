import Proofs.Rounding

namespace Vibecheck.Ideal

theorem near_mul {a a' b b' α β A B : ℝ} (ha : |a - a'| ≤ α) (hb : |b - b'| ≤ β)
    (hA : |a'| ≤ A) (hB : |b| ≤ B) : |a * b - a' * b'| ≤ B * α + A * β := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [e]
  calc |(a - a') * b + a' * (b - b')| ≤ |(a - a') * b| + |a' * (b - b')| := abs_add_le _ _
    _ = |a - a'| * |b| + |a'| * |b - b'| := by rw [abs_mul, abs_mul]
    _ ≤ α * B + A * β := by
        gcongr
        · exact (abs_nonneg _).trans ha
        · exact (abs_nonneg _).trans hA
    _ = B * α + A * β := by ring

theorem near_add {a a' b b' α β : ℝ} (ha : |a - a'| ≤ α) (hb : |b - b'| ≤ β) :
    |a + b - (a' + b')| ≤ α + β := by
  have e : a + b - (a' + b') = (a - a') + (b - b') := by ring
  rw [e]; exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem near_sub {a a' b b' α β : ℝ} (ha : |a - a'| ≤ α) (hb : |b - b'| ≤ β) :
    |a - b - (a' - b')| ≤ α + β := by
  have e : a - b - (a' - b') = (a - a') - (b - b') := by ring
  rw [e]; exact (abs_sub _ _).trans (add_le_add ha hb)

theorem near_max0 {a a' α : ℝ} (ha : |a - a'| ≤ α) : |max a 0 - max a' 0| ≤ α :=
  (abs_max_sub_max_le_abs a a' 0).trans ha

theorem abs_le_of_near {a a' α A : ℝ} (ha : |a - a'| ≤ α) (hA : |a'| ≤ A) : |a| ≤ A + α := by
  have := abs_sub_abs_le_abs_sub a a'
  linarith

theorem liftShapeR_lip {a a' t t' : ℝ} (ht : 0 ≤ t) :
    |liftShapeR a t - liftShapeR a' t'| ≤ |a - a'| + 2 * |t - t'| := by
  have h1 := le_abs_self (a - a')
  have h2 := neg_abs_le (a - a')
  have h3 := le_abs_self (t - t')
  have h4 := neg_abs_le (t - t')
  simp only [liftShapeR, stallFloor_eq, max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem liftShapeR_abs_le {a t : ℝ} (ht : 0 ≤ t) : |liftShapeR a t| ≤ |a| := by
  have h1 := le_abs_self a
  have h2 := neg_abs_le a
  simp only [liftShapeR, stallFloor_eq, max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

section box

variable {b : Box} {y : Fin 7 → ℝ}

theorem InBox.V_nonneg (h : InBox b y) : 0 ≤ b.V := (abs_nonneg _).trans h.vx
theorem InBox.D_nonneg (h : InBox b y) : 0 ≤ b.D := (abs_nonneg _).trans h.dx
theorem InBox.Q_nonneg (h : InBox b y) : 0 ≤ b.Q := (abs_nonneg _).trans h.q
theorem InBox.U_nonneg (h : InBox b y) : 0 ≤ b.U := (abs_nonneg _).trans h.u
theorem InBox.A_nonneg (h : InBox b y) : 0 ≤ b.A := (abs_nonneg _).trans h.alpha

theorem upR_nonneg (vx vz dx dz : ℝ) : 0 ≤ upR vx vz dx dz := le_max_right _ _

theorem InBox.up (h : InBox b y) : |upR (y 2) (y 3) (y 4) (y 5)| ≤ b.U := by
  rw [abs_of_nonneg (upR_nonneg _ _ _ _)]
  exact max_le ((le_abs_self _).trans h.u) h.U_nonneg

theorem InBox.lift (h : InBox b y) :
    |liftShapeR (alphaVR (y 2) (y 3) (y 4) (y 5)) (tauStall * upR (y 2) (y 3) (y 4) (y 5))|
      ≤ b.A := by
  refine (liftShapeR_abs_le ?_).trans h.alpha
  rw [tauStall_eq]; exact mul_nonneg (by norm_num) (upR_nonneg _ _ _ _)

theorem InBox.aN (h : InBox b y) : |aNR (y 2) (y 3) (y 4) (y 5)| ≤ kN * b.U * b.A := by
  have hkN : (0 : ℝ) ≤ kN := by rw [kN_eq]; norm_num
  rw [aNR, abs_mul, abs_mul, abs_of_nonneg hkN]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h.up hkN) h.lift (abs_nonneg _)
    (mul_nonneg hkN h.U_nonneg)

theorem kcoef_nonneg : 0 ≤ kN ∧ 0 ≤ tauStall ∧ 0 ≤ kD ∧ 0 ≤ kElev ∧ 0 ≤ kAlpha ∧ 0 ≤ kQ ∧
    thrustMax = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, thrustMax_eq⟩ <;>
    simp only [kN_eq, tauStall_eq, kD_eq, kElev_eq, kAlpha_eq, kQ_eq] <;> norm_num

end box

end Vibecheck.Ideal
