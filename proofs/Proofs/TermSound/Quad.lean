import Mathlib

/-! Robust invariance of a quadratic sublevel set `{q ≤ r²}` under a linear 2-state frame map `e ↦ A e + w`. -/

namespace Proofs.TermSound

structure Form where
  p11 : ℝ
  p12 : ℝ
  p22 : ℝ

def q (P : Form) (x y : ℝ) : ℝ := P.p11 * x ^ 2 + 2 * P.p12 * x * y + P.p22 * y ^ 2

def Form.PD (P : Form) : Prop := 0 < P.p11 ∧ P.p12 ^ 2 < P.p11 * P.p22

theorem q_nonneg_of {a b c : ℝ} (ha : 0 < a) (hd : b ^ 2 ≤ a * c) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have h1 : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
  have h2 : 0 ≤ (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by
    have := sq_nonneg (a * x + b * y); have := sq_nonneg y; nlinarith
  rw [← h1] at h2
  by_contra hv; push Not at hv; nlinarith

theorem q_nonneg {P : Form} (hP : P.PD) (x y : ℝ) : 0 ≤ q P x y :=
  q_nonneg_of hP.1 hP.2.le x y

theorem q_add_le {P : Form} (hP : P.PD) {t : ℝ} (ht : 0 < t) (x y u v : ℝ) :
    q P (x + u) (y + v) ≤ (1 + t) * q P x y + (1 + 1 / t) * q P u v := by
  have h0 := q_nonneg hP (t * x - u) (t * y - v)
  have e1 : q P (x + u) (y + v) = q P x y + 2 * (P.p11 * x * u + P.p12 * (x * v + y * u) + P.p22 * y * v)
      + q P u v := by unfold q; ring
  have e2 : q P (t * x - u) (t * y - v) = t ^ 2 * q P x y
      - 2 * t * (P.p11 * x * u + P.p12 * (x * v + y * u) + P.p22 * y * v) + q P u v := by unfold q; ring
  rw [e2] at h0
  rw [e1]
  have hq := q_nonneg hP u v
  set B := P.p11 * x * u + P.p12 * (x * v + y * u) + P.p22 * y * v
  have key : 2 * t * B ≤ t ^ 2 * q P x y + q P u v := by linarith
  have key' : 2 * B ≤ t * q P x y + q P u v / t := by
    have : t * q P x y + q P u v / t = (t ^ 2 * q P x y + q P u v) / t := by field_simp
    rw [this, le_div_iff₀ ht]; linarith
  have : (1 + 1 / t) * q P u v = q P u v + q P u v / t := by field_simp
  rw [this]; nlinarith

theorem q_le_box {P : Form} (h11 : 0 ≤ P.p11) (h22 : 0 ≤ P.p22) {u v a b : ℝ} (hu : |u| ≤ a) (hv : |v| ≤ b) :
    q P u v ≤ P.p11 * a ^ 2 + 2 * |P.p12| * a * b + P.p22 * b ^ 2 := by
  unfold q
  have hu2 : u ^ 2 ≤ a ^ 2 := by
    have := abs_nonneg u; rw [← sq_abs]; exact pow_le_pow_left₀ this hu 2
  have hv2 : v ^ 2 ≤ b ^ 2 := by
    have := abs_nonneg v; rw [← sq_abs v]; exact pow_le_pow_left₀ this hv 2
  have hx : P.p12 * u * v ≤ |P.p12| * a * b := by
    calc P.p12 * u * v ≤ |P.p12 * u * v| := le_abs_self _
      _ = |P.p12| * |u| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ |P.p12| * a * b := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hu (abs_nonneg _)) hv (abs_nonneg _)
        exact mul_nonneg (abs_nonneg _) ((abs_nonneg u).trans hu)
  nlinarith [mul_le_mul_of_nonneg_left hu2 h11, mul_le_mul_of_nonneg_left hv2 h22]

/-- Extent of a sublevel set along the first axis: `(p₁₁p₂₂ − p₁₂²) x² ≤ p₂₂ q x y`. -/
theorem q_extent_x {P : Form} (x y : ℝ) :
    (P.p11 * P.p22 - P.p12 ^ 2) * x ^ 2 ≤ P.p22 * q P x y := by
  have : P.p22 * q P x y = (P.p12 * x + P.p22 * y) ^ 2 + (P.p11 * P.p22 - P.p12 ^ 2) * x ^ 2 := by unfold q; ring
  rw [this]; nlinarith [sq_nonneg (P.p12 * x + P.p22 * y)]

/-- Extent of a sublevel set along the second axis: `(p₁₁p₂₂ − p₁₂²) y² ≤ p₁₁ q x y`. -/
theorem q_extent_y {P : Form} (x y : ℝ) :
    (P.p11 * P.p22 - P.p12 ^ 2) * y ^ 2 ≤ P.p11 * q P x y := by
  have : P.p11 * q P x y = (P.p11 * x + P.p12 * y) ^ 2 + (P.p11 * P.p22 - P.p12 ^ 2) * y ^ 2 := by unfold q; ring
  rw [this]; nlinarith [sq_nonneg (P.p11 * x + P.p12 * y)]

theorem abs_le_of_sq {x E : ℝ} (hE : 0 ≤ E) (h : x ^ 2 ≤ E ^ 2) : |x| ≤ E :=
  abs_le_of_sq_le_sq' h hE |> fun h => abs_le.mpr h

structure Mat where
  a11 : ℝ
  a12 : ℝ
  a21 : ℝ
  a22 : ℝ

/-- The entries of `c² P − Aᵀ P A`. -/
def m11 (P : Form) (A : Mat) (c2 : ℝ) : ℝ :=
  c2 * P.p11 - (A.a11 * A.a11 * P.p11 + 2 * A.a11 * A.a21 * P.p12 + A.a21 * A.a21 * P.p22)
def m12 (P : Form) (A : Mat) (c2 : ℝ) : ℝ :=
  c2 * P.p12 - (A.a11 * A.a12 * P.p11 + (A.a11 * A.a22 + A.a12 * A.a21) * P.p12 + A.a21 * A.a22 * P.p22)
def m22 (P : Form) (A : Mat) (c2 : ℝ) : ℝ :=
  c2 * P.p22 - (A.a12 * A.a12 * P.p11 + 2 * A.a12 * A.a22 * P.p12 + A.a22 * A.a22 * P.p22)

/-- Contraction: `c² P − Aᵀ P A ⪰ 0` gives `q (A e) ≤ c² q e`. -/
theorem q_contract {P : Form} {A : Mat} {c2 : ℝ} (h1 : 0 < m11 P A c2)
    (hd : m12 P A c2 ^ 2 ≤ m11 P A c2 * m22 P A c2) (x y : ℝ) :
    q P (A.a11 * x + A.a12 * y) (A.a21 * x + A.a22 * y) ≤ c2 * q P x y := by
  have h := q_nonneg_of h1 hd x y
  have e : c2 * q P x y - q P (A.a11 * x + A.a12 * y) (A.a21 * x + A.a22 * y)
      = m11 P A c2 * x ^ 2 + 2 * m12 P A c2 * x * y + m22 P A c2 * y ^ 2 := by
    unfold q m11 m12 m22; ring
  linarith

/-- **Robust one-step invariance** of the sublevel set `{q ≤ r²}` for `e ↦ A e + w`, `q w ≤ K`. -/
theorem q_robust_step {P : Form} (hP : P.PD) {A : Mat} {c2 t r2 K : ℝ} (hc2 : 0 ≤ c2)
    (h1 : 0 < m11 P A c2) (hd : m12 P A c2 ^ 2 ≤ m11 P A c2 * m22 P A c2) (ht : 0 < t)
    (hbudget : (1 + t) * c2 * r2 + (1 + 1 / t) * K ≤ r2)
    {x y u v : ℝ} (he : q P x y ≤ r2) (hw : q P u v ≤ K) :
    q P (A.a11 * x + A.a12 * y + u) (A.a21 * x + A.a22 * y + v) ≤ r2 := by
  have hadd := q_add_le hP ht (A.a11 * x + A.a12 * y) (A.a21 * x + A.a22 * y) u v
  have hc := q_contract h1 hd x y
  have ht1 : 0 ≤ 1 + t := by linarith
  have ht2 : 0 ≤ 1 + 1 / t := by positivity
  have := mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left he hc2)) ht1
  have := mul_le_mul_of_nonneg_left hw ht2
  nlinarith

end Proofs.TermSound
