import Proofs.Ideal

/-! Exact meaning of fixed-point operations: `+`, `-`, `max`, comparisons are exact; `*`, `div16` round down by less than `2⁻¹⁶`. -/

namespace Vibecheck.Ideal

open Vibecheck

noncomputable def ε : ℝ := 1 / 65536

theorem fxR_eq (a : Fx) : fxR a = (a.raw : ℝ) / 65536 := by
  simp [fxR, Fx.toRat]

theorem fxR_of_raw {a : Fx} {n : ℤ} (h : a.raw = n) : fxR a = (n : ℝ) / 65536 := by
  rw [fxR_eq, h]

@[simp] theorem fxR_add (a b : Fx) : fxR (a + b) = fxR a + fxR b := by
  simp only [fxR_eq, Fx.add_raw]; push_cast; ring

@[simp] theorem fxR_sub (a b : Fx) : fxR (a - b) = fxR a - fxR b := by
  simp only [fxR_eq, Fx.sub_raw]; push_cast; ring

@[simp] theorem fxR_neg (a : Fx) : fxR (-a) = -fxR a := by
  simp only [fxR_eq, Fx.neg_raw]; push_cast; ring

theorem fxR_lt (a b : Fx) : a < b ↔ fxR a < fxR b := by
  simp only [Fx.lt_def, fxR_eq]
  constructor
  · intro h; have : (a.raw : ℝ) < b.raw := by exact_mod_cast h
    linarith
  · intro h; have : (a.raw : ℝ) < b.raw := by linarith
    exact_mod_cast this

theorem fxR_le (a b : Fx) : a ≤ b ↔ fxR a ≤ fxR b := by
  have h := fxR_lt b a
  simp only [Fx.lt_def, Fx.le_def] at h ⊢
  rw [← not_lt, h, not_lt]

@[simp] theorem fxR_max (a b : Fx) : fxR (max a b) = max (fxR a) (fxR b) := by
  rw [Fx.max_def']
  by_cases h : a ≤ b
  · simp only [h, ↓reduceIte]; rw [max_eq_right ((fxR_le a b).1 h)]
  · simp only [h, ↓reduceIte]; rw [max_eq_left (le_of_lt (lt_of_not_ge (fun h' => h ((fxR_le a b).2 h'))))]

theorem floor_div_bounds (x : ℤ) (d : ℕ) (hd : 0 < d) :
    (x : ℝ) / d - 1 < ((x / (d : ℤ) : ℤ) : ℝ) ∧ ((x / (d : ℤ) : ℤ) : ℝ) ≤ (x : ℝ) / d := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have h1 := Int.mul_ediv_add_emod x d
  have h2 := Int.emod_nonneg x (ne_of_gt hd')
  have h3 := Int.emod_lt_of_pos x hd'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e1 : ((d : ℤ) : ℝ) * ((x / (d : ℤ) : ℤ) : ℝ) + ((x % (d : ℤ) : ℤ) : ℝ) = (x : ℝ) := by
    exact_mod_cast h1
  have e2 : (0 : ℝ) ≤ ((x % (d : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2
  have e3 : ((x % (d : ℤ) : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast h3
  push_cast at e1
  constructor
  · rw [div_sub_one (ne_of_gt hdR), div_lt_iff₀ hdR]; nlinarith
  · rw [le_div_iff₀ hdR]; nlinarith

theorem fxR_mul_bounds (a b : Fx) :
    fxR a * fxR b - ε < fxR (a * b) ∧ fxR (a * b) ≤ fxR a * fxR b := by
  have hraw := Fx.mul_raw a b
  obtain ⟨h1, h2⟩ := floor_div_bounds (a.raw * b.raw) 65536 (by norm_num)
  simp only [fxR_eq, hraw, ε]
  push_cast at h1 h2 ⊢
  constructor
  · have : (a.raw : ℝ) / 65536 * ((b.raw : ℝ) / 65536) - 1 / 65536
        = ((a.raw : ℝ) * b.raw / 65536 - 1) / 65536 := by ring
    rw [this]; exact div_lt_div_of_pos_right h1 (by norm_num)
  · have : (a.raw : ℝ) / 65536 * ((b.raw : ℝ) / 65536) = ((a.raw : ℝ) * b.raw / 65536) / 65536 := by
      ring
    rw [this]; exact div_le_div_of_nonneg_right h2 (by norm_num)

theorem fxR_mul_err (a b : Fx) : |fxR (a * b) - fxR a * fxR b| ≤ ε := by
  obtain ⟨h1, h2⟩ := fxR_mul_bounds a b
  rw [abs_le]; constructor <;> linarith

theorem fxR_dt_err (a : Fx) : |fxR (dt a) - fxR a / 16| ≤ ε := by
  obtain ⟨h1, h2⟩ := floor_div_bounds a.raw 16 (by norm_num)
  have hr : (dt a).raw = a.raw / 16 := rfl
  simp only [fxR_eq, hr, ε]
  push_cast at h1 h2 ⊢
  rw [abs_le]; constructor
  · have : (a.raw : ℝ) / 16 - 1 < ((a.raw / 16 : ℤ) : ℝ) := h1
    have : ((a.raw : ℝ) / 16 - 1) / 65536 ≤ ((a.raw / 16 : ℤ) : ℝ) / 65536 :=
      div_le_div_of_nonneg_right this.le (by norm_num)
    have e : ((a.raw : ℝ) / 16 - 1) / 65536 = (a.raw : ℝ) / 65536 / 16 - 1 / 65536 := by ring
    linarith
  · have : ((a.raw / 16 : ℤ) : ℝ) / 65536 ≤ ((a.raw : ℝ) / 16) / 65536 :=
      div_le_div_of_nonneg_right h2 (by norm_num)
    have e : ((a.raw : ℝ) / 16) / 65536 = (a.raw : ℝ) / 65536 / 16 := by ring
    have : (0 : ℝ) ≤ 1 / 65536 := by norm_num
    linarith

theorem g_eq : g = 642908 / 65536 := by rw [g, fxR_of_raw (n := 642908) (by decide)]; norm_num
theorem kN_eq : kN = 3670 / 65536 := by rw [kN, fxR_of_raw (n := 3670) (by decide)]; norm_num
theorem tauStall_eq : tauStall = 17563 / 65536 := by
  rw [tauStall, fxR_of_raw (n := 17563) (by decide)]; norm_num
theorem stallFloor_eq : stallFloor = 1 / 2 := by
  rw [stallFloor, fxR_of_raw (n := 32768) (by decide)]; norm_num
theorem kD_eq : kD = 39 / 65536 := by rw [kD, fxR_of_raw (n := 39) (by decide)]; norm_num
theorem thrustMax_eq : thrustMax = 5 := by
  rw [thrustMax, fxR_of_raw (n := 327680) (by decide)]; norm_num
theorem kElev_eq : kElev = 85 / 65536 := by rw [kElev, fxR_of_raw (n := 85) (by decide)]; norm_num
theorem kAlpha_eq : kAlpha = 235 / 65536 := by
  rw [kAlpha, fxR_of_raw (n := 235) (by decide)]; norm_num
theorem kQ_eq : kQ = 5505 / 65536 := by rw [kQ, fxR_of_raw (n := 5505) (by decide)]; norm_num
theorem fxR_half : fxR (0.5 : Fx) = 1 / 2 := by rw [fxR_of_raw (n := 32768) (by decide)]; norm_num
theorem fxR_three : fxR (3 : Fx) = 3 := by rw [fxR_of_raw (n := 196608) (by decide)]; norm_num
theorem fxR_zero : fxR (0 : Fx) = 0 := by rw [fxR_of_raw (n := 0) (by decide)]; norm_num

end Vibecheck.Ideal
