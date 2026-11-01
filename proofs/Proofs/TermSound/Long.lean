import Proofs.TermSound.Model

/-! Longitudinal block: robust invariance of `{q_L(u − u*(z), v_z − v_z*(z)) ≤ 1/4}`, the trim moving with altitude. -/

namespace Proofs.TermSound

noncomputable section

def eu (E0 : ℝ) (s : St) : ℝ := s.u - uStar E0 s.z
def evz (E0 : ℝ) (s : St) : ℝ := s.vz - vzStar E0 s.z

def PL : Form := ⟨28, -3, 1⟩
def AL : Mat := ⟨1 - h * kD, -(h * (g / ur)), h * (kG * kV), 1 - h * kG⟩
def r2L : ℝ := 1 / 4
def c2L : ℝ := 9964 / 10000
def tL : ℝ := 18 / 10000
/-- Valid for both kinds up to their altitude caps. -/
def DZ : ℝ := 44 / 1000
def wU : ℝ := dU + E1 * DZ
def wVZ : ℝ := dVZ + kV * E1 * DZ
def KL : ℝ := 28 * wU ^ 2 + 2 * 3 * wU * wVZ + wVZ ^ 2
def EU : ℝ := 23 / 200
def EVZ : ℝ := 61 / 100

theorem PL_pd : PL.PD := by norm_num [Form.PD, PL]

theorem AL_psd : 0 < m11 PL AL c2L ∧ m12 PL AL c2L ^ 2 ≤ m11 PL AL c2L * m22 PL AL c2L := by
  norm_num [m11, m12, m22, PL, AL, c2L, h, kD, g, ur, kG, kV]

theorem L_budget : (1 + tL) * c2L * r2L + (1 + 1 / tL) * KL ≤ r2L := by
  norm_num [tL, c2L, r2L, KL, wU, wVZ, dU, dVZ, E1, DZ, kV]

theorem eu_step (E0 : ℝ) (s : St) (du dz : ℝ) :
    (s.u + h * accU E0 s + du) - uStar E0 (s.z + h * s.vz + dz)
      = AL.a11 * eu E0 s + AL.a12 * evz E0 s + (du + E1 * (h * s.vz + dz)) := by
  simp only [accU, aZero, aZ, uStar, vzStar, eu, evz, AL]; ring

theorem evz_step (E0 : ℝ) (s : St) (dvz dz : ℝ) :
    (s.vz + h * accVz s + dvz) - vzStar E0 (s.z + h * s.vz + dz)
      = AL.a21 * eu E0 s + AL.a22 * evz E0 s + (dvz + kV * E1 * (h * s.vz + dz)) := by
  simp only [accVz, uStar, vzStar, eu, evz, AL]; ring

theorem long_step (E0 : ℝ) (s : St) {du dvz dz : ℝ} (hQ : q PL (eu E0 s) (evz E0 s) ≤ r2L)
    (hdz : |h * s.vz + dz| ≤ DZ) (hdu : |du| ≤ dU) (hdvz : |dvz| ≤ dVZ) :
    q PL ((s.u + h * accU E0 s + du) - uStar E0 (s.z + h * s.vz + dz))
      ((s.vz + h * accVz s + dvz) - vzStar E0 (s.z + h * s.vz + dz)) ≤ r2L := by
  rw [eu_step, evz_step]
  have hE1 : (0 : ℝ) ≤ E1 := by norm_num [E1]
  have hkV : (0 : ℝ) ≤ kV * E1 := by norm_num [E1, kV]
  have h1 : |du + E1 * (h * s.vz + dz)| ≤ wU := by
    calc _ ≤ |du| + |E1 * (h * s.vz + dz)| := abs_add_le _ _
      _ = |du| + E1 * |h * s.vz + dz| := by rw [abs_mul, abs_of_nonneg hE1]
      _ ≤ dU + E1 * DZ := by gcongr
      _ = wU := rfl
  have h2 : |dvz + kV * E1 * (h * s.vz + dz)| ≤ wVZ := by
    calc _ ≤ |dvz| + |kV * E1 * (h * s.vz + dz)| := abs_add_le _ _
      _ = |dvz| + kV * E1 * |h * s.vz + dz| := by rw [abs_mul, abs_of_nonneg hkV]
      _ ≤ dVZ + kV * E1 * DZ := by gcongr
      _ = wVZ := by rw [wVZ, mul_assoc]
  have hw : q PL (du + E1 * (h * s.vz + dz)) (dvz + kV * E1 * (h * s.vz + dz)) ≤ KL := by
    have := q_le_box (P := PL) (by norm_num [PL]) (by norm_num [PL]) h1 h2
    simpa [PL, KL] using this
  exact q_robust_step PL_pd (by norm_num [c2L]) AL_psd.1 AL_psd.2 (by norm_num [tL]) L_budget hQ hw

theorem long_extent {a b : ℝ} (hQ : q PL a b ≤ r2L) : |a| ≤ EU ∧ |b| ≤ EVZ := by
  have hx := q_extent_x (P := PL) a b
  have hy := q_extent_y (P := PL) a b
  simp only [PL] at hx hy
  constructor
  · apply abs_le_of_sq (by norm_num [EU]); simp only [PL] at hQ; norm_num [EU, r2L] at *; nlinarith
  · apply abs_le_of_sq (by norm_num [EVZ]); simp only [PL] at hQ; norm_num [EVZ, r2L] at *; nlinarith

end

end Proofs.TermSound
