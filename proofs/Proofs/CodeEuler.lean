import Proofs.EulerFlow

namespace Vibecheck.Ideal

open Vibecheck

theorem ε_pos : 0 < ε := by norm_num [ε]

theorem approx_mul {a b : Fx} {ra rb ea eb A B : ℝ} (ha : |fxR a - ra| ≤ ea)
    (hb : |fxR b - rb| ≤ eb) (hA : |ra| ≤ A) (hB : |fxR b| ≤ B) :
    |fxR (a * b) - ra * rb| ≤ B * ea + A * eb + ε := by
  have h1 := near_mul ha hb hA hB
  have h2 := fxR_mul_err a b
  have := abs_sub_le (fxR (a * b)) (fxR a * fxR b) (ra * rb)
  linarith

theorem approx_cmul {c b : Fx} {rb eb : ℝ} (hb : |fxR b - rb| ≤ eb) (hc : 0 ≤ fxR c) :
    |fxR (c * b) - fxR c * rb| ≤ fxR c * eb + ε := by
  have := approx_mul (a := c) (ra := fxR c) (ea := 0) (A := fxR c) (B := |fxR b|)
    (by simp) hb (by rw [abs_of_nonneg hc]) le_rfl
  linarith

theorem approx_exact_mul {a b : Fx} : |fxR (a * b) - fxR a * fxR b| ≤ ε := fxR_mul_err a b

noncomputable def aBox : Box := ⟨100, 101 / 100, 4, 202, 202⟩

section

variable (s : State)

theorem err_u : |fxR s.u - uR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 2 * ε := by
  have := near_add (approx_exact_mul (a := s.vx) (b := s.dx))
    (approx_exact_mul (a := s.vz) (b := s.dz))
  simp only [State.u, fxR_add, uR] at *
  linarith

theorem err_up :
    |fxR (max s.u 0) - upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 2 * ε := by
  rw [fxR_max, fxR_zero, upR]; exact near_max0 (err_u s)

theorem err_alpha :
    |fxR s.alphaV - alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 2 * ε := by
  have := near_sub (approx_exact_mul (a := s.vx) (b := s.dz))
    (approx_exact_mul (a := s.vz) (b := s.dx))
  simp only [State.alphaV, fxR_sub, alphaVR] at *
  linarith

theorem tau_up_nonneg : 0 ≤ fxR (P.tauStall * max s.u 0) := by
  rw [fxR_eq]
  apply div_nonneg _ (by norm_num)
  have h1 : (0 : ℤ) ≤ (max s.u 0).raw := by rw [Fx.max_raw]; exact le_max_right _ _
  have h2 : (0 : ℤ) ≤ (P.tauStall * max s.u 0).raw := by
    rw [Fx.mul_raw]; exact Int.ediv_nonneg (mul_nonneg (by decide) h1) (by decide)
  exact_mod_cast h2

theorem liftShape_err (a t : Fx) :
    |fxR (liftShape a t) - liftShapeR (fxR a) (fxR t)| ≤ ε := by
  have hs : fxR P.stallFloor = 1 / 2 := stallFloor_eq
  obtain ⟨m1, m2⟩ := fxR_mul_bounds P.stallFloor t
  rw [hs] at m1 m2
  have he := ε_pos
  have c1 := fxR_lt t a
  have c2 := fxR_lt a (-t)
  rw [fxR_neg] at c2
  simp only [liftShape, liftShapeR, stallFloor_eq]
  by_cases h1 : t < a
  · simp only [h1, c1.1 h1, ite_true, fxR_max, fxR_sub, max_def]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · have h1' : ¬ fxR t < fxR a := fun h => h1 (c1.2 h)
    by_cases h2 : a < -t
    · simp only [h1, h1', h2, c2.1 h2, ite_true, ite_false, fxR_neg, fxR_max, fxR_sub, max_def]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · have h2' : ¬ fxR a < -fxR t := fun h => h2 (c2.2 h)
      simp only [h1, h1', h2, h2', ite_false, sub_self, abs_zero]
      exact he.le

end

section

variable {s : State}

theorem abs_le_of_sq {x c : ℝ} (hc : 0 ≤ c) (h : x ^ 2 ≤ c ^ 2) : |x| ≤ c := by
  rw [← abs_of_nonneg hc]; exact sq_le_sq.1 h

theorem abox_of (hvx : |fxR s.vx| ≤ 100) (hvz : |fxR s.vz| ≤ 100) (hq : |fxR s.q| ≤ 4)
    (hn : |fxR s.dx ^ 2 + fxR s.dz ^ 2 - 1| ≤ 1 / 100) : InBox aBox (toReal s) := by
  have hn' := (abs_le.1 hn).2
  have hdx : |fxR s.dx| ≤ 101 / 100 :=
    abs_le_of_sq (by norm_num) (by nlinarith [sq_nonneg (fxR s.dz)])
  have hdz : |fxR s.dz| ≤ 101 / 100 :=
    abs_le_of_sq (by norm_num) (by nlinarith [sq_nonneg (fxR s.dx)])
  have p1 : |fxR s.vx * fxR s.dx| ≤ 100 * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hvx hdx (abs_nonneg _) (by norm_num)
  have p2 : |fxR s.vz * fxR s.dz| ≤ 100 * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hvz hdz (abs_nonneg _) (by norm_num)
  have p3 : |fxR s.vx * fxR s.dz| ≤ 100 * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hvx hdz (abs_nonneg _) (by norm_num)
  have p4 : |fxR s.vz * fxR s.dx| ≤ 100 * (101 / 100) := by
    rw [abs_mul]; exact mul_le_mul hvz hdx (abs_nonneg _) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [toReal, aBox, uR, alphaVR] <;>
    simp only [Matrix.cons_val, Fin.isValue]
  · exact hvx
  · exact hvz
  · exact hdx
  · exact hdz
  · exact hq
  · have := abs_add_le (fxR s.vx * fxR s.dx) (fxR s.vz * fxR s.dz); linarith
  · have := abs_sub (fxR s.vx * fxR s.dz) (fxR s.vz * fxR s.dx); linarith

end

section accel

variable (s : State)

theorem err_lift :
    |fxR (liftShape s.alphaV (P.tauStall * max s.u 0))
      - liftShapeR (alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))
          (tauStall * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))| ≤ 7 * ε := by
  have h1 := liftShape_err s.alphaV (P.tauStall * max s.u 0)
  have h2 := liftShapeR_lip (a := fxR s.alphaV)
    (a' := alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))
    (t' := tauStall * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)) (tau_up_nonneg s)
  have htau : (0 : ℝ) ≤ tauStall := kcoef_nonneg.2.1
  have h3 : |fxR (P.tauStall * max s.u 0) - tauStall * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)|
      ≤ tauStall * (2 * ε) + ε := approx_cmul (err_up s) htau
  have h4 := err_alpha s
  have := abs_sub_le (fxR (liftShape s.alphaV (P.tauStall * max s.u 0)))
    (liftShapeR (fxR s.alphaV) (fxR (P.tauStall * max s.u 0)))
    (liftShapeR (alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))
          (tauStall * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)))
  have hn : tauStall * (2 * ε) + ε ≤ 2 * ε := by rw [tauStall_eq]; norm_num [ε]
  linarith

variable {s}

theorem err_aN (hb : InBox aBox (toReal s)) :
    |fxR (P.kN * max s.u 0 * liftShape s.alphaV (P.tauStall * max s.u 0))
      - aNR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 330 * ε := by
  have hkN : (0 : ℝ) ≤ kN := kcoef_nonneg.1
  have hU : |upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 202 := by
    simpa [toReal, aBox] using hb.up
  have hL : |liftShapeR (alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))
      (tauStall * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz))| ≤ 202 := by
    simpa [toReal, aBox] using hb.lift
  have k1 : |fxR (P.kN * max s.u 0) - kN * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)|
      ≤ kN * (2 * ε) + ε := approx_cmul (err_up s) hkN
  have kA : |kN * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ kN * 202 := by
    rw [abs_mul, abs_of_nonneg hkN]; exact mul_le_mul_of_nonneg_left hU hkN
  have hLf := abs_le_of_near (err_lift s) hL
  have := approx_mul k1 (err_lift s) kA hLf
  have hn : (202 + 7 * ε) * (kN * (2 * ε) + ε) + kN * 202 * (7 * ε) + ε ≤ 330 * ε := by
    rw [kN_eq]; norm_num [ε]
  simp only [aNR]
  linarith

theorem accel_ax (thr : Fx) : (accel s thr).ax = P.thrustMax * thr * s.dx
    - P.kN * max s.u 0 * liftShape s.alphaV (P.tauStall * max s.u 0) * s.dz
    - P.kD * max s.u 0 * s.vx := rfl

theorem accel_az (thr : Fx) : (accel s thr).az = P.thrustMax * thr * s.dz
    + P.kN * max s.u 0 * liftShape s.alphaV (P.tauStall * max s.u 0) * s.dx
    - P.kD * max s.u 0 * s.vz - P.g := rfl

theorem accel_qdot (thr : Fx) : (accel s thr).qdot = P.kElev * max s.u 0 * max s.u 0 * s.elev
    - P.kAlpha * max s.u 0 * s.alphaV - P.kQ * max s.u 0 * s.q := rfl

theorem err_thrust {thr : Fx} (hthr : 0 ≤ fxR thr ∧ fxR thr ≤ 1) :
    |fxR (P.thrustMax * thr) - thrustMax * fxR thr| ≤ ε ∧ |thrustMax * fxR thr| ≤ 5 := by
  refine ⟨approx_exact_mul, ?_⟩
  rw [thrustMax_eq, abs_of_nonneg (by linarith [hthr.1])]; linarith [hthr.2]

theorem err_drag (hb : InBox aBox (toReal s)) (v : Fx) (hv : |fxR v| ≤ 100) :
    |fxR (P.kD * max s.u 0 * v) - kD * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz) * fxR v|
      ≤ 102 * ε := by
  have hkD : (0 : ℝ) ≤ kD := kcoef_nonneg.2.2.1
  have hU : |upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 202 := by
    simpa [toReal, aBox] using hb.up
  have k1 : |fxR (P.kD * max s.u 0) - kD * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)|
      ≤ kD * (2 * ε) + ε := approx_cmul (err_up s) hkD
  have kA : |kD * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ kD * 202 := by
    rw [abs_mul, abs_of_nonneg hkD]; exact mul_le_mul_of_nonneg_left hU hkD
  have := approx_mul k1 (show |fxR v - fxR v| ≤ 0 by simp) kA hv
  have hn : 100 * (kD * (2 * ε) + ε) + kD * 202 * 0 + ε ≤ 102 * ε := by
    rw [kD_eq]; norm_num [ε]
  linarith

theorem err_ax (hb : InBox aBox (toReal s)) {thr : Fx} (hthr : 0 ≤ fxR thr ∧ fxR thr ≤ 1) :
    |fxR (accel s thr).ax - axR (fxR thr) (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)|
      ≤ 440 * ε := by
  have hdx : |fxR s.dx| ≤ 101 / 100 := by simpa [toReal, aBox] using hb.dx
  have hdz : |fxR s.dz| ≤ 101 / 100 := by simpa [toReal, aBox] using hb.dz
  have hvx : |fxR s.vx| ≤ 100 := by simpa [toReal, aBox] using hb.vx
  have haN : |aNR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ kN * 202 * 202 := by
    simpa [toReal, aBox] using hb.aN
  obtain ⟨ht1, ht2⟩ := err_thrust hthr
  have t1 := approx_mul ht1 (show |fxR s.dx - fxR s.dx| ≤ 0 by simp) ht2 hdx
  have t2 := approx_mul (err_aN hb) (show |fxR s.dz - fxR s.dz| ≤ 0 by simp) haN hdz
  have t3 := err_drag hb s.vx hvx
  have := near_sub (near_sub t1 t2) t3
  rw [accel_ax, fxR_sub, fxR_sub]
  simp only [axR]
  have he := ε_pos
  linarith

theorem err_az (hb : InBox aBox (toReal s)) {thr : Fx} (hthr : 0 ≤ fxR thr ∧ fxR thr ≤ 1) :
    |fxR (accel s thr).az - azR (fxR thr) (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)|
      ≤ 440 * ε := by
  have hdx : |fxR s.dx| ≤ 101 / 100 := by simpa [toReal, aBox] using hb.dx
  have hdz : |fxR s.dz| ≤ 101 / 100 := by simpa [toReal, aBox] using hb.dz
  have hvz : |fxR s.vz| ≤ 100 := by simpa [toReal, aBox] using hb.vz
  have haN : |aNR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ kN * 202 * 202 := by
    simpa [toReal, aBox] using hb.aN
  obtain ⟨ht1, ht2⟩ := err_thrust hthr
  have t1 := approx_mul ht1 (show |fxR s.dz - fxR s.dz| ≤ 0 by simp) ht2 hdz
  have t2 := approx_mul (err_aN hb) (show |fxR s.dx - fxR s.dx| ≤ 0 by simp) haN hdx
  have t3 := err_drag hb s.vz hvz
  have := near_sub (near_sub (near_add t1 t2) t3) (show |fxR P.g - g| ≤ 0 by simp [g])
  rw [accel_az, fxR_sub, fxR_sub, fxR_add]
  simp only [azR]
  have he := ε_pos
  linarith

theorem err_cup (hb : InBox aBox (toReal s)) {c : Fx} (hc : 0 ≤ fxR c) (w : Fx) {rw ew W : ℝ}
    (hw : |fxR w - rw| ≤ ew) (hW : |fxR w| ≤ W) :
    |fxR (c * max s.u 0 * w) - fxR c * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz) * rw|
      ≤ W * (fxR c * (2 * ε) + ε) + fxR c * 202 * ew + ε := by
  have hU : |upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 202 := by
    simpa [toReal, aBox] using hb.up
  have k1 := approx_cmul (c := c) (err_up s) hc
  have kA : |fxR c * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ fxR c * 202 := by
    rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hU hc
  exact approx_mul k1 hw kA hW

theorem err_qdot (hb : InBox aBox (toReal s)) (he : |fxR s.elev| ≤ 1) (thr : Fx) :
    |fxR (accel s thr).qdot
      - qdotR (fxR s.elev) (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz) (fxR s.q)| ≤ 420 * ε := by
  obtain ⟨-, -, -, hkE, hkA, hkQ, -⟩ := kcoef_nonneg
  have hU : |upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 202 := by
    simpa [toReal, aBox] using hb.up
  have hal : |alphaVR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ 202 := by
    simpa [toReal, aBox] using hb.alpha
  have hq : |fxR s.q| ≤ 4 := by simpa [toReal, aBox] using hb.q
  have k2 := err_cup hb (c := P.kElev) hkE (max s.u 0) (err_up s) (abs_le_of_near (err_up s) hU)
  have kA2 : |kElev * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)
      * upR (fxR s.vx) (fxR s.vz) (fxR s.dx) (fxR s.dz)| ≤ kElev * 202 * 202 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hkE]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hU hkE) hU (abs_nonneg _) (by positivity)
  have k3 := approx_mul k2 (show |fxR s.elev - fxR s.elev| ≤ 0 by simp) kA2 he
  have k5 := err_cup hb (c := P.kAlpha) hkA s.alphaV (err_alpha s)
    (abs_le_of_near (err_alpha s) hal)
  have k7 := err_cup hb (c := P.kQ) hkQ s.q (show |fxR s.q - fxR s.q| ≤ 0 by simp) hq
  have := near_sub (near_sub k3 k5) k7
  rw [accel_qdot, fxR_sub, fxR_sub]
  simp only [qdotR]
  have hn : 1 * ((202 + 2 * ε) * (kElev * (2 * ε) + ε) + kElev * 202 * (2 * ε) + ε)
      + kElev * 202 * 202 * 0 + ε
      + ((202 + 2 * ε) * (kAlpha * (2 * ε) + ε) + kAlpha * 202 * (2 * ε) + ε)
      + (4 * (kQ * (2 * ε) + ε) + kQ * 202 * 0 + ε) ≤ 420 * ε := by
    rw [kElev_eq, kAlpha_eq, kQ_eq]; norm_num [ε]
  exact this.trans hn

end accel

section rotate

theorem err_k {ex ez : Fx} {exR ezR : ℝ} (hx : |fxR ex - exR| ≤ 17 / 16 * ε)
    (hz : |fxR ez - ezR| ≤ 17 / 16 * ε) (bx : |exR| ≤ 104 / 100) (bz : |ezR| ≤ 104 / 100)
    (hn : 99 / 100 ≤ exR * exR + ezR * ezR ∧ exR * exR + ezR * ezR ≤ 1073125 / 1000000) :
    |fxR ((3 - (ex * ex + ez * ez)) * 0.5) - (3 - (exR * exR + ezR * ezR)) * (1 / 2)|
      ≤ 5 * ε := by
  have sx := approx_mul hx hx bx (abs_le_of_near hx bx)
  have sz := approx_mul hz hz bz (abs_le_of_near hz bz)
  have hS := near_sub (show |fxR (3 : Fx) - 3| ≤ 0 by rw [fxR_three]; simp) (near_add sx sz)
  rw [← fxR_add, ← fxR_sub] at hS
  have hA : |3 - (exR * exR + ezR * ezR)| ≤ 201 / 100 := by
    rw [abs_le]; constructor <;> linarith [hn.1, hn.2]
  have := approx_mul hS (show |fxR (0.5 : Fx) - 1 / 2| ≤ 0 by rw [fxR_half]; simp) hA
    (show |fxR (0.5 : Fx)| ≤ 1 / 2 by rw [fxR_half]; norm_num)
  have hnum : 1 / 2 * (0 + ((104 / 100 + 17 / 16 * ε) * (17 / 16 * ε) + 104 / 100 * (17 / 16 * ε) + ε
      + ((104 / 100 + 17 / 16 * ε) * (17 / 16 * ε) + 104 / 100 * (17 / 16 * ε) + ε)))
      + 201 / 100 * 0 + ε ≤ 5 * ε := by norm_num [ε]
  linarith

theorem err_scale {ex k : Fx} {exR kR : ℝ} (hx : |fxR ex - exR| ≤ 17 / 16 * ε)
    (hk : |fxR k - kR| ≤ 5 * ε) (bx : |exR| ≤ 104 / 100) (bk : |kR - 1| ≤ 365625 / 10000000) :
    |fxR (ex * k) - exR| ≤ 39 / 1000 := by
  have bk' : |kR| ≤ 1005 / 1000 + 4 / 100 := by
    rw [abs_le] at bk ⊢; constructor <;> linarith [bk.1, bk.2]
  have := approx_mul hx hk bx (abs_le_of_near hk bk')
  have h2 : |exR * kR - exR| ≤ 104 / 100 * (365625 / 10000000) := by
    have : exR * kR - exR = exR * (kR - 1) := by ring
    rw [this, abs_mul]; exact mul_le_mul bx bk (abs_nonneg _) (by norm_num)
  have h3 := abs_sub_le (fxR (ex * k)) (exR * kR) exR
  have hnum : (1005 / 1000 + 4 / 100 + 5 * ε) * (17 / 16 * ε) + 104 / 100 * (5 * ε) + ε
      + 104 / 100 * (365625 / 10000000) ≤ 39 / 1000 := by norm_num [ε]
  linarith

theorem err_dtmul (q d : Fx) : |fxR (dt (q * d)) - fxR q * fxR d / 16| ≤ 17 / 16 * ε := by
  have h1 := fxR_dt_err (q * d)
  have h2 := fxR_mul_err q d
  have : |fxR (q * d) / 16 - fxR q * fxR d / 16| ≤ ε / 16 := by
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]; linarith
  have := abs_sub_le (fxR (dt (q * d))) (fxR (q * d) / 16) (fxR q * fxR d / 16)
  linarith

variable {dx dz q : Fx}

theorem rot_facts (hq : |fxR q| ≤ 4) (hn : |fxR dx ^ 2 + fxR dz ^ 2 - 1| ≤ 1 / 100) :
    let exR := fxR dx - fxR q * fxR dz / 16
    let ezR := fxR dz + fxR q * fxR dx / 16
    |exR| ≤ 104 / 100 ∧ |ezR| ≤ 104 / 100 ∧
      (99 / 100 ≤ exR * exR + ezR * ezR ∧ exR * exR + ezR * ezR ≤ 1073125 / 1000000) ∧
      |(3 - (exR * exR + ezR * ezR)) * (1 / 2) - 1| ≤ 365625 / 10000000 := by
  intro exR ezR
  have hid : exR * exR + ezR * ezR = (fxR dx ^ 2 + fxR dz ^ 2) * (1 + fxR q ^ 2 / 256) := by
    simp only [exR, ezR]; ring
  have hq2 : fxR q ^ 2 ≤ 16 := by
    have := sq_abs (fxR q); nlinarith [abs_nonneg (fxR q)]
  have hn1 := (abs_le.1 hn).1
  have hn2 := (abs_le.1 hn).2
  have hq0 := sq_nonneg (fxR q)
  have hS : 99 / 100 ≤ exR * exR + ezR * ezR ∧ exR * exR + ezR * ezR ≤ 1073125 / 1000000 := by
    rw [hid]; constructor <;> nlinarith
  refine ⟨abs_le_of_sq (by norm_num) ?_, abs_le_of_sq (by norm_num) ?_, hS, ?_⟩
  · nlinarith [mul_self_nonneg ezR]
  · nlinarith [mul_self_nonneg exR]
  · rw [abs_le]; constructor <;> linarith [hS.1, hS.2]

theorem rotate_fst : (rotate dx dz q).1 = (dx - dt (q * dz)) *
    ((3 - ((dx - dt (q * dz)) * (dx - dt (q * dz)) + (dz + dt (q * dx)) * (dz + dt (q * dx))))
      * 0.5) := rfl

theorem rotate_snd : (rotate dx dz q).2 = (dz + dt (q * dx)) *
    ((3 - ((dx - dt (q * dz)) * (dx - dt (q * dz)) + (dz + dt (q * dx)) * (dz + dt (q * dx))))
      * 0.5) := rfl

theorem err_rotate (hq : |fxR q| ≤ 4) (hn : |fxR dx ^ 2 + fxR dz ^ 2 - 1| ≤ 1 / 100) :
    |fxR (rotate dx dz q).1 - (fxR dx - fxR q * fxR dz / 16)| ≤ 39 / 1000 ∧
    |fxR (rotate dx dz q).2 - (fxR dz + fxR q * fxR dx / 16)| ≤ 39 / 1000 := by
  obtain ⟨bx, bz, hS, hk1⟩ := rot_facts hq hn
  have hx : |fxR (dx - dt (q * dz)) - (fxR dx - fxR q * fxR dz / 16)| ≤ 17 / 16 * ε := by
    rw [fxR_sub]
    have := err_dtmul q dz
    rw [show fxR dx - fxR (dt (q * dz)) - (fxR dx - fxR q * fxR dz / 16)
      = -(fxR (dt (q * dz)) - fxR q * fxR dz / 16) by ring, abs_neg]
    exact this
  have hz : |fxR (dz + dt (q * dx)) - (fxR dz + fxR q * fxR dx / 16)| ≤ 17 / 16 * ε := by
    rw [fxR_add]
    have := err_dtmul q dx
    rw [show fxR dz + fxR (dt (q * dx)) - (fxR dz + fxR q * fxR dx / 16)
      = fxR (dt (q * dx)) - fxR q * fxR dx / 16 by ring]
    exact this
  have hk := err_k hx hz bx bz hS
  exact ⟨rotate_fst ▸ err_scale hx hk bx hk1, rotate_snd ▸ err_scale hz hk bz hk1⟩

end rotate

theorem stepAir_fly (s : State) (u : Input) (h : (stepAir s u).phase = .air) :
    stepAir s u =
      { x := s.x + dt s.vx, h := s.h + dt s.vz,
        vx := s.vx + dt (accel s (effThrottle s u)).ax,
        vz := s.vz + dt (accel s (effThrottle s u)).az,
        dx := (rotate s.dx s.dz s.q).1, dz := (rotate s.dx s.dz s.q).2,
        q := s.q + dt (accel s (effThrottle s u)).qdot,
        elev := stepElev s.elev u.stick,
        fuel := max 0 (s.fuel - dt (effThrottle s u)),
        phase := .air } := by
  rcases hr : rotate s.dx s.dz s.q with ⟨dx', dz'⟩
  simp only [stepAir, hr] at h ⊢
  split_ifs at h ⊢ <;> first | rfl | (split at h <;> simp at h)

theorem step_comp (a b : Fx) {r e : ℝ} (h : |fxR b - r| ≤ e) :
    |fxR (a + dt b) - (fxR a + Δt * r)| ≤ ε + e / 16 := by
  have h1 := fxR_dt_err b
  rw [fxR_add]
  have : fxR a + fxR (dt b) - (fxR a + Δt * r) = (fxR (dt b) - fxR b / 16) + (fxR b - r) / 16 := by
    simp only [Δt]; ring
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]; linarith

theorem effThrottle_mem (s : State) (u : Input) (h : 0 ≤ fxR u.throttle ∧ fxR u.throttle ≤ 1) :
    0 ≤ fxR (effThrottle s u) ∧ fxR (effThrottle s u) ≤ 1 := by
  unfold effThrottle; split_ifs
  · exact h
  · rw [fxR_zero]; norm_num

/-- Rounding bounds of Theorem A for `(x, h, vx, vz, dx, dz, q)`; units m, m/s, 1, rad/s. -/
noncomputable def δA : Fin 7 → ℝ :=
  ![1 / 65536, 1 / 65536, 1 / 2048, 1 / 2048, 39 / 1000, 39 / 1000, 1 / 2048]

/-- **Theorem A.** On the flying branch, each coordinate of `stepAir s u` is within `δA i` of
the real Euler step of `F` (actuators: elevator `s.elev`, delivered throttle). -/
theorem stepAir_near_euler (s : State) (u : Input)
    (hvx : |fxR s.vx| ≤ 100) (hvz : |fxR s.vz| ≤ 100) (hq : |fxR s.q| ≤ 4)
    (hd : |fxR s.dx ^ 2 + fxR s.dz ^ 2 - 1| ≤ 1 / 100) (he : |fxR s.elev| ≤ 1)
    (hthr : 0 ≤ fxR u.throttle ∧ fxR u.throttle ≤ 1)
    (hfly : (stepAir s u).phase = .air) (i : Fin 7) :
    |toReal (stepAir s u) i - euler (fxR s.elev) (fxR (effThrottle s u)) (toReal s) i|
      ≤ δA i := by
  have hb := abox_of hvx hvz hq hd
  have ht := effThrottle_mem s u hthr
  have hε : ε = 1 / 65536 := rfl
  rw [stepAir_fly s u hfly]
  fin_cases i <;>
    simp only [toReal, euler, F, δA, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
  · have := step_comp s.x s.vx (show |fxR s.vx - fxR s.vx| ≤ 0 by simp); linarith
  · have := step_comp s.h s.vz (show |fxR s.vz - fxR s.vz| ≤ 0 by simp); linarith
  · have := step_comp s.vx _ (err_ax hb ht); linarith
  · have := step_comp s.vz _ (err_az hb ht); linarith
  · have := (err_rotate hq hd).1
    have e : fxR s.dx + Δt * -(fxR s.q * fxR s.dz) = fxR s.dx - fxR s.q * fxR s.dz / 16 := by
      simp only [Δt]; ring
    rw [e]; exact this
  · have := (err_rotate hq hd).2
    have e : fxR s.dz + Δt * (fxR s.q * fxR s.dx) = fxR s.dz + fxR s.q * fxR s.dx / 16 := by
      simp only [Δt]; ring
    rw [e]; exact this
  · have := step_comp s.q _ (err_qdot hb he (effThrottle s u)); linarith

end Vibecheck.Ideal
