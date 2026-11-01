import Proofs.Continuous.Tables

/-! Pointwise clause: on a region of the escape climb, the vertical acceleration of the real-number vector field
is at least 0.6 m/s² (the one-tick vz bound needs 0.462 m/s² at every substep, see `Jsb.incr_of_substeps`). -/

namespace Jsb.Cont
open Jsb.C172 Real

/-- `atan2 w u` lies between `sin` and `tan` of itself for `u > 0`, `w ≥ 0`. -/
theorem atan2R_bounds {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w) :
    w / √(u * u + w * w) ≤ atan2R w u ∧ atan2R w u ≤ w / u := by
  have hz : (⟨u, w⟩ : ℂ) ≠ 0 := fun h => by simp [Complex.ext_iff] at h; linarith
  have hnorm : ‖(⟨u, w⟩ : ℂ)‖ = √(u * u + w * w) := by simp [Complex.norm_def, Complex.normSq_apply]
  have hpos : 0 ≤ atan2R w u := Complex.arg_nonneg_iff.mpr hw
  have habs : |atan2R w u| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  constructor
  · have := Complex.sin_arg (⟨u, w⟩ : ℂ)
    rw [hnorm] at this
    simp only at this
    rw [← this]; exact sin_le hpos
  · have ht := Complex.tan_arg (⟨u, w⟩ : ℂ)
    simp only at ht
    have e : atan2R w u = arctan (w / u) := by
      rw [← ht]; exact (arctan_tan (by linarith [abs_lt.mp habs]) (abs_lt.mp habs).2).symm
    rw [e]; exact arctan_le_self (div_nonneg hw hu.le)

/-- The body-to-world rotation of the aerodynamic and thrust forces, in wind-axis form. -/
theorem rot_shape (dx dz vx vz u w vt m L D T n2 : ℝ) (hvt : vt ≠ 0) (hm : m ≠ 0)
    (h1 : dz * w + dx * u = vx * n2) (h2 : dx * w - dz * u = -(vz * n2)) :
    dz * ((L * (w / vt) - D * (u / vt) + T) / m) - dx * ((-(D * (w / vt)) - L * (u / vt)) / m) =
      ((L * vx - D * vz) * n2 / vt + dz * T) / m := by
  field_simp
  linear_combination L * h1 + D * h2



/-- The numeric core: lift coefficient sum at least 12.2, drag at most 2.58 (per unit dynamic pressure). -/
theorem au_core (dz vx vz h ρ M vt n2 Lt Dt T : ℝ) (hvx0 : 37 ≤ vx) (hvz1 : vz ≤ vx / 20) (hh0 : 0 ≤ h)
    (hρ : 71083 / 65536 ≤ ρ) (hvt : 36.9 ≤ vt) (hvt2 : vt * vt = M) (hn : 0.998 ≤ n2) (hdz : 0 ≤ dz)
    (hL : ρ * M / 2000 * 12.2 ≤ Lt) (hD0 : 0 ≤ Dt) (hD1 : Dt ≤ ρ * M / 2000 * 2.58) (hT : 0 ≤ T) :
    3 / 5 ≤ ((Lt * vx - Dt * vz) * n2 / vt + dz * T) / (27943 / 32768) - (643183 / 65536 - h / 1000 / (21295551 / 65536)) +
      vx * vx / 1000 / (208998793 / 32768 + h / 1000) + vx / (449362085 / 65536) + 2223 / 65536 := by
  set Q := ρ * M / 2000 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ, ← hvt2]; nlinarith
  have hvt0 : 0 < vt := by linarith
  -- (L vx - D vz) ≥ Q vx (12.2 - 2.58 / 20)
  have hLD : Q * vx * 12.071 ≤ Lt * vx - Dt * vz := by
    rcases le_or_gt vz 0 with hz | hz
    · nlinarith [mul_nonneg hD0 (by linarith : 0 ≤ -vz)]
    · nlinarith [mul_le_mul_of_nonneg_right hD1 hz.le]
  have hX : ρ * vt * vx * 12.071 * 0.998 / 2000 ≤ (Lt * vx - Dt * vz) * n2 / vt := by
    rw [le_div_iff₀ hvt0]
    have h1 : 0 ≤ Q * vx * 12.071 := by positivity
    have := mul_le_mul hLD hn (by norm_num) (by linarith)
    have e : ρ * vt * vx * 12.071 * 0.998 / 2000 * vt = Q * vx * 12.071 * 0.998 := by rw [hQ, ← hvt2]; ring
    rw [e]; linarith
  have hX2 : 8.91 ≤ ρ * vt * vx * 12.071 * 0.998 / 2000 := by
    have : (71083 / 65536 : ℝ) * 36.9 * 37 ≤ ρ * vt * vx := by
      have := mul_le_mul hρ hvt (by norm_num) (by linarith)
      exact mul_le_mul this hvx0 (by norm_num) (by positivity)
    nlinarith
  have hrest : 0 ≤ vx * vx / 1000 / (208998793 / 32768 + h / 1000) + vx / (449362085 / 65536) := by positivity
  have hg : 0 ≤ h / 1000 / (21295551 / 65536) := by positivity
  have hdT : 0 ≤ dz * T := mul_nonneg hdz hT
  have : 8.91 ≤ (Lt * vx - Dt * vz) * n2 / vt + dz * T := by linarith
  have : 8.91 / (27943 / 32768) ≤ ((Lt * vx - Dt * vz) * n2 / vt + dz * T) / (27943 / 32768) :=
    div_le_div_of_nonneg_right this (by norm_num)
  norm_num at this ⊢
  linarith

/-- Region of the vertical clause, in the state's own quantities: altitude, speed, flight path, attitude norm,
angle of attack (via `w / |v|` from below and `w / u` from above), pitch rate, alpha rate, elevator, rpm. -/
structure AuRegion (s : StateOf ℝ) (e : ℝ) : Prop where
  h_lo : 600 ≤ s.h
  h_hi : s.h ≤ 1250
  vx_lo : 37 ≤ s.vx
  vx_hi : s.vx ≤ 45
  vz_lo : -(s.vx / 10) ≤ s.vz
  vz_hi : s.vz ≤ s.vx / 20
  n_lo : 0.998 ≤ s.dx * s.dx + s.dz * s.dz
  n_hi : s.dx * s.dx + s.dz * s.dz ≤ 1.002
  dz_nn : 0 ≤ s.dz
  u_pos : 0 < s.vx * s.dx + s.vz * s.dz
  alpha_lo : 0.1 * √((s.vx * s.dx + s.vz * s.dz) * (s.vx * s.dx + s.vz * s.dz) +
      (s.vx * s.dz - s.vz * s.dx) * (s.vx * s.dz - s.vz * s.dx)) ≤ s.vx * s.dz - s.vz * s.dx
  alpha_hi : s.vx * s.dz - s.vz * s.dx ≤ 0.2 * (s.vx * s.dx + s.vz * s.dz)
  q_lo : 0 ≤ s.q
  q_hi : s.q ≤ 0.5
  adot : |(s.vx * s.dx + s.vz * s.dz) * s.wdot - (s.vx * s.dz - s.vz * s.dx) * s.udot| ≤
      0.3 * ((s.vx * s.dx + s.vz * s.dz) * (s.vx * s.dx + s.vz * s.dz) +
        (s.vx * s.dz - s.vz * s.dx) * (s.vx * s.dz - s.vz * s.dx))
  stall : s.stall = 0
  e_lo : 0 < e
  e_hi : e ≤ 0.3
  rpm_lo : 2300 ≤ s.rpm

-- unfolding `evaluate` over ℝ and generalizing its subterms exceeds the default budget
set_option maxHeartbeats 1000000 in
theorem au_lower (s : StateOf ℝ) (e : ℝ) (R : AuRegion s e) : 0.6 ≤ (evalR ⟨e, 1, 0, 0⟩ s).1.au := by
  obtain ⟨hh0, hh1, hvx0, hvx1, hvz0, hvz1, hn0, hn1, hdz, hu0, ha0, ha1, hq0, hq1, had, hst, he0, he1, hr0⟩ := R
  -- facts about the region, before the model is unfolded
  have hdx1 : s.dx ≤ 1.01 := by nlinarith [sq_nonneg s.dz]
  have hdx0 : -1.01 ≤ s.dx := by nlinarith [sq_nonneg s.dz]
  have hdz1 : s.dz ≤ 1.01 := by nlinarith [sq_nonneg s.dx]
  have hb : (72090 / 65536 : ℝ) ≤ (s.h + -(1803 / 65536 * s.dz) + 36057 / 65536 * s.dx) / (357559 / 32768) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hel : (if e ≤ 0 then max (-1) (min 1 (-e)) * 23 * 1745 else max (-1) (min 1 (-e)) * 28 * 1745 : ℝ) =
      -e * 28 * 1745 := by
    rw [if_neg (by linarith : ¬ _), min_eq_right (by linarith), max_eq_right (by linarith)]
  have hρ0 : 71083 / 65536 ≤ atmR atmRho s.h := rho_lower hh0 hh1
  generalize hu : s.vx * s.dx + s.vz * s.dz = u at *
  generalize hw : s.vx * s.dz - s.vz * s.dx = w at *
  have hMid : u * u + w * w = (s.dx * s.dx + s.dz * s.dz) * (s.vx * s.vx + s.vz * s.vz) := by
    rw [← hu, ← hw]; ring
  generalize hM : u * u + w * w = M at *
  have hM0 : 1366 ≤ M := by rw [hMid]; nlinarith
  have hM1 : M ≤ 2116 := by rw [hMid]; nlinarith
  have hvt0 : 36.9 ≤ √M := by
    rw [show (36.9 : ℝ) = √(36.9 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_le_sqrt (by linarith)
  have hvt1 : √M ≤ 46 := by
    rw [show (46 : ℝ) = √(46 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_le_sqrt (by linarith)
  have hvt2 : √M * √M = M := Real.mul_self_sqrt (by linarith)
  have hw0 : 0 ≤ w := by nlinarith
  have hal := atan2R_bounds hu0 hw0
  rw [hM] at hal
  have hα0 : 0.1 ≤ atan2R w u := le_trans (by rw [le_div_iff₀ (by linarith)]; linarith) hal.1
  have hα1 : atan2R w u ≤ 0.2 := le_trans hal.2 (by rw [div_le_iff₀ hu0]; linarith)
  have hstall : (if (23593 / 65536 : ℝ) < atan2R w u then (1 : ℝ)
      else if atan2R w u < 2949 / 32768 then 0 else s.stall) = 0 := by
    rw [if_neg (by linarith : ¬ _)]; split_ifs <;> simp [hst]
  have hCL := CL_lower hα0 hα1
  have hCD := CD_bounds hα0 hα1
  simp only [evalR, evaluate, i_add, i_sub, i_mul, i_div, i_neg, i_max, i_min, i_ofNat, i_selLt, i_selLe, i_sqrt,
    i_atan2, i_shr, i_abs, i_lit, i_atm, i_tbl1, i_tbl2, cosSmall, sinSmall, ifZero2, liftForce, dragForce,
    f_CLwbh, f_CLDf, f_CLDe, f_CLadot, f_CLq, f_CDo, f_CDDf, f_CDwbh, f_CDDe, f_CDbeta, fn_kCLge, fn_kCDge,
    massT, wingChord, elevTravelUp, elevTravelDown, gravity0, gravScaleHKm, earthRadiusKm, omegaInv2, omega2R0,
    propD4, propDiameter, thrusterBodyZ, rpBodyX, rpBodyZ, wingSpan, alphaHystHi, alphaHystLo]
  norm_num
  rw [hu, hw, hM, hstall, kCLge_hi hb, kCDge_hi hb, flapCL_zero, flapCD_zero, hel]
  generalize atmR atmRho s.h = ρ at *
  generalize tbl2R tbl_x_5 (atan2R w u) 0 = CL at *
  generalize tbl2R tbl_x_4 (atan2R w u) 0 = CD at *
  have hu1 : u ≤ √M := Real.le_sqrt_of_sq_le (by have := mul_self_nonneg w; rw [← hM, sq]; linarith)
  have hadv : (if (655 / 65536 : ℝ) < s.rpm / 60 then (u + s.q * (18543 / 65536)) / (62423 / 32768 * (s.rpm / 60))
      else (u + s.q * (18543 / 65536)) / (62423 / 32768)) ≤ 72090 / 65536 := by
    rw [if_pos (by linarith), div_le_iff₀ (by positivity)]; linarith
  have hct := CT_pos hadv
  have hvt0' : (0 : ℝ) < √M := by linarith only [hvt0]
  have hρp : 0 ≤ ρ := by linarith only [hρ0]
  have hM0' : 0 ≤ M := by linarith only [hM0]
  have hQ0 : 0 ≤ ρ * M / 2000 := by positivity
  have hci : 0 ≤ 97879 / 65536 / (√M + √M) := by positivity
  have hci1 : 97879 / 65536 / (√M + √M) ≤ 97879 / 65536 / 73.8 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hvt0])
  have hA : -(ρ * M / 2000 * 0.1669) ≤ (if (33 / 32768 : ℝ) < M then
      112561 / 4096 * (ρ * M / 2000) * ((u * s.wdot - w * s.udot) / M) * (97879 / 65536 / (√M + √M)) else 0) := by
    split_ifs
    · have h1 : |(u * s.wdot - w * s.udot) / M| ≤ 0.3 := by
        rw [abs_div, abs_of_pos (by linarith only [hM0] : (0:ℝ) < M), div_le_iff₀ (by linarith only [hM0])]; exact had
      have h5 : 0 ≤ (u * s.wdot - w * s.udot) / M + 0.3 := by linarith only [h1, neg_abs_le ((u * s.wdot - w * s.udot) / M)]
      have h7 := mul_nonneg (mul_nonneg hQ0 hci) h5
      rw [mul_add] at h7
      have h8 := mul_le_mul_of_nonneg_left hci1 hQ0
      rw [show 112561 / 4096 * (ρ * M / 2000) * ((u * s.wdot - w * s.udot) / M) * (97879 / 65536 / (√M + √M)) =
        112561 / 4096 * (ρ * M / 2000 * (97879 / 65536 / (√M + √M)) * ((u * s.wdot - w * s.udot) / M)) by ring]
      linarith only [h7, h8, hQ0]
    · linarith only [hQ0]
  have hel0 : -e * 28 * 1745 / 100000 < 0 := by linarith only [he0]
  have hCLQ : ρ * M / 2000 * (54394 / 65536) ≤ ρ * M / 2000 * CL :=
    mul_le_mul_of_nonneg_left (by linarith only [hCL]) hQ0
  have heQ : ρ * M / 2000 * e ≤ ρ * M / 2000 * 0.3 := mul_le_mul_of_nonneg_left he1 hQ0
  have hCDQ : ρ * M / 2000 * CD ≤ ρ * M / 2000 * (8100 / 65536) := mul_le_mul_of_nonneg_left hCD.2 hQ0
  have hCDQ0 : 0 ≤ ρ * M / 2000 * CD := mul_nonneg hQ0 hCD.1
  have heQ0 : 0 ≤ ρ * M / 2000 * e := mul_nonneg hQ0 he0.le
  rw [rot_shape s.dx s.dz s.vx s.vz u w (√M) (27943 / 32768) _ _ _ (s.dx * s.dx + s.dz * s.dz) hvt0'.ne'
    (by norm_num) (by rw [← hu, ← hw]; ring) (by rw [← hu, ← hw]; ring)]
  refine au_core s.dz s.vx s.vz s.h ρ M (√M) _ _ _ _ hvx0 hvz1 (by linarith only [hh0]) hρ0 hvt0 hvt2 hn0 hdz ?_ ?_ ?_ ?_
  · -- lift: CL ≥ 0.83, elevator ≥ -0.147, alpha-rate term ≥ -0.167, pitch-rate term ≥ 0
    have hq : 0 ≤ 1032913 / 16384 * (ρ * M / 2000) * s.q * (97879 / 65536 / (√M + √M)) := by positivity
    generalize (if (33 / 32768 : ℝ) < M then
      112561 / 4096 * (ρ * M / 2000) * ((u * s.wdot - w * s.udot) / M) * (97879 / 65536 / (√M + √M)) else 0) = A at *
    generalize 1032913 / 16384 * (ρ * M / 2000) * s.q * (97879 / 65536 / (√M + √M)) = P at *
    generalize ρ * M / 2000 = Q at *
    rw [show 529699 / 32768 * Q * CL * 1 + 529699 / 32768 * Q * 1 * 0 + 455541 / 65536 * Q * (-e * 28 * 1745 / 100000)
      + A + P = 529699 / 32768 * (Q * CL) - 455541 / 65536 * 28 * 1745 / 100000 * (Q * e) + A + P by ring]
    linarith only [hq, hA, hCLQ, heQ, hQ0]
  · rw [abs_of_neg hel0]; linarith only [hCDQ0, heQ0, hQ0]
  · rw [abs_of_neg hel0]; linarith only [hCDQ, heQ, hQ0]
  · have := CTMach_pos (√(s.rpm / 60 * (62423 / 32768) * (205887 / 65536) / atmR atmA s.h *
        (s.rpm / 60 * (62423 / 32768) * (205887 / 65536) / atmR atmA s.h) +
        (u + s.q * (18543 / 65536)) / atmR atmA s.h * ((u + s.q * (18543 / 65536)) / atmR atmA s.h)))
    have hr : 0 ≤ s.rpm / 60 := by linarith only [hr0]
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hct this) (by norm_num)) hρp) hr) hr

end Jsb.Cont
