import Proofs.TermSound.Long

/-! The 30° climbing turn. -/

namespace Proofs.TermSound

open Complex

noncomputable section

def ZCAPH : ℝ := 4100
def ZT : ℝ := 1200
def RL : ℝ := 1 / 200
def kappa : ℝ := 1 / 3

def Rstar (z : ℝ) : ℝ := uStar EH z ^ 2 / (g * lc)

/-- The turn centre the trim radius at the current altitude would give. -/
def centre (s : St) : ℂ := pos s + (Rstar s.z : ℂ) * I * cis s.psi

/-- Entered at altitude `z0` with centre `c0` and slack `m0`; terrain matters only below `ztop`. -/
def DynH (c0 : ℂ) (z0 m0 ztop : ℝ) (s : St) : Prop :=
  q PL (eu EH s) (evz EH s) ≤ r2L ∧ z0 ≤ s.z ∧ s.z ≤ ZCAPH ∧
    (s.z < ztop → |s.l - lc| ≤ RL ∧ ‖centre s - c0‖ ≤ m0 + kappa * (s.z - z0))

theorem norm_cis (a : ℝ) : ‖cis a‖ = 1 := by
  simp [cis]

theorem norm_cis_sub (a b : ℝ) : ‖cis a - cis b‖ ≤ |a - b| := by
  have e : cis a - cis b = cis b * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    simp only [cis, mul_sub, mul_one, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [e, norm_mul, norm_cis, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem norm_real_I_cis (r a : ℝ) : ‖(r : ℂ) * I * cis a‖ = |r| := by
  rw [norm_mul, norm_mul, norm_I, norm_cis, Complex.norm_real, Real.norm_eq_abs]; ring

theorem norm_real_I_mul (r : ℝ) (w : ℂ) : ‖(r : ℂ) * I * w‖ = |r| * ‖w‖ := by
  rw [norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs]; ring

theorem pos_step (s d : St) :
    pos (stepHelix s + d) = pos s + (radius s : ℂ) * I * (cis s.psi - cis (s.psi + h * omega s))
      + ⟨d.x, d.y⟩ := by
  apply Complex.ext <;> simp [pos, stepHelix]

theorem centre_step (s d : St) :
    centre (stepHelix s + d) - centre s =
      ((radius s - Rstar s.z : ℝ) : ℂ) * I * (cis s.psi - cis (s.psi + h * omega s))
      + (Rstar (stepHelix s + d).z : ℂ) * I * (cis (s.psi + h * omega s + d.psi) - cis (s.psi + h * omega s))
      + ((Rstar (stepHelix s + d).z - Rstar s.z : ℝ) : ℂ) * I * cis (s.psi + h * omega s)
      + ⟨d.x, d.y⟩ := by
  have hp := pos_step s d
  have hpsi : (stepHelix s + d).psi = s.psi + h * omega s + d.psi := by simp [stepHelix]
  simp only [centre, hp, hpsi]
  push_cast; ring

theorem centre_drift (s d : St) :
    ‖centre (stepHelix s + d) - centre s‖ ≤
      |radius s - Rstar s.z| * |h * omega s| + |Rstar (stepHelix s + d).z| * |d.psi|
      + |Rstar (stepHelix s + d).z - Rstar s.z| + (|d.x| + |d.y|) := by
  rw [centre_step]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · rw [norm_real_I_mul]
    have := norm_cis_sub s.psi (s.psi + h * omega s)
    rw [show s.psi - (s.psi + h * omega s) = -(h * omega s) by ring, abs_neg] at this
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · rw [norm_real_I_mul]
    have := norm_cis_sub (s.psi + h * omega s + d.psi) (s.psi + h * omega s)
    rw [show s.psi + h * omega s + d.psi - (s.psi + h * omega s) = d.psi by ring] at this
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · rw [norm_real_I_cis]
  · exact Complex.norm_le_abs_re_add_abs_im _

theorem stepHelix_fields (s d : St) :
    (stepHelix s + d).z = s.z + h * s.vz + d.z ∧ (stepHelix s + d).u = s.u + h * accU EH s + d.u ∧
    (stepHelix s + d).vz = s.vz + h * accVz s + d.vz ∧ (stepHelix s + d).l = s.l + h / tau * (lc - s.l) + d.l ∧
    (stepHelix s + d).psi = s.psi + h * omega s + d.psi := by
  simp [stepHelix]

def DZMIN : ℝ := h * (vzStar EH ZT - EVZ) - dZ

theorem vz_band {E0 : ℝ} {s : St} (hQ : q PL (eu E0 s) (evz E0 s) ≤ r2L) :
    vzStar E0 s.z - EVZ ≤ s.vz ∧ s.vz ≤ vzStar E0 s.z + EVZ := by
  have := (long_extent hQ).2
  rw [abs_le] at this; unfold evz at this; constructor <;> linarith [this.1, this.2]

theorem u_band {E0 : ℝ} {s : St} (hQ : q PL (eu E0 s) (evz E0 s) ≤ r2L) :
    uStar E0 s.z - EU ≤ s.u ∧ s.u ≤ uStar E0 s.z + EU := by
  have := (long_extent hQ).1
  rw [abs_le] at this; unfold eu at this; constructor <;> linarith [this.1, this.2]

theorem dz_H {s : St} {dz : ℝ} (hQ : q PL (eu EH s) (evz EH s) ≤ r2L) (h0 : 0 ≤ s.z) (h1 : s.z ≤ ZCAPH)
    (hdz : |dz| ≤ dZ) : |h * s.vz + dz| ≤ DZ := by
  have hv := vz_band hQ
  rw [abs_le] at hdz ⊢
  simp only [vzStar, EH, E1, kV, v0, EVZ, ZCAPH, h, dZ, DZ] at *
  constructor <;> nlinarith [hv.1, hv.2, hdz.1, hdz.2]

theorem climb_H {s : St} {dz : ℝ} (hQ : q PL (eu EH s) (evz EH s) ≤ r2L) (h1 : s.z ≤ ZT)
    (hdz : |dz| ≤ dZ) : DZMIN ≤ h * s.vz + dz := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [DZMIN, vzStar, EH, E1, kV, v0, EVZ, ZT, h, dZ] at *
  nlinarith [hv.1, hdz.1]

theorem DZMIN_pos : 0 < DZMIN := by norm_num [DZMIN, vzStar, EH, E1, kV, v0, EVZ, ZT, h, dZ]

theorem cap_H {s : St} {dz : ℝ} (hQ : q PL (eu EH s) (evz EH s) ≤ r2L) (h1 : s.z ≤ ZCAPH)
    (hdz : |dz| ≤ dZ) : s.z + h * s.vz + dz ≤ ZCAPH := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [vzStar, EH, E1, kV, v0, EVZ, ZCAPH, h, dZ] at *
  nlinarith [hv.2, hdz.2]

theorem stay_H {s : St} {dz ztop : ℝ} (hQ : q PL (eu EH s) (evz EH s) ≤ r2L) (hzt : ztop ≤ ZT)
    (hz : ztop ≤ s.z) (hdz : |dz| ≤ dZ) : ztop ≤ s.z + h * s.vz + dz := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [vzStar, EH, E1, kV, v0, EVZ, ZT, h, dZ] at *
  rcases le_or_gt s.z 1200 with hz' | hz'
  · nlinarith [hv.1, hdz.1]
  · nlinarith [hv.1, hdz.1]

def DRAD : ℝ := 16 / 5
def OMAX : ℝ := 181 / 1000
def RMAX : ℝ := 201
def LR : ℝ := 21 / 1000

theorem uStar_H_band {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ ZT + 1) : 314 / 10 - 1 / 500 ≤ uStar EH z ∧ uStar EH z ≤ 67 / 2 := by
  simp only [uStar, EH, E1, ur, ZT] at *; constructor <;> nlinarith

theorem radius_err {s : St} (hu : |s.u - uStar EH s.z| ≤ EU) (hl : |s.l - lc| ≤ RL) (h0 : 0 ≤ s.z)
    (h1 : s.z ≤ ZT) : |radius s - Rstar s.z| ≤ DRAD := by
  obtain ⟨hs0, hs1⟩ := uStar_H_band h0 (by linarith)
  set us := uStar EH s.z
  have hlpos : 0 < s.l := by
    rw [abs_le] at hl; simp only [lc, RL] at hl; linarith [hl.1]
  have hl0 : (0 : ℝ) < lc := by norm_num [lc]
  have hg : (0 : ℝ) < g := by norm_num [g]
  have e : radius s - Rstar s.z = (lc * (s.u - us) * (s.u + us) - us ^ 2 * (s.l - lc)) / (g * s.l * lc) := by
    simp only [radius, Rstar, us]; field_simp; ring
  have hdpos : 0 < g * s.l * lc := mul_pos (mul_pos hg hlpos) hl0
  rw [e, abs_div, abs_of_pos hdpos]
  have hu' := abs_le.mp hu
  simp only [EU] at hu'
  have hupos : 0 ≤ s.u + us := by linarith [hu'.1]
  have hsum : s.u + us ≤ 67 + EU := by simp only [EU]; linarith [hu'.2]
  have hnum : |lc * (s.u - us) * (s.u + us) - us ^ 2 * (s.l - lc)| ≤ lc * EU * (67 + EU) + (67 / 2) ^ 2 * RL := by
    have t1 : |s.u - us| * (s.u + us) ≤ EU * (67 + EU) :=
      mul_le_mul hu hsum hupos (by norm_num [EU])
    have t2 : us ^ 2 * |s.l - lc| ≤ (67 / 2) ^ 2 * RL :=
      mul_le_mul (by nlinarith) hl (abs_nonneg _) (by positivity)
    calc _ ≤ |lc * (s.u - us) * (s.u + us)| + |us ^ 2 * (s.l - lc)| := abs_sub _ _
      _ = lc * (|s.u - us| * (s.u + us)) + us ^ 2 * |s.l - lc| := by
          simp only [abs_mul, abs_of_pos hl0, abs_of_nonneg hupos, abs_pow, sq_abs]; ring
      _ ≤ lc * (EU * (67 + EU)) + (67 / 2) ^ 2 * RL := by
          have := mul_le_mul_of_nonneg_left t1 hl0.le; linarith
      _ = _ := by ring
  have hden : g * (lc - RL) * lc ≤ g * s.l * lc := by
    rw [abs_le] at hl; gcongr; linarith [hl.1]
  have hden0 : 0 < g * (lc - RL) * lc := by norm_num [g, lc, RL]
  calc _ ≤ (lc * EU * (67 + EU) + (67 / 2) ^ 2 * RL) / (g * (lc - RL) * lc) := by
        apply div_le_div₀ (by norm_num [lc, EU, RL]) hnum hden0 hden
    _ ≤ DRAD := by norm_num [lc, EU, RL, g, DRAD]

theorem omega_band {s : St} (hu : |s.u - uStar EH s.z| ≤ EU) (hl : |s.l - lc| ≤ RL) (h0 : 0 ≤ s.z)
    (h1 : s.z ≤ ZT) : |h * omega s| ≤ h * OMAX := by
  obtain ⟨hs0, hs1⟩ := uStar_H_band h0 (by linarith)
  rw [abs_le] at hu hl
  have hu0 : 31 ≤ s.u := by simp only [EU] at hu; linarith [hu.1]
  have hl0 : 0 ≤ s.l := by simp only [lc, RL] at hl; linarith [hl.1]
  have hom0 : 0 ≤ omega s := div_nonneg (mul_nonneg (by norm_num [g]) hl0) (by linarith)
  have hom : omega s ≤ OMAX := by
    unfold omega; rw [div_le_iff₀ (by linarith)]
    simp only [g, OMAX, lc, RL, EU] at *; nlinarith [hl.2, hu.1]
  rw [abs_of_nonneg (by unfold h; positivity)]; unfold h at *; gcongr

theorem Rstar_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ ZT + 1) : |Rstar z| ≤ RMAX := by
  obtain ⟨hs0, hs1⟩ := uStar_H_band h0 h1
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num [g, lc]))]
  unfold Rstar; rw [div_le_iff₀ (by norm_num [g, lc])]
  have : uStar EH z ^ 2 ≤ (67 / 2) ^ 2 := by nlinarith
  norm_num [g, lc, RMAX] at *; linarith

theorem Rstar_lip {z z' : ℝ} (h0 : 0 ≤ z) (hzz : z ≤ z') (h1 : z' ≤ ZT + 1) :
    |Rstar z' - Rstar z| ≤ LR * (z' - z) := by
  obtain ⟨a0, a1⟩ := uStar_H_band h0 (by linarith)
  obtain ⟨b0, b1⟩ := uStar_H_band (h0.trans hzz) h1
  have e : Rstar z' - Rstar z = -(E1 * (z' - z) * (uStar EH z' + uStar EH z)) / (g * lc) := by
    simp only [Rstar, uStar]; field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos (by norm_num [g, lc] : (0 : ℝ) < g * lc),
    abs_of_nonneg (by have : (0 : ℝ) ≤ E1 := by norm_num [E1]
                      have : 0 ≤ z' - z := by linarith
                      positivity), div_le_iff₀ (by norm_num [g, lc])]
  have : 0 ≤ z' - z := by linarith
  have : E1 * (z' - z) * (uStar EH z' + uStar EH z) ≤ E1 * (z' - z) * 67 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by norm_num [E1]; linarith)
  norm_num [E1, LR, g, lc] at *; nlinarith

theorem drift_budget : DRAD * (h * OMAX) + RMAX * dPSI + 2 * dP ≤ (kappa - LR) * DZMIN := by
  norm_num [DRAD, h, OMAX, RMAX, dPSI, dP, kappa, LR, DZMIN, vzStar, EH, E1, kV, v0, EVZ, ZT, dZ]

theorem bank_step {s d : St} (hl : |s.l - lc| ≤ RL) (hd : |d.l| ≤ dL) :
    |s.l + h / tau * (lc - s.l) + d.l - lc| ≤ RL := by
  have e : s.l + h / tau * (lc - s.l) + d.l - lc = (1 - h / tau) * (s.l - lc) + d.l := by ring
  rw [e]
  calc _ ≤ |(1 - h / tau) * (s.l - lc)| + |d.l| := abs_add_le _ _
    _ = (1 - h / tau) * |s.l - lc| + |d.l| := by rw [abs_mul, abs_of_pos (by norm_num [h, tau])]
    _ ≤ (1 - h / tau) * RL + dL := by gcongr; norm_num [h, tau]
    _ ≤ RL := by norm_num [h, tau, RL, dL]

/-- **Robust invariance of the helix end set** under every per-frame disturbance within the budget. -/
theorem dynH_robust {c0 : ℂ} {z0 m0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT) {s d : St}
    (hs : DynH c0 z0 m0 ztop s) (hd : Small d) : DynH c0 z0 m0 ztop (stepHelix s + d) := by
  obtain ⟨hQ, hz0s, hcap, hcone⟩ := hs
  obtain ⟨hdx, hdy, hdz, hdpsi, hdu, hdvz, hdl⟩ := hd
  obtain ⟨fz, fu, fvz, fl, fpsi⟩ := stepHelix_fields s d
  have hz0' : 0 ≤ s.z := hz0.trans hz0s
  have hDZ := dz_H hQ hz0' hcap hdz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show eu EH (stepHelix s + d) = _ from congrArg₂ (· - uStar EH ·) fu fz,
      show evz EH (stepHelix s + d) = _ from congrArg₂ (· - vzStar EH ·) fvz fz]
    exact long_step EH s hQ hDZ hdu hdvz
  · rw [fz]
    rcases lt_or_ge s.z ztop with hlt | hge
    · have := climb_H hQ (hlt.le.trans hzt) hdz; linarith [DZMIN_pos]
    · have := stay_H hQ hzt hge hdz
      by_contra hc; push Not at hc
      have : ztop < z0 := by linarith
      linarith
  · rw [fz]; exact cap_H hQ hcap hdz
  · intro hlt'
    rw [fz] at hlt'
    have hlt : s.z < ztop := by
      by_contra hge; push Not at hge; have := stay_H hQ hzt hge hdz; linarith
    obtain ⟨hl, hc⟩ := hcone hlt
    have hzT : s.z ≤ ZT := hlt.le.trans hzt
    have hclimb := climb_H hQ hzT hdz
    have hu := (long_extent hQ).1
    refine ⟨by rw [fl]; exact bank_step hl hdl, ?_⟩
    have hdr := radius_err hu hl hz0' hzT
    have hom := omega_band hu hl hz0' hzT
    have hzz : s.z ≤ (stepHelix s + d).z := by rw [fz]; linarith [DZMIN_pos]
    have hz1 : (stepHelix s + d).z ≤ ZT + 1 := by
      rw [fz]; have := (abs_le.mp hDZ).2; linarith
    have hR := Rstar_le (hz0'.trans hzz) hz1
    have hlip := Rstar_lip hz0' hzz hz1
    have hdrift := centre_drift s d
    have hstep : ‖centre (stepHelix s + d) - centre s‖ ≤
        DRAD * (h * OMAX) + RMAX * dPSI + LR * ((stepHelix s + d).z - s.z) + (dP + dP) := by
      refine hdrift.trans ?_
      gcongr
      all_goals norm_num [DRAD, RMAX]
    have hΔ : DZMIN ≤ (stepHelix s + d).z - s.z := by rw [fz]; linarith
    have hb := drift_budget
    have hk : 0 ≤ kappa - LR := by norm_num [kappa, LR]
    calc ‖centre (stepHelix s + d) - c0‖
        ≤ ‖centre s - c0‖ + ‖centre (stepHelix s + d) - centre s‖ := by
          have := norm_add_le (centre s - c0) (centre (stepHelix s + d) - centre s)
          rwa [show centre s - c0 + (centre (stepHelix s + d) - centre s) = centre (stepHelix s + d) - c0
            by ring] at this
      _ ≤ m0 + kappa * (s.z - z0) + (DRAD * (h * OMAX) + RMAX * dPSI + LR * ((stepHelix s + d).z - s.z)
            + (dP + dP)) := add_le_add hc hstep
      _ ≤ m0 + kappa * ((stepHelix s + d).z - z0) := by
          have := mul_le_mul_of_nonneg_left hΔ hk
          nlinarith

end

end Proofs.TermSound
