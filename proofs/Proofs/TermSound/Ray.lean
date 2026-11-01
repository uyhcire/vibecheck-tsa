import Proofs.TermSound.Helix

namespace Proofs.TermSound

noncomputable section

def ZCAPR : ℝ := 4600
def PT : Form := ⟨5, 7 / 4, 1⟩
def thN : ℝ := 3 / 10
def AT : Mat := ⟨1, h * thN, -(h * kChi / tau), 1 - h / tau⟩
def r2T : ℝ := 1 / 625
def c2T : ℝ := 9944 / 10000
def tT : ℝ := 28 / 10000
def ECH : ℝ := 3 / 100
def EL : ℝ := 13 / 200
def MISG : ℝ := 17 / 1000
def wPSI : ℝ := dPSI + h * EL * MISG
def KT : ℝ := 5 * wPSI ^ 2 + 2 * (7 / 4) * wPSI * dL + dL ^ 2
def kapY : ℝ := 1 / 30
def G : ℝ := 2 / 25

def DynR (x0 z0 w0 ztop : ℝ) (s : St) : Prop :=
  q PL (eu ER s) (evz ER s) ≤ r2L ∧ z0 ≤ s.z ∧ s.z ≤ ZCAPR ∧
    (s.z < ztop → q PT s.psi s.l ≤ r2T ∧ x0 ≤ s.x ∧ |s.y| ≤ w0 + kapY * (s.x - x0) ∧
      z0 + G * (s.x - x0) ≤ s.z)

theorem stepRay_fields (s d : St) :
    (stepRay s + d).z = s.z + h * s.vz + d.z ∧ (stepRay s + d).u = s.u + h * accU ER s + d.u ∧
    (stepRay s + d).vz = s.vz + h * accVz s + d.vz ∧
    (stepRay s + d).l = s.l + h / tau * (-kChi * s.psi - s.l) + d.l ∧
    (stepRay s + d).psi = s.psi + h * (g * s.l / s.u) + d.psi ∧
    (stepRay s + d).x = s.x + h * s.u * Real.cos s.psi + d.x ∧
    (stepRay s + d).y = s.y + h * s.u * Real.sin s.psi + d.y := by
  simp [stepRay]

def DZMINR : ℝ := h * (vzStar ER ZT - EVZ) - dZ

theorem dz_R {s : St} {dz : ℝ} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h0 : 0 ≤ s.z) (h1 : s.z ≤ ZCAPR)
    (hdz : |dz| ≤ dZ) : |h * s.vz + dz| ≤ DZ := by
  have hv := vz_band hQ
  rw [abs_le] at hdz ⊢
  simp only [vzStar, ER, E1, kV, v0, EVZ, ZCAPR, h, dZ, DZ] at *
  constructor <;> nlinarith [hv.1, hv.2, hdz.1, hdz.2]

theorem climb_R {s : St} {dz : ℝ} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h1 : s.z ≤ ZT)
    (hdz : |dz| ≤ dZ) : DZMINR ≤ h * s.vz + dz := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [DZMINR, vzStar, ER, E1, kV, v0, EVZ, ZT, h, dZ] at *
  nlinarith [hv.1, hdz.1]

theorem DZMINR_pos : 0 < DZMINR := by norm_num [DZMINR, vzStar, ER, E1, kV, v0, EVZ, ZT, h, dZ]

theorem cap_R {s : St} {dz : ℝ} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h1 : s.z ≤ ZCAPR)
    (hdz : |dz| ≤ dZ) : s.z + h * s.vz + dz ≤ ZCAPR := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [vzStar, ER, E1, kV, v0, EVZ, ZCAPR, h, dZ] at *
  nlinarith [hv.2, hdz.2]

theorem stay_R {s : St} {dz ztop : ℝ} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (hzt : ztop ≤ ZT)
    (hz : ztop ≤ s.z) (hdz : |dz| ≤ dZ) : ztop ≤ s.z + h * s.vz + dz := by
  have hv := vz_band hQ
  rw [abs_le] at hdz
  simp only [vzStar, ER, E1, kV, v0, EVZ, ZT, h, dZ] at *
  nlinarith [hv.1, hdz.1]

theorem PT_pd : PT.PD := by norm_num [Form.PD, PT]

theorem AT_psd : 0 < m11 PT AT c2T ∧ m12 PT AT c2T ^ 2 ≤ m11 PT AT c2T * m22 PT AT c2T := by
  norm_num [m11, m12, m22, PT, AT, c2T, h, thN, kChi, tau]

theorem T_budget : (1 + tT) * c2T * r2T + (1 + 1 / tT) * KT ≤ r2T := by
  norm_num [tT, c2T, r2T, KT, wPSI, dPSI, h, EL, MISG, dL]

theorem lat_extent {a b : ℝ} (hQ : q PT a b ≤ r2T) : |a| ≤ ECH ∧ |b| ≤ EL := by
  have hx := q_extent_x (P := PT) a b
  have hy := q_extent_y (P := PT) a b
  simp only [PT] at hx hy
  constructor
  · apply abs_le_of_sq (by norm_num [ECH]); simp only [PT] at hQ; norm_num [ECH, r2T] at *; nlinarith
  · apply abs_le_of_sq (by norm_num [EL]); simp only [PT] at hQ; norm_num [EL, r2T] at *; nlinarith

theorem uStar_R_band {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ ZT) : 324 / 10 ≤ uStar ER z ∧ uStar ER z ≤ 69 / 2 := by
  simp only [uStar, ER, E1, ur, ZT] at *; constructor <;> nlinarith

theorem turn_mismatch {s : St} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h0 : 0 ≤ s.z) (h1 : s.z ≤ ZT)
    (hl : |s.l| ≤ EL) : |h * s.l * (g / s.u - thN)| ≤ h * EL * MISG := by
  obtain ⟨a, b⟩ := uStar_R_band h0 h1
  obtain ⟨c, d⟩ := u_band hQ
  have hu0 : 32 < s.u := by simp only [EU] at c; linarith
  have hm : |g / s.u - thN| ≤ MISG := by
    rw [abs_le]; constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
      simp only [g, thN, MISG, EU] at *; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
      simp only [g, thN, MISG, EU] at *; nlinarith
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num [h] : (0 : ℝ) < h)]
  have : |s.l| * |g / s.u - thN| ≤ EL * MISG := mul_le_mul hl hm (abs_nonneg _) (by norm_num [EL])
  have hh : (0 : ℝ) < h := by norm_num [h]
  nlinarith

theorem lat_step {s d : St} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h0 : 0 ≤ s.z) (h1 : s.z ≤ ZT)
    (hT : q PT s.psi s.l ≤ r2T) (hdpsi : |d.psi| ≤ dPSI) (hdl : |d.l| ≤ dL) :
    q PT (s.psi + h * (g * s.l / s.u) + d.psi) (s.l + h / tau * (-kChi * s.psi - s.l) + d.l) ≤ r2T := by
  have e1 : s.psi + h * (g * s.l / s.u) + d.psi = AT.a11 * s.psi + AT.a12 * s.l + (h * s.l * (g / s.u - thN) + d.psi) := by
    simp only [AT]; ring
  have e2 : s.l + h / tau * (-kChi * s.psi - s.l) + d.l = AT.a21 * s.psi + AT.a22 * s.l + d.l := by
    simp only [AT]; ring
  rw [e1, e2]
  have hm := turn_mismatch hQ h0 h1 (lat_extent hT).2
  have hw1 : |h * s.l * (g / s.u - thN) + d.psi| ≤ wPSI := by
    calc _ ≤ |h * s.l * (g / s.u - thN)| + |d.psi| := abs_add_le _ _
      _ ≤ h * EL * MISG + dPSI := add_le_add hm hdpsi
      _ = wPSI := by unfold wPSI; ring
  have hw : q PT (h * s.l * (g / s.u - thN) + d.psi) d.l ≤ KT := by
    have := q_le_box (P := PT) (by norm_num [PT]) (by norm_num [PT]) hw1 hdl
    simpa [PT, KT, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using this
  exact q_robust_step PT_pd (by norm_num [c2T]) AT_psd.1 AT_psd.2 (by norm_num [tT]) T_budget hT hw

def DXMIN : ℝ := h * (324 / 10 - EU) * (1 - ECH ^ 2 / 2) - dP
def DXMAX : ℝ := h * (69 / 2 + EU) + dP
def DYMAX : ℝ := h * (69 / 2 + EU) * ECH + dP

theorem track_step {s d : St} (hQ : q PL (eu ER s) (evz ER s) ≤ r2L) (h0 : 0 ≤ s.z) (h1 : s.z ≤ ZT)
    (hpsi : |s.psi| ≤ ECH) (hdx : |d.x| ≤ dP) (hdy : |d.y| ≤ dP) :
    DXMIN ≤ h * s.u * Real.cos s.psi + d.x ∧ h * s.u * Real.cos s.psi + d.x ≤ DXMAX ∧
      |h * s.u * Real.sin s.psi + d.y| ≤ DYMAX := by
  obtain ⟨a, b⟩ := uStar_R_band h0 h1
  obtain ⟨c, d'⟩ := u_band hQ
  have hu0 : 324 / 10 - EU ≤ s.u := by linarith
  have hu1 : s.u ≤ 69 / 2 + EU := by linarith
  have hupos : 0 ≤ s.u := by simp only [EU] at hu0; linarith
  have hh : (0 : ℝ) < h := by norm_num [h]
  have hcos1 := Real.cos_le_one s.psi
  have hcos0 : 1 - ECH ^ 2 / 2 ≤ Real.cos s.psi := by
    have := Real.one_sub_sq_div_two_le_cos (x := s.psi)
    have : s.psi ^ 2 ≤ ECH ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpsi 2
    linarith
  have hsin : |Real.sin s.psi| ≤ ECH := Real.abs_sin_le_abs.trans hpsi
  rw [abs_le] at hdx
  have hc0 : 0 ≤ 1 - ECH ^ 2 / 2 := by norm_num [ECH]
  refine ⟨?_, ?_, ?_⟩
  · unfold DXMIN
    have : h * (324 / 10 - EU) * (1 - ECH ^ 2 / 2) ≤ h * s.u * Real.cos s.psi := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hu0 hh.le) hcos0 hc0 (by positivity)
    linarith [hdx.1]
  · unfold DXMAX
    have : h * s.u * Real.cos s.psi ≤ h * (69 / 2 + EU) := by
      have := mul_le_mul_of_nonneg_left hcos1 (by positivity : 0 ≤ h * s.u)
      have := mul_le_mul_of_nonneg_left hu1 hh.le
      nlinarith
    linarith [hdx.2]
  · unfold DYMAX
    calc _ ≤ |h * s.u * Real.sin s.psi| + |d.y| := abs_add_le _ _
      _ = h * s.u * |Real.sin s.psi| + |d.y| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h * s.u)]
      _ ≤ h * (69 / 2 + EU) * ECH + dP := by
          gcongr
          all_goals norm_num [h, EU, ECH]

theorem cone_budget : DYMAX ≤ kapY * DXMIN := by norm_num [DYMAX, DXMIN, kapY, h, EU, ECH, dP]

theorem gradient_budget : G * DXMAX ≤ DZMINR := by
  norm_num [G, DXMAX, DZMINR, h, EU, dP, vzStar, ER, E1, kV, v0, EVZ, ZT, dZ]

/-- **Robust invariance of the ray end set** under every per-frame disturbance within the budget. -/
theorem dynR_robust {x0 z0 w0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT) {s d : St}
    (hs : DynR x0 z0 w0 ztop s) (hd : Small d) : DynR x0 z0 w0 ztop (stepRay s + d) := by
  obtain ⟨hQ, hz0s, hcap, hcone⟩ := hs
  obtain ⟨hdx, hdy, hdz, hdpsi, hdu, hdvz, hdl⟩ := hd
  obtain ⟨fz, fu, fvz, fl, fpsi, fx, fy⟩ := stepRay_fields s d
  have hz0' : 0 ≤ s.z := hz0.trans hz0s
  have hDZ := dz_R hQ hz0' hcap hdz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show eu ER (stepRay s + d) = _ from congrArg₂ (· - uStar ER ·) fu fz,
      show evz ER (stepRay s + d) = _ from congrArg₂ (· - vzStar ER ·) fvz fz]
    exact long_step ER s hQ hDZ hdu hdvz
  · rw [fz]
    rcases lt_or_ge s.z ztop with hlt | hge
    · have := climb_R hQ (hlt.le.trans hzt) hdz; linarith [DZMINR_pos]
    · have := stay_R hQ hzt hge hdz; linarith
  · rw [fz]; exact cap_R hQ hcap hdz
  · intro hlt'
    rw [fz] at hlt'
    have hlt : s.z < ztop := by
      by_contra hge; push Not at hge; have := stay_R hQ hzt hge hdz; linarith
    obtain ⟨hT, hx0, hy, hgr⟩ := hcone hlt
    have hzT : s.z ≤ ZT := hlt.le.trans hzt
    have hclimb := climb_R hQ hzT hdz
    obtain ⟨tx0, tx1, ty⟩ := track_step hQ hz0' hzT (lat_extent hT).1 hdx hdy
    have hcb := cone_budget
    have hgb := gradient_budget
    refine ⟨by rw [fpsi, fl]; exact lat_step hQ hz0' hzT hT hdpsi hdl, ?_, ?_, ?_⟩
    · rw [fx]; have : 0 < DXMIN := by norm_num [DXMIN, h, EU, ECH, dP]
      linarith
    · rw [fx, fy]
      calc |s.y + h * s.u * Real.sin s.psi + d.y| ≤ |s.y| + |h * s.u * Real.sin s.psi + d.y| := by
            rw [add_assoc]; exact abs_add_le _ _
        _ ≤ w0 + kapY * (s.x - x0) + kapY * DXMIN := by linarith
        _ ≤ w0 + kapY * (s.x + h * s.u * Real.cos s.psi + d.x - x0) := by
            have := mul_le_mul_of_nonneg_left tx0 (by norm_num [kapY] : (0 : ℝ) ≤ kapY)
            nlinarith
    · rw [fx, fz]
      have := mul_le_mul_of_nonneg_left tx1 (by norm_num [G] : (0 : ℝ) ≤ G)
      have e : G * (s.x + h * s.u * Real.cos s.psi + d.x - x0)
          = G * (s.x - x0) + G * (h * s.u * Real.cos s.psi + d.x) := by ring
      rw [e]; linarith

end

end Proofs.TermSound
