import Proofs.TermSound.Ray

namespace Proofs.TermSound

open Complex

noncomputable section

/-- The frames of an escape under per-frame disturbances `d`. -/
def traj (step : St → St) (s0 : St) (d : ℕ → St) : ℕ → St
  | 0 => s0
  | n + 1 => step (traj step s0 d n) + d n

theorem forever {Dyn : St → Prop} {step : St → St} (hinv : ∀ s d, Dyn s → Small d → Dyn (step s + d))
    {s0 : St} {d : ℕ → St} (h0 : Dyn s0) (hd : ∀ n, Small (d n)) : ∀ n, Dyn (traj step s0 d n) := by
  intro n; induction n with
  | zero => exact h0
  | succ n ih => exact hinv _ _ ih (hd n)

theorem helix_forever {c0 : ℂ} {z0 m0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT)
    {s0 : St} {d : ℕ → St} (h0 : DynH c0 z0 m0 ztop s0) (hd : ∀ n, Small (d n)) :
    ∀ n, DynH c0 z0 m0 ztop (traj stepHelix s0 d n) :=
  forever (fun _ _ hs hd => dynH_robust hz0 hz0t hzt hs hd) h0 hd

theorem ray_forever {x0 z0 w0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT)
    {s0 : St} {d : ℕ → St} (h0 : DynR x0 z0 w0 ztop s0) (hd : ∀ n, Small (d n)) :
    ∀ n, DynR x0 z0 w0 ztop (traj stepRay s0 d n) :=
  forever (fun _ _ hs hd => dynR_robust hz0 hz0t hzt hs hd) h0 hd

/-- Once above `ztop`, never below it again. -/
theorem helix_stays_above {c0 : ℂ} {z0 m0 ztop : ℝ} (hzt : ztop ≤ ZT) {s d : St}
    (hs : DynH c0 z0 m0 ztop s) (hd : Small d) (hz : ztop ≤ s.z) : ztop ≤ (stepHelix s + d).z := by
  rw [(stepHelix_fields s d).1]; exact stay_H hs.1 hzt hz hd.2.2.1

theorem ray_stays_above {x0 z0 w0 ztop : ℝ} (hzt : ztop ≤ ZT) {s d : St}
    (hs : DynR x0 z0 w0 ztop s) (hd : Small d) (hz : ztop ≤ s.z) : ztop ≤ (stepRay s + d).z := by
  rw [(stepRay_fields s d).1]; exact stay_R hs.1 hzt hz hd.2.2.1

theorem Rstar_band {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ ZT) : 176 ≤ Rstar z ∧ Rstar z ≤ 401 / 2 := by
  obtain ⟨a, b⟩ := uStar_H_band h0 (by linarith)
  have a' : 314 / 10 ≤ uStar EH z := by simp only [uStar, EH, E1, ur, ZT] at *; nlinarith
  unfold Rstar
  constructor
  · rw [le_div_iff₀ (by norm_num [g, lc])]; norm_num [g, lc]; nlinarith
  · rw [div_le_iff₀ (by norm_num [g, lc])]; norm_num [g, lc]; nlinarith

/-- **Helix bounds for the geometry**: an annulus about the fixed `c0` of radius `R*(z)`, widening by `kappa` per
metre climbed, with altitude never below `z0` and climbing at `≥ 2 m/s` while below `ztop`. -/
theorem helix_bounds {c0 : ℂ} {z0 m0 ztop : ℝ} (hz0 : 0 ≤ z0) (hzt : ztop ≤ ZT) {s : St}
    (hs : DynH c0 z0 m0 ztop s) :
    z0 ≤ s.z ∧ (s.z < ztop →
      Rstar s.z - (m0 + kappa * (s.z - z0)) ≤ ‖pos s - c0‖ ∧ ‖pos s - c0‖ ≤ Rstar s.z + (m0 + kappa * (s.z - z0)) ∧
      176 ≤ Rstar s.z ∧ Rstar s.z ≤ 401 / 2 ∧ |radius s - Rstar s.z| ≤ DRAD ∧ 2 ≤ s.vz) := by
  obtain ⟨hQ, hz0s, -, hcone⟩ := hs
  refine ⟨hz0s, fun hlt => ?_⟩
  obtain ⟨hl, hc⟩ := hcone hlt
  have hzT : s.z ≤ ZT := hlt.le.trans hzt
  have hz0' : 0 ≤ s.z := hz0.trans hz0s
  have hp : pos s - c0 = (centre s - c0) - (Rstar s.z : ℂ) * I * cis s.psi := by unfold centre; ring
  have hn := norm_real_I_cis (Rstar s.z) s.psi
  have hR := Rstar_band hz0' hzT
  rw [abs_of_nonneg (by linarith [hR.1])] at hn
  have hv := (vz_band hQ).1
  refine ⟨?_, ?_, hR.1, hR.2, radius_err (long_extent hQ).1 hl hz0' hzT, ?_⟩
  · rw [hp]
    have := norm_sub_norm_le ((Rstar s.z : ℂ) * I * cis s.psi) (centre s - c0)
    rw [norm_sub_rev ((Rstar s.z : ℂ) * I * cis s.psi), hn] at this
    linarith
  · rw [hp]
    have := norm_sub_le (centre s - c0) ((Rstar s.z : ℂ) * I * cis s.psi)
    rw [hn] at this; linarith
  · simp only [vzStar, EH, E1, kV, v0, EVZ, ZT] at *; nlinarith

/-- **Ray bounds for the geometry**: a corridor about the track line widening by `kapY` per metre along track,
altitude at least `z0 + G · along-track` and climbing at `≥ 2.8 m/s` while below `ztop`. -/
theorem ray_bounds {x0 z0 w0 ztop : ℝ} (hz0 : 0 ≤ z0) (hzt : ztop ≤ ZT) {s : St}
    (hs : DynR x0 z0 w0 ztop s) :
    z0 ≤ s.z ∧ (s.z < ztop →
      x0 ≤ s.x ∧ |s.y| ≤ w0 + kapY * (s.x - x0) ∧ z0 + G * (s.x - x0) ≤ s.z ∧ |s.psi| ≤ ECH ∧
      28 / 10 ≤ s.vz) := by
  obtain ⟨hQ, hz0s, -, hcone⟩ := hs
  refine ⟨hz0s, fun hlt => ?_⟩
  obtain ⟨hT, hx, hy, hg⟩ := hcone hlt
  have hzT : s.z ≤ ZT := hlt.le.trans hzt
  have hv := (vz_band hQ).1
  refine ⟨hx, hy, hg, (lat_extent hT).1, ?_⟩
  simp only [vzStar, ER, E1, kV, v0, EVZ, ZT] at *; nlinarith

theorem Rstar_anti {z z' : ℝ} (h0 : 0 ≤ z) (hzz : z ≤ z') (h1 : z' ≤ ZT) : Rstar z' ≤ Rstar z := by
  obtain ⟨a, b⟩ := uStar_H_band h0 (by linarith)
  obtain ⟨c, d⟩ := uStar_H_band (h0.trans hzz) (by linarith)
  have hle : uStar EH z' ≤ uStar EH z := by simp only [uStar, E1]; nlinarith
  unfold Rstar
  apply div_le_div_of_nonneg_right _ (by norm_num [g, lc])
  nlinarith

/-- `helix_bounds` in the fixed-annulus form `Helix.Conf` of `Spec/EndSets.lean`, below `ztop`. -/
theorem helix_conf {c0 : ℂ} {z0 m0 ztop : ℝ} (hz0 : 0 ≤ z0) (hzt : ztop ≤ ZT) {s : St}
    (hs : DynH c0 z0 m0 ztop s) (hlt : s.z < ztop) :
    let r := (Rstar z0 + Rstar ztop) / 2
    let δ := (Rstar z0 - Rstar ztop) / 2 + m0 + kappa * (ztop - z0)
    r - δ ≤ ‖pos s - c0‖ ∧ ‖pos s - c0‖ ≤ r + δ ∧ z0 ≤ s.z := by
  obtain ⟨hz0s, hb⟩ := helix_bounds hz0 hzt hs
  obtain ⟨lo, hi, -, -, -, -⟩ := hb hlt
  have hz0' : 0 ≤ s.z := hz0.trans hz0s
  have a1 := Rstar_anti hz0 hz0s (hlt.le.trans hzt)
  have a2 := Rstar_anti hz0' hlt.le hzt
  have hk : kappa * (s.z - z0) ≤ kappa * (ztop - z0) :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num [kappa])
  refine ⟨by linarith, by linarith, hz0s⟩

/-- `ray_bounds` in the constant-width form `Ray.Conf` of `Spec/EndSets.lean`, below `ztop`: the along-track
distance below `ztop` is under `(ztop - z0) / G`. -/
theorem ray_conf {x0 z0 w0 ztop : ℝ} (hz0 : 0 ≤ z0) (hzt : ztop ≤ ZT) {s : St}
    (hs : DynR x0 z0 w0 ztop s) (hlt : s.z < ztop) :
    |s.y| ≤ w0 + kapY * ((ztop - z0) / G) ∧ 0 ≤ s.x - x0 ∧ z0 + G * (s.x - x0) ≤ s.z := by
  obtain ⟨-, hb⟩ := ray_bounds hz0 hzt hs
  obtain ⟨hx, hy, hg, -, -⟩ := hb hlt
  have hG : (0 : ℝ) < G := by norm_num [G]
  have hal : s.x - x0 ≤ (ztop - z0) / G := by rw [le_div_iff₀ hG]; nlinarith
  refine ⟨hy.trans (by gcongr; norm_num [kapY]), by linarith, hg⟩

end

end Proofs.TermSound
