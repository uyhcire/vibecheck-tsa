import Ci.proof.LawIv
import ExpJsb.IntervalSoundBase

/-! Soundness of `Ci.Proof.LawIv.elev`: on a box of states and memories, the law's elevator lies in the interval. -/

namespace Ci.Proof.LawIv
open ExpVibecheck ExpJsb Ci.Lawfirst

/-- `x ∈ a`. -/
def In (x : Int) (a : I) : Prop := a.1 ≤ x ∧ x ≤ a.2

theorem add_in {x y : Int} {a b : I} (hx : In x a) (hy : In y b) : In (x + y) (add a b) := by
  unfold In add at *; omega
theorem sub_in {x y : Int} {a b : I} (hx : In x a) (hy : In y b) : In (x - y) (sub a b) := by
  unfold In sub at *; omega
theorem const_in (c : Int) : In c (const c) := by unfold In const; omega
theorem mul_in {x y : Int} {a b : I} (hx : In x a) (hy : In y b) : In (x * y) (mul a b) := by
  have := ExpJsb.Iv.corners hx hy
  unfold In mul; simpa [ExpJsb.Iv.prods, ExpJsb.Iv.min4, ExpJsb.Iv.max4] using this
theorem divC_in {x : Int} {a : I} {d : Int} (hd : 0 < d) (hx : In x a) : In (x / d) (divC a d) := by
  unfold In divC at *
  exact ⟨Int.ediv_le_ediv hd hx.1, Int.ediv_le_ediv hd hx.2⟩
theorem divI_in {x y : Int} {a b : I} (hb : 0 < b.1) (hx : In x a) (hy : In y b) : In (x / y) (divI a b) := by
  have l1 := ExpJsb.Iv.div_range (N := a.1) hb hy
  have l2 := ExpJsb.Iv.div_range (N := a.2) hb hy
  have m1 : a.1 / y ≤ x / y := Int.ediv_le_ediv (by unfold In at hy; omega) hx.1
  have m2 : x / y ≤ a.2 / y := Int.ediv_le_ediv (by unfold In at hy; omega) hx.2
  unfold In divI; constructor <;> omega
theorem maxC_in {x : Int} {a : I} (c : Int) (hx : In x a) : In (max x c) (maxC a c) := by
  unfold In maxC at *; omega
theorem clamp_in {x : Int} {a : I} (lo hi : Int) (hx : In x a) : In (clampI lo hi x) (clamp lo hi a) := by
  unfold In clamp clampI at *; omega
theorem clampIv_in {x y : Int} {a b : I} (lo : Int) (hy : In y b) (hx : In x a) :
    In (clampI lo y x) (clampIv lo b a) := by
  unfold In clampIv clampI at *; omega
theorem nsqrt_mono {a b : Nat} (h : a ≤ b) : Nat.sqrt a ≤ Nat.sqrt b := by
  apply Nat.le_of_not_lt; intro hlt
  have h1 : Nat.succ (Nat.sqrt b) ≤ Nat.sqrt a := hlt
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := Nat.sqrt_le a
  have h4 := Nat.lt_succ_sqrt b
  omega
theorem sq_nonneg' (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ -x by omega); simpa [Int.neg_mul_neg] using this
theorem isqrt_in {x : Int} {a : I} (hx : In x a) : In (Nat.sqrt x.toNat : Int) (isqrt a) := by
  unfold In isqrt at *
  constructor
  · exact Int.ofNat_le.mpr (nsqrt_mono (Int.toNat_le_toNat hx.1))
  · exact Int.ofNat_le.mpr (nsqrt_mono (Int.toNat_le_toNat hx.2))
theorem sq_in {x : Int} {a : I} (hx : In x a) : In (x * x) (sq a) := by
  unfold In sq at *
  split
  · have := Int.mul_le_mul hx.1 hx.1 (by assumption) (by omega)
    have := Int.mul_le_mul hx.2 hx.2 (by omega) (by omega)
    constructor <;> omega
  · split
    · have h1 : 0 ≤ -x := by omega
      have := Int.mul_le_mul (show -a.2 ≤ -x by omega) (show -a.2 ≤ -x by omega) (by omega) h1
      have := Int.mul_le_mul (show -x ≤ -a.1 by omega) (show -x ≤ -a.1 by omega) h1 (by omega)
      simp only [Int.neg_mul_neg] at *
      constructor <;> omega
    · constructor
      · exact sq_nonneg' x
      · rcases Int.le_total 0 x with h | h
        · have := Int.mul_le_mul hx.2 hx.2 h (by omega); omega
        · have h1 : 0 ≤ -x := by omega
          have := Int.mul_le_mul (show -x ≤ -a.1 by omega) (show -x ≤ -a.1 by omega) h1 (by omega)
          simp only [Int.neg_mul_neg] at *; omega


/-- The box contains the state and memory. -/
structure Holds (b : Box) (s : State) (m : Mem) : Prop where
  vx : In s.vx.raw b.vx
  vz : In s.vz.raw b.vz
  dx : In s.dx.raw b.dx
  dz : In s.dz.raw b.dz
  q : In s.q.raw b.q
  ah : In s.ah.raw b.ah
  au : In s.au.raw b.au
  rho : In (ExpJsb.atmLookup ExpJsb.C172.atmRho s.h).raw b.rho
  eI : In m.eI b.eI

section
variable {b : Box} {s : State} {m : Mem} (H : Holds b s m)
include H

theorem u_in : In (s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw) (uI b) := add_in (mul_in H.vx H.dx) (mul_in H.vz H.dz)
theorem w_in : In (s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw) (wI b) := sub_in (mul_in H.vx H.dz) (mul_in H.vz H.dx)

theorem ta_in (hg : 0 < (uI b).1) : In (tanA s) (taI b) := by
  have hu := u_in H
  have hpos : s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw > 0 := by unfold In at hu; omega
  have : tanA s = (s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw) * 65536 / (s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw) := by
    unfold tanA; simp only [hpos, if_true, decide_true]
  rw [this]; exact divI_in hg (mul_in (w_in H) (const_in _)) hu

theorem v2s_in : In (s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw) (v2sI b) := add_in (sq_in H.vx) (sq_in H.vz)
theorem v_in : In (speedRaw s) (vI b) := isqrt_in (v2s_in H)

theorem tg_in (hg : 0 < b.vx.1) : In (tanG s) (tgI b) := by
  have hpos : s.vx.raw > 0 := by have := H.vx; unfold In at this; omega
  have : tanG s = s.vz.raw * 65536 / s.vx.raw := by unfold tanG; simp only [hpos, if_true, decide_true]
  rw [this]; exact divI_in hg (mul_in H.vz (const_in _)) H.vx

theorem n_in : In (nRaw s) (nI b) := by
  unfold nRaw Ci.loadNum
  exact divC_in (by decide) (sub_in (mul_in (add_in H.au (const_in _)) H.dx) (mul_in H.ah H.dz))

theorem raw_in (hg : 0 < b.vx.1) :
    In (p1.aRef + p1.kV * max (speedRaw s - p1.vC) (-vBand) / 65536 + p1.kG * (p1.gC - tanG s) / 65536 -
      p1.kGL * max 0 (tanG s - p1.gMax) / 65536) (rawI b) := by
  have htg := tg_in H hg
  have hm : max 0 (tanG s - p1.gMax) = max (tanG s - p1.gMax) 0 := Int.max_comm _ _
  rw [hm]
  exact sub_in (add_in (add_in (const_in _) (divC_in (by decide) (mul_in (const_in _)
    (maxC_in _ (sub_in (v_in H) (const_in _))))))
    (divC_in (by decide) (mul_in (const_in _) (sub_in (const_in _) htg))))
    (divC_in (by decide) (mul_in (const_in _) (maxC_in _ (sub_in htg (const_in _)))))

theorem nL_in : In (if s.vz.raw > 0 && p1.nLimUp ≥ 0 then p1.nLimUp else p1.nLim) (nLI b) := by
  have hv := H.vz
  unfold nLI In const at *
  have h1 : p1.nLimUp = 183500 := rfl
  have h2 : p1.nLim = 235929 := rfl
  by_cases c : s.vz.raw > 0
  · simp only [c, decide_true, Bool.true_and, h1]
    split <;> split <;> simp_all <;> omega
  · simp only [c, decide_false, Bool.false_and, h2]
    split <;> split <;> simp_all <;> omega

theorem alphaCmd_in (hg : guards b = true) : In (alphaCmd p1 s) (acI b) := by
  simp only [guards, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hu, hvx⟩, hn⟩, hta⟩, hv⟩ := hg
  have ta := ta_in H hu
  have n := n_in H
  have hnpos : nRaw s > 19661 := by unfold In at n; omega
  have htapos : tanA s > p1.a0 := by unfold In at ta; omega
  have haN : In (if nRaw s > 19661 && tanA s > p1.a0 then
      p1.a0 + (tanA s - p1.a0) * (if s.vz.raw > 0 && p1.nLimUp ≥ 0 then p1.nLimUp else p1.nLim) / nRaw s else p1.aMax)
      (aNI b) := by
    simp only [hnpos, htapos, decide_true, Bool.and_self, if_true]
    exact add_in (const_in _) (divI_in (by omega) (mul_in (sub_in ta (const_in _)) (nL_in H)) n)
  have hmin : In (min p1.aMax (if nRaw s > 19661 && tanA s > p1.a0 then
      p1.a0 + (tanA s - p1.a0) * (if s.vz.raw > 0 && p1.nLimUp ≥ 0 then p1.nLimUp else p1.nLim) / nRaw s else p1.aMax))
      (min p1.aMax (aNI b).1, min p1.aMax (aNI b).2) := by
    unfold In at *; omega
  exact clampIv_in _ hmin (raw_in H hvx)

theorem alphaCmd_range : p1.aMin ≤ alphaCmd p1 s ∧ alphaCmd p1 s ≤ p1.aMax := by
  have k : ∀ aN raw : Int, p1.aMin ≤ max p1.aMin (min (min p1.aMax aN) raw) ∧
      max p1.aMin (min (min p1.aMax aN) raw) ≤ p1.aMax := by
    intro aN raw
    have e3 : p1.aMin = -6000 := rfl
    have e4 : p1.aMax = 15000 := rfl
    rw [e3, e4]; omega
  exact k _ _

theorem ac_eq (hac : -900000 ≤ m.ac ∧ m.ac ≤ 900000) :
    clampI (m.ac - p1.rDn) (m.ac + p1.rUp) (alphaCmd p1 s) = alphaCmd p1 s := by
  have := alphaCmd_range (b := b) H
  have e1 : p1.rDn = 1000000 := rfl
  have e2 : p1.rUp = 1000000 := rfl
  have e3 : p1.aMin = -6000 := rfl
  have e4 : p1.aMax = 15000 := rfl
  unfold clampI; rw [e1, e2]; rw [e3, e4] at this; omega

theorem ne_in (hg : 0 < (uI b).1) : In (nEst s (tanA s)) (neI b) := by
  unfold nEst
  exact divC_in (by decide) (mul_in (divC_in (by decide) (mul_in (divC_in (by decide) (mul_in H.rho
    (divC_in (by decide) (v2s_in H)))) (add_in (ta_in H hg) (const_in _)))) (const_in _))

/-- The law's elevator lies in `elev b`. -/
theorem elev_sound (hac : -900000 ≤ m.ac ∧ m.ac ≤ 900000) {e : I} (he : elev b = some e) :
    In (stepP p1 m s).1.elev.raw e := by
  unfold elev at he
  split at he
  · rename_i hg
    cases he
    have hg' := hg
    simp only [guards, Bool.and_eq_true, decide_eq_true_eq] at hg'
    obtain ⟨⟨⟨⟨hu, hvx⟩, hn⟩, hta⟩, hv⟩ := hg'
    have ta := ta_in H hu
    have hacv := alphaCmd_in H hg
    have hv' := v_in H
    have hmax : max 65536 (speedRaw s) = speedRaw s := by unfold In at hv'; omega
    have qRef : In (Ci.gRaw * (nEst s (tanA s) - 65536) / max 65536 (speedRaw s)) (qRefI b) := by
      rw [hmax]; exact divI_in (by omega) (mul_in (const_in _) (sub_in (ne_in H hu) (const_in _))) hv'
    show In (clampI (-65536) 65536 (m.eI + p1.kF * clampI (m.ac - p1.rDn) (m.ac + p1.rUp) (alphaCmd p1 s) / 65536 +
      p1.kA * (clampI (m.ac - p1.rDn) (m.ac + p1.rUp) (alphaCmd p1 s) - tanA s) / 65536 -
      p1.kQ * (s.q.raw - (if p1.qss then Ci.gRaw * (nEst s (tanA s) - 65536) / max 65536 (speedRaw s) else 0)) / 65536)) _
    rw [ac_eq H hac]
    have hq : p1.qss = true := rfl
    simp only [hq, if_true]
    exact clamp_in _ _ (sub_in (add_in (add_in H.eI (divC_in (by decide) (mul_in (const_in _) hacv)))
      (divC_in (by decide) (mul_in (const_in _) (sub_in hacv ta))))
      (divC_in (by decide) (mul_in (const_in _) (sub_in H.q qRef))))
  · cases he

end

end Ci.Proof.LawIv
