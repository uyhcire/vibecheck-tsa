import Proofs.CiProof.StaticDisp
import Proofs.CiProof.Bridge
import Ci.proof.StaticCells
import Ci.proof.BandNext
import Ci.proof.SafeCells

/-! The static fit: a state that passes the band, slow-quadratic and fast checks lies in its cell box
(`static_box : restOk p = true → boxOk p = true`). The slow deviations are bounded by the certified `slowB`
(LDLᵀ certificates), the fast ones by the slaving, kink and tolerance terms, and the table half is `static_cells`. -/

namespace Proofs.CiProof.Skel
open Matrix Ci.Proof

theorem lerp_le_max (a b f S : Int) (hS : 0 < S) (f0 : 0 ≤ f) (f1 : f ≤ S) : lerp a b f S ≤ max a b := by
  unfold lerp
  rcases le_total a b with h | h
  · have h2 : (b - a) * f ≤ (b - a) * S := Int.mul_le_mul_of_nonneg_left f1 (by omega)
    have h3 : (b - a) * f / S ≤ (b - a) * S / S := Int.ediv_le_ediv hS h2
    rw [Int.mul_ediv_cancel _ (by omega)] at h3
    omega
  · have h1 : (b - a) * f ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) f0
    have h2 : (b - a) * f / S ≤ 0 / S := Int.ediv_le_ediv hS h1
    rw [Int.zero_ediv] at h2
    omega

theorem slowB_pos : ∀ i, i < 27 → ∀ k, k < 7 → (1 : Int) ≤ (TData.slowB[i]!)[k]! := by decide

/-- The slow deviations are bounded by the certified `slowB − 1`. -/
theorem slow_dev (p : Jsb.State × Ci.Lawfirst.Mem) (hb : bandOk p = true) (hq : quadOk p = true) (k : Nat)
    (hk : k < 7) : -(sbound (nodeJ p.1.h.raw) k) ≤ dev p k ∧ dev p k ≤ sbound (nodeJ p.1.h.raw) k := by
  obtain ⟨hl, hh⟩ := band_h hb
  have h0 : 0 ≤ p.1.h.raw := le_trans (by unfold hLoT; decide) hl
  have hj := nodeJ_le h0 hh
  set i := nodeJ p.1.h.raw with hi
  obtain ⟨f0, f1⟩ := nodeF_range h0
  have hR := (quad_real p hb).2
  have hsc := qf_P_scaled p h0
  have hq' := hq
  unfold quadOk at hq'
  simp only [decide_eq_true_eq] at hq'
  have hrmax := lerp_le_max TData.r2Tab[i]! TData.r2Tab[i + 1]! (nodeF p.1.h.raw) (100 * 65536) (by decide) f0 f1.le
  have c0 := scd i k i (by omega) hk (Or.inl rfl) (z p)
  have c1 := scd i k (i + 1) (by omega) hk (Or.inr rfl) (z p)
  rw [qf_pNode_quad] at c0 c1
  have hB := slowB_pos i (by omega) k hk
  set Rb : ℝ := ((max TData.r2Tab[i]! TData.r2Tab[i + 1]! + 1 : Int) : ℝ)
  set B : ℝ := (((TData.slowB[i]!)[k]! : Int) : ℝ)
  set Q0 : ℝ := ((quad TData.pTab[i]! (dSlow p) : Int) : ℝ)
  set Q1 : ℝ := ((quad TData.pTab[i + 1]! (dSlow p) : Int) : ℝ)
  set t : ℝ := (nodeF p.1.h.raw : ℝ) / (100 * 65536)
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast f0) (by norm_num)
  have ht1 : t ≤ 1 := by rw [div_le_one (by norm_num)]; exact_mod_cast f1.le
  have hI : lerp (quad TData.pTab[i]! (dSlow p)) (quad TData.pTab[i + 1]! (dSlow p)) (nodeF p.1.h.raw)
      (100 * 65536) + 1 ≤ max TData.r2Tab[i]! TData.r2Tab[i + 1]! + 1 := by
    rw [hi]; rw [hi] at hrmax; omega
  have hRb : (2 : ℝ) ^ TData.pK * qf (P p) (z p) < Rb := by
    have h2 : ((lerp (quad TData.pTab[i]! (dSlow p)) (quad TData.pTab[i + 1]! (dSlow p)) (nodeF p.1.h.raw)
        (100 * 65536) + 1 : Int) : ℝ) ≤ Rb := by simp only [Rb]; exact_mod_cast hI
    push_cast at h2
    rw [← hi] at hR
    have e6 : (100 * 65536 : Int) = 6553600 := by norm_num
    rw [e6] at hR
    linarith
  rw [hsc] at hRb
  have hzk : z p ⟨k, hk⟩ = (dev p k : ℝ) := rfl
  rw [hzk] at c0 c1
  have hRbpos : 0 < Rb := by
    have : (0 : Int) < max TData.r2Tab[i]! TData.r2Tab[i + 1]! + 1 := by
      have := r2Tab_pos i (by omega); omega
    show (0 : ℝ) < ((max TData.r2Tab[i]! TData.r2Tab[i + 1]! + 1 : Int) : ℝ)
    exact_mod_cast this
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
  have m0 := mul_le_mul_of_nonneg_left c0 (show (0 : ℝ) ≤ 1 - t by linarith)
  have m1 := mul_le_mul_of_nonneg_left c1 ht0
  have comb : Rb * (dev p k : ℝ) ^ 2 ≤ B ^ 2 * (Q0 + (Q1 - Q0) * t) := by nlinarith
  have key : Rb * (dev p k : ℝ) ^ 2 < B ^ 2 * Rb := by
    have hBpos : (1 : ℝ) ≤ B := by show (1 : ℝ) ≤ (((TData.slowB[i]!)[k]! : Int) : ℝ); exact_mod_cast hB
    have : B ^ 2 * (Q0 + (Q1 - Q0) * t) < B ^ 2 * Rb := mul_lt_mul_of_pos_left hRb (by positivity)
    linarith
  have key2 : (dev p k : ℝ) ^ 2 < B ^ 2 := by
    have : Rb * (dev p k : ℝ) ^ 2 < Rb * B ^ 2 := by linarith
    exact lt_of_mul_lt_mul_left this hRbpos.le
  simp only [B] at key2
  have key3 : ((dev p k) ^ 2 : Int) < ((TData.slowB[i]!)[k]!) ^ 2 := by exact_mod_cast key2
  have : |dev p k| < (TData.slowB[i]!)[k]! := abs_lt_of_sq_lt_sq key3 (by omega)
  have h2 := abs_lt.mp this
  unfold sbound
  constructor <;> omega

theorem term_bd (g d s : Int) (h : -s ≤ d ∧ d ≤ s) : -(iabs g * s) ≤ g * d ∧ g * d ≤ iabs g * s := by
  unfold iabs
  rcases le_total 0 g with hg | hg
  · rw [max_eq_left (by omega)]; constructor <;> nlinarith
  · rw [max_eq_right (by omega)]; constructor <;> nlinarith

theorem div_bd (x M c : Int) (hc : 0 < c) (h : -M ≤ x ∧ x ≤ M) : -(M / c) - 1 ≤ x / c ∧ x / c ≤ M / c := by
  constructor
  · have h1 : (-M) / c ≤ x / c := Int.ediv_le_ediv hc h.1
    have h2 := Int.lt_ediv_add_one_mul_self M hc
    have h3 : -(M / c) - 1 ≤ (-M) / c := by
      rw [Int.le_ediv_iff_mul_le hc]; nlinarith
    omega
  · exact Int.ediv_le_ediv hc h.2

theorem mul_bd (x y X Y : Int) (hx : -X ≤ x ∧ x ≤ X) (hy : -Y ≤ y ∧ y ≤ Y) : -(X * Y) ≤ x * y ∧ x * y ≤ X * Y := by
  constructor <;> nlinarith

theorem lerp_in (a b f S : Int) (hS : 0 < S) (f0 : 0 ≤ f) (f1 : f ≤ S) :
    min a b ≤ lerp a b f S ∧ lerp a b f S ≤ max a b :=
  ⟨lerp_ge_min a b f S hS f0 f1, lerp_le_max a b f S hS f0 f1⟩

theorem fastEs_get (p : Jsb.State × Ci.Lawfirst.Mem) (kk : Nat) (hk : kk < 10) :
    (fastEs p)[kk]! = dev p (TData.nSlow + kk) - lerp (gmul TData.gTab[nodeJ p.1.h.raw]! (dSlow p) kk)
      (gmul TData.gTab[nodeJ p.1.h.raw + 1]! (dSlow p) kk) (nodeF p.1.h.raw) (100 * 65536) / (2 ^ TData.gK : Int) := by
  have hn : nFast = 10 := by decide
  simp only [fastEs, hn]
  simp [hk]

theorem gmul_bd (G : Array (Array Int)) (p : Jsb.State × Ci.Lawfirst.Mem) (j kk : Nat)
    (hd : ∀ i, i < 7 → -(sbound j i) ≤ dev p i ∧ dev p i ≤ sbound j i) :
    -(((List.range 7).map fun i => iabs (G[kk]!)[i]! * sbound j i).sum) ≤ gmul G (dSlow p) kk ∧
      gmul G (dSlow p) kk ≤ ((List.range 7).map fun i => iabs (G[kk]!)[i]! * sbound j i).sum := by
  have e : ∀ i, i < 7 → (dSlow p)[i]! = dev p i := fun i hi => dSlow_get p ⟨i, hi⟩
  have t := fun (i : Nat) (hi : i < 7) => term_bd (G[kk]!)[i]! ((dSlow p)[i]!) (sbound j i) (by rw [e i hi]; exact hd i hi)
  have t0 := t 0 (by decide); have t1 := t 1 (by decide); have t2 := t 2 (by decide); have t3 := t 3 (by decide)
  have t4 := t 4 (by decide); have t5 := t 5 (by decide); have t6 := t 6 (by decide)
  simp only [gmul, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.map_append,
    List.sum_cons, List.sum_nil, List.sum_append]
  constructor <;> omega

/-- The fast deviations are bounded by `fbound`. -/
theorem fast_dev (p : Jsb.State × Ci.Lawfirst.Mem) (hb : bandOk p = true) (hq : quadOk p = true)
    (hf : fastOk p = true) (kk : Nat) (hk : kk < 10) :
    -(fbound (nodeJ p.1.h.raw) kk) ≤ dev p (TData.nSlow + kk) ∧ dev p (TData.nSlow + kk) ≤ fbound (nodeJ p.1.h.raw) kk := by
  obtain ⟨hl, hh⟩ := band_h hb
  have h0 : 0 ≤ p.1.h.raw := le_trans (by unfold hLoT; decide) hl
  obtain ⟨f0, f1⟩ := nodeF_range h0
  set j := nodeJ p.1.h.raw with hjd
  have hd : ∀ i, i < 7 → -(sbound j i) ≤ dev p i ∧ dev p i ≤ sbound j i := fun i hi => slow_dev p hb hq i hi
  have hn : nFast = 10 := by decide
  have hf' := hf
  unfold fastOk at hf'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, hn] at hf'
  obtain ⟨⟨hl1, hl2⟩, hper⟩ := hf'
  have hp := hper kk hk
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  rw [fastEs_get p kk hk] at hp
  simp only [← hjd] at hl1 hl2 hp
  have g0 := gmul_bd TData.gTab[j]! p j kk hd
  have g1 := gmul_bd TData.gTab[j + 1]! p j kk hd
  have S0 : (0 : Int) < 100 * 65536 := by decide
  have lg := lerp_in (gmul TData.gTab[j]! (dSlow p) kk) (gmul TData.gTab[j + 1]! (dSlow p) kk) (nodeF p.1.h.raw)
    (100 * 65536) S0 f0 f1.le
  set Mg := max (gabs j j kk) (gabs j (j + 1) kk)
  have hMg : -Mg ≤ lerp (gmul TData.gTab[j]! (dSlow p) kk) (gmul TData.gTab[j + 1]! (dSlow p) kk) (nodeF p.1.h.raw)
      (100 * 65536) ∧ lerp (gmul TData.gTab[j]! (dSlow p) kk) (gmul TData.gTab[j + 1]! (dSlow p) kk) (nodeF p.1.h.raw)
      (100 * 65536) ≤ Mg := by
    have e0 : gabs j j kk = ((List.range 7).map fun i => iabs ((TData.gTab[j]!)[kk]!)[i]! * sbound j i).sum := rfl
    have e1 : gabs j (j + 1) kk = ((List.range 7).map fun i => iabs ((TData.gTab[j + 1]!)[kk]!)[i]! * sbound j i).sum := rfl
    simp only [Mg, e0, e1]
    constructor <;> omega
  have dp := div_bd _ Mg (2 ^ TData.gK) (by decide) hMg
  have ltk := lerp_in TData.tkTab[j]! TData.tkTab[j + 1]! (nodeF p.1.h.raw) (100 * 65536) S0 f0 f1.le
  have lkb := lerp_in (TData.kbTab[j]!)[kk]! (TData.kbTab[j + 1]!)[kk]! (nodeF p.1.h.raw) (100 * 65536) S0 f0 f1.le
  have ltp := lerp_in (TData.tpTab[j]!)[kk]! (TData.tpTab[j + 1]!)[kk]! (nodeF p.1.h.raw) (100 * 65536) S0 f0 f1.le
  set TK := max TData.tkTab[j]! TData.tkTab[j + 1]!
  set KB := max (iabs (TData.kbTab[j]!)[kk]!) (iabs (TData.kbTab[j + 1]!)[kk]!)
  have hlam : -TK ≤ fastLam p ∧ fastLam p ≤ TK := by constructor <;> omega
  have hkb : -KB ≤ lerp (TData.kbTab[j]!)[kk]! (TData.kbTab[j + 1]!)[kk]! (nodeF p.1.h.raw) (100 * 65536) ∧
      lerp (TData.kbTab[j]!)[kk]! (TData.kbTab[j + 1]!)[kk]! (nodeF p.1.h.raw) (100 * 65536) ≤ KB := by
    simp only [KB, iabs]; constructor <;> omega
  have mb := mul_bd _ _ TK KB hlam hkb
  have db := div_bd _ (TK * KB) (2 ^ 50) (by decide) mb
  have hfb : fbound j kk = Mg / (2 ^ TData.gK : Int) + 1 + TK * KB / (2 ^ 50 : Int) + 1 +
      max (TData.tpTab[j]!)[kk]! (TData.tpTab[j + 1]!)[kk]! := rfl
  rw [hfb]
  constructor <;> omega

/-- The static fit: a state that passes the band, slow-quadratic and fast checks lies in its cell box. -/
theorem static_box (p : Jsb.State × Ci.Lawfirst.Mem) (hb : bandOk p = true) (hq : quadOk p = true)
    (hf : fastOk p = true) : boxOk p = true := by
  have hb' := hb
  unfold bandOk at hb'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb'
  obtain ⟨⟨⟨⟨hlo, hhi⟩, hst⟩, hac1⟩, hac2⟩ := hb'
  set h := p.1.h.raw with hdef
  have eL : hLoT = 655360 := rfl
  have eH : hHiT = 175636480 := rfl
  have eS : cellSpan = 655360 := rfl
  set ci := cellIdx h with hci
  have hci' : (ci : Int) = (h - hLoT) / cellSpan := by
    rw [hci]; unfold cellIdx; rw [Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) (by rw [eS]; decide))]
  have hcilt : ci < 267 := by
    have : (ci : Int) < 267 := by rw [hci', eL, eS]; omega
    omega
  have hsz : TData.boxTab.size = 267 := Ci.Proof.SafeIv.boxTab_size
  have sc := static_cells ci hcilt
  unfold staticOk at sc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at sc
  obtain ⟨⟨⟨⟨⟨⟨⟨hrows, hbl⟩, hbh⟩, hsl⟩, hsh⟩, hnj⟩, ha2⟩, ha0⟩ := sc
  set a := cellLo ci with hadef
  have hca : a = hLoT + ci * cellSpan := rfl
  have hh1 : a ≤ h ∧ h < a + cellSpan := by rw [hca, hci']; rw [eL, eS] at *; constructor <;> omega
  -- node interval of the cell
  have hj : nodeJ h = nodeJ a := by
    have m1 : nodeJ a ≤ nodeJ h := by
      unfold nodeJ; apply Int.toNat_le_toNat; exact Int.ediv_le_ediv (by decide) hh1.1
    have m2 : nodeJ h ≤ nodeJ (a + cellSpan - 1) := by
      unfold nodeJ; apply Int.toNat_le_toNat; exact Int.ediv_le_ediv (by decide) (by omega)
    omega
  -- row of the centre table
  set ii := (h / (2 * 65536)).toNat with hii
  have hrow : ∃ r, r < 5 ∧ ii = (a / (2 * 65536)).toNat + r := by
    refine ⟨ii - (a / (2 * 65536)).toNat, ?_, ?_⟩ <;> rw [hii] <;> rw [eS] at hh1 <;>
      have q1 : 0 ≤ a / (2 * 65536) := Int.ediv_nonneg ha0 (by decide) <;>
      have q2 : 0 ≤ h / (2 * 65536) := Int.ediv_nonneg (by omega) (by decide) <;> omega
  obtain ⟨r, hr5, hrr⟩ := hrow
  have hk := hrows r hr5
  rw [← hrr] at hk
  -- each listed field lies in the box
  have field_in : ∀ k, k < 17 → boxLo ci TData.fields[k]! ≤ coord p.1 p.2 TData.fields[k]! ∧
      coord p.1 p.2 TData.fields[k]! ≤ boxHi ci TData.fields[k]! := by
    intro k hk17
    have hb2 := hk k hk17
    have hdv : -(fieldBound (nodeJ a) k) ≤ dev p k ∧ dev p k ≤ fieldBound (nodeJ a) k := by
      unfold fieldBound
      by_cases h7 : k < 7
      · rw [if_pos h7, ← hj]; exact slow_dev p hb hq k h7
      · rw [if_neg h7, ← hj]
        have := fast_dev p hb hq hf (k - 7) (by omega)
        have e : TData.nSlow + (k - 7) = k := by
          have : TData.nSlow = 7 := rfl
          omega
        rw [e] at this; exact this
    have hcoord : coord p.1 p.2 TData.fields[k]! = dev p k + lerp ((TData.centre[ii]!)[k]!) ((TData.centre[ii + 1]!)[k]!)
        (h - ii * (2 * 65536)) (2 * 65536) := by
      unfold dev; simp only [hii, hdef]; ring
    have q2 : 0 ≤ h / (2 * 65536) := Int.ediv_nonneg (by omega) (by decide)
    have hf0 : 0 ≤ h - ii * (2 * 65536) := by rw [hii, Int.toNat_of_nonneg q2]; omega
    have hf1 : h - ii * (2 * 65536) ≤ 2 * 65536 := by rw [hii, Int.toNat_of_nonneg q2]; omega
    have hl := lerp_in ((TData.centre[ii]!)[k]!) ((TData.centre[ii + 1]!)[k]!) (h - ii * (2 * 65536)) (2 * 65536)
      (by decide) hf0 hf1
    rw [hcoord]
    obtain ⟨b1, b2⟩ := hb2
    constructor <;> omega
  -- assemble the box membership
  have hsize : cellIdx h < TData.boxTab.size := by rw [hsz]; exact hcilt
  unfold boxOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hsize, hac1, hac2⟩, ?_⟩
  have F0 := field_in 0 (by decide)
  rw [show TData.fields[0]! = 2 from by decide] at F0
  have F1 := field_in 1 (by decide)
  rw [show TData.fields[1]! = 3 from by decide] at F1
  have F2 := field_in 2 (by decide)
  rw [show TData.fields[2]! = 5 from by decide] at F2
  have F3 := field_in 3 (by decide)
  rw [show TData.fields[3]! = 6 from by decide] at F3
  have F4 := field_in 4 (by decide)
  rw [show TData.fields[4]! = 7 from by decide] at F4
  have F5 := field_in 5 (by decide)
  rw [show TData.fields[5]! = 8 from by decide] at F5
  have F6 := field_in 6 (by decide)
  rw [show TData.fields[6]! = 19 from by decide] at F6
  have F7 := field_in 7 (by decide)
  rw [show TData.fields[7]! = 4 from by decide] at F7
  have F8 := field_in 8 (by decide)
  rw [show TData.fields[8]! = 9 from by decide] at F8
  have F9 := field_in 9 (by decide)
  rw [show TData.fields[9]! = 10 from by decide] at F9
  have F10 := field_in 10 (by decide)
  rw [show TData.fields[10]! = 12 from by decide] at F10
  have F11 := field_in 11 (by decide)
  rw [show TData.fields[11]! = 13 from by decide] at F11
  have F12 := field_in 12 (by decide)
  rw [show TData.fields[12]! = 14 from by decide] at F12
  have F13 := field_in 13 (by decide)
  rw [show TData.fields[13]! = 15 from by decide] at F13
  have F14 := field_in 14 (by decide)
  rw [show TData.fields[14]! = 16 from by decide] at F14
  have F15 := field_in 15 (by decide)
  rw [show TData.fields[15]! = 17 from by decide] at F15
  have F16 := field_in 16 (by decide)
  rw [show TData.fields[16]! = 18 from by decide] at F16
  norm_num [boxLo, boxHi] at F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 hbl hbh hsl hsh
  simp only [coord] at F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16
  unfold cellBox pt Jsb.CLOf.Mem Jsb.StateOf.Mem
  simp only [Jsb.Iv.mem_top, Jsb.Iv.mem_box, true_and]
  simp only [← hdef]
  simp only [← hci]
  constructorm* _ ∧ _
  all_goals omega

/-- `TInvariant lawT` from the fast-coordinate obligation and the enclosure alone: the band part of the side
conditions is `band_next`, the cell boxes follow from the static fit, the integer/real bridges are proved. -/
theorem tInvariant_of_fast_enc
    (hfast : ∀ s m, L.inT (s, m) = true → fastOk ((Ci.tickT L s m).s, (Ci.tickT L s m).m) = true)
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (e : Fin 7 → ℝ) (ρ ε : ℝ),
      z ((Ci.tickT L s m).s, (Ci.tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((Ci.tickT L s m).s, (Ci.tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((Ci.tickT L s m).s, (Ci.tickT L s m).m)) e ≤ ε ^ 2 ∧
      ρ * rIn (s, m) + ε ≤ rOut ((Ci.tickT L s m).s, (Ci.tickT L s m).m)) :
    Ci.Goals.TInvariant L := by
  let side' : Jsb.State × Ci.Lawfirst.Mem → Prop := fun p => bandOk p = true ∧ fastOk p = true
  have hin : ∀ p, L.inT p = true → side' p ∧ qf (P p) (z p) ≤ rIn p ^ 2 := fun p hT =>
    ⟨⟨(bridge_in p hT).1.1, (bridge_in p hT).1.2.1⟩, (bridge_in p hT).2⟩
  have hout : ∀ p, side' p → qf (P p) (z p) ≤ rOut p ^ 2 → L.inT p = true := by
    intro p hs hq
    obtain ⟨hb, hf⟩ := hs
    have hr := r2At_pos hb
    have qr := (quad_real p hb).1
    unfold rOut at hq
    rw [Real.sq_sqrt (by positivity), le_div_iff₀ (by positivity)] at hq
    have : (lerp (quad TData.pTab[nodeJ p.1.h.raw]! (dSlow p)) (quad TData.pTab[nodeJ p.1.h.raw + 1]! (dSlow p))
        (nodeF p.1.h.raw) (100 * 65536) : ℝ) ≤ (r2At p : ℝ) := by linarith
    have hq2 : quadOk p = true := by
      unfold quadOk
      simp only [decide_eq_true_eq]
      exact_mod_cast this
    have hx := static_box p hb hq2 hf
    show inT p = true
    unfold inT restOk
    simp [hb, hq2, hf, hx]
  have hside : ∀ s m, L.inT (s, m) = true → side' ((Ci.tickT L s m).s, (Ci.tickT L s m).m) := fun s m hT =>
    ⟨Ci.Proof.SafeIv.band_next s m hT, hfast s m hT⟩
  intro s m hT
  exact ⟨(Ci.Proof.SafeIv.tick_safe_climb s m hT).1, (Ci.Proof.SafeIv.tick_safe_climb s m hT).2,
    inT_next_of_lyap L side' z P rIn rOut (fun _ => Real.sqrt_nonneg _) P_psd hin hout hside henc s m hT⟩

end Proofs.CiProof.Skel
