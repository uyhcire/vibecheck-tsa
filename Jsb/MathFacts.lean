import Jsb.Math

/-! The `Int64` fast paths and `isqrt` of `Jsb.Math` agree with plain `Int`/`Nat` arithmetic (no overflow). -/

namespace Jsb
open Vibecheck

def InI64 (x : Int) : Prop := -9223372036854775808 ≤ x ∧ x < 9223372036854775808

theorem toInt_ofInt_of {x : Int} (h : InI64 x) : (Int64.ofInt x).toInt = x :=
  Int64.toInt_ofInt_of_le h.1 h.2

theorem bmod64_of {x : Int} (h : InI64 x) : x.bmod (2 ^ 64) = x :=
  Int.bmod_eq_of_le (by have := h.1; omega) (by have := h.2; omega)

theorem toInt_shr16 (x : Int64) : (x >>> (16 : Int64)).toInt = x.toInt / 65536 := by
  rw [Fx.shr16, Int.shiftRight_eq_div_pow]; rfl

theorem toInt_shr30 (x : Int64) : (x >>> (30 : Int64)).toInt = x.toInt / 1073741824 := by
  have h : (30 : Int64).toBitVec.smod 64 = 30#64 := by decide
  rw [← Int64.toInt_toBitVec, Int64.toBitVec_shiftRight, h, BitVec.toInt_sshiftRight', Int64.toInt_toBitVec,
    Int.shiftRight_eq_div_pow]; rfl

theorem toInt_shl16 (x : Int64) (h : -140737488355328 ≤ x.toInt ∧ x.toInt < 140737488355328) :
    (x <<< (16 : Int64)).toInt = x.toInt * 65536 := by
  have e : x <<< (16 : Int64) = x * 65536 := by
    apply Int64.toBitVec_inj.mp
    have h16 : (16 : Int64).toBitVec.smod 64 = 16#64 := by decide
    rw [Int64.toBitVec_shiftLeft, h16, BitVec.shiftLeft_eq', Int64.toBitVec_mul]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  rw [e, Int64.toInt_mul]
  have : (65536 : Int64).toInt = 65536 := by decide
  rw [this]; exact bmod64_of ⟨by omega, by omega⟩

theorem int64_le_iff {a : Int64} {x : Int} (ha : a.toInt = x) (c : Int64) (cv : Int) (hc : c.toInt = cv) :
    (c ≤ a ↔ cv ≤ x) := by rw [Int64.le_iff_toInt_le, ha, hc]

theorem int64_lt_iff {a : Int64} {x : Int} (ha : a.toInt = x) (c : Int64) (cv : Int) (hc : c.toInt = cv) :
    (a < c ↔ x < cv) := by rw [Int64.lt_iff_toInt_lt, ha, hc]

/-- Bounds on Euclidean division by a positive divisor. -/
theorem ediv_bounds {a b : Int} (hb : 0 < b) : (0 ≤ a → 0 ≤ a / b ∧ a / b ≤ a) ∧ (a < 0 → a ≤ a / b ∧ a / b < 0) := by
  constructor
  · intro ha; exact ⟨Int.ediv_nonneg ha (by omega), Int.ediv_le_self b ha⟩
  · intro ha
    constructor
    · rw [Int.le_ediv_iff_mul_le hb]
      have : a * (b - 1) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      rw [Int.mul_sub, Int.mul_one] at this; omega
    · rw [Int.ediv_lt_iff_lt_mul hb]; omega

theorem floorDiv64_toInt (a b : Int64) (hb : 0 < b.toInt) : (floorDiv64 a b).toInt = a.toInt / b.toInt := by
  have ha := a.toInt.le_refl
  have hlo := Int64.le_toInt a
  have hhi := Int64.toInt_lt a
  have hdiv := Int64.toInt_div a b
  have hmod := Int64.toInt_mod a b
  have te := @Int.tdiv_eq_ediv a.toInt b.toInt
  have tm := @Int.tmod_eq_emod a.toInt b.toInt
  have em := Int.emod_lt_of_pos a.toInt hb
  have en := Int.emod_nonneg a.toInt (show b.toInt ≠ 0 by omega)
  have eb := ediv_bounds (a := a.toInt) hb
  have sg : b.toInt.sign = 1 := Int.sign_eq_one_of_pos hb
  have nb : (b.toInt.natAbs : Int) = b.toInt := Int.natAbs_of_nonneg (by omega)
  unfold floorDiv64
  simp only
  by_cases c : 0 ≤ a.toInt ∨ b.toInt ∣ a.toInt
  · simp only [c, ite_true, Int.add_zero, Int.sub_zero, Int.cast_ofNat_Int] at te tm
    have : ¬ (a % b < 0) := by
      rw [Int64.lt_iff_toInt_lt, hmod, tm]; simp; omega
    simp only [this, ite_false, hdiv, te]
    apply bmod64_of
    by_cases h0 : 0 ≤ a.toInt
    · have := eb.1 h0; constructor <;> omega
    · have := eb.2 (by omega); constructor <;> omega
  · simp only [c, ite_false, sg, nb] at te tm
    have hn : a.toInt < 0 := by omega
    have : a % b < 0 := by
      rw [Int64.lt_iff_toInt_lt, hmod, tm]; simp; omega
    simp only [this, ite_true]
    rw [Int64.toInt_sub, hdiv, te, Int64.toInt_one]
    have := eb.2 hn
    rw [bmod64_of (x := a.toInt / b.toInt + 1) ⟨by omega, by omega⟩, bmod64_of ⟨by omega, by omega⟩]; omega

theorem floorDiv_eq (n d : Int) (hn : InI64 n) (hd : InI64 d) (hp : 0 < d) : floorDiv n d = n / d := by
  unfold floorDiv
  simp only [hp, ite_true]
  rw [floorDiv64_toInt _ _ (by rw [toInt_ofInt_of hd]; exact hp), toInt_ofInt_of hn, toInt_ofInt_of hd]

theorem lit64_m31 : (-2147483648 : Int64).toInt = -2147483648 := by decide
theorem lit64_31 : (2147483648 : Int64).toInt = 2147483648 := by decide
theorem lit64_m47 : (-140737488355328 : Int64).toInt = -140737488355328 := by decide
theorem lit64_47 : (140737488355328 : Int64).toInt = 140737488355328 := by decide
theorem lit64_0 : (0 : Int64).toInt = 0 := by decide
theorem lit64_32768 : (32768 : Int64).toInt = 32768 := by decide

theorem fmul_raw (a b : Fx) (ha : InI64 a.raw) (hb : InI64 b.raw) : (fmul a b).raw = a.raw * b.raw / 65536 := by
  have ea := toInt_ofInt_of ha
  have eb := toInt_ofInt_of hb
  unfold fmul
  simp only [int64_le_iff ea _ _ lit64_m31, int64_lt_iff ea _ _ lit64_31, int64_le_iff eb _ _ lit64_m31,
    int64_lt_iff eb _ _ lit64_31]
  split
  · rename_i h
    have hm := Fx.mul_bound a.raw b.raw ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩
    simp only [toInt_shr16, Int64.toInt_mul, ea, eb]
    rw [bmod64_of ⟨by omega, by omega⟩]
  · rfl

theorem mulR_raw (a b : Fx) (ha : InI64 a.raw) (hb : InI64 b.raw) :
    (mulR a b).raw = (a.raw * b.raw + 32768) / 65536 := by
  have ea := toInt_ofInt_of ha
  have eb := toInt_ofInt_of hb
  unfold mulR
  simp only [int64_le_iff ea _ _ lit64_m31, int64_lt_iff ea _ _ lit64_31, int64_le_iff eb _ _ lit64_m31,
    int64_lt_iff eb _ _ lit64_31]
  split
  · rename_i h
    have hm := Fx.mul_bound a.raw b.raw ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩
    simp only [toInt_shr16, Int64.toInt_add, Int64.toInt_mul, ea, eb, lit64_32768]
    rw [bmod64_of (x := a.raw * b.raw) ⟨by omega, by omega⟩, bmod64_of ⟨by omega, by omega⟩]
  · rfl

theorem fdiv_raw (a b : Fx) (ha : InI64 a.raw) (hb : InI64 b.raw) : (fdiv a b).raw = a.raw * 65536 / b.raw := by
  have ea := toInt_ofInt_of ha
  have eb := toInt_ofInt_of hb
  unfold fdiv
  simp only [int64_le_iff ea _ _ lit64_m47, int64_lt_iff ea _ _ lit64_47, Int64.lt_iff_toInt_lt, eb, lit64_0]
  split
  · rename_i h
    simp only
    rw [floorDiv64_toInt _ _ (by rw [eb]; exact h.1), toInt_shl16 _ (by rw [ea]; exact h.2), ea, eb]
  · rfl

theorem lerp_eq (x0 x1 y0 y1 x : Int) (h1 : InI64 (y1 - y0)) (h2 : InI64 (x - x0)) (h3 : InI64 (x1 - x0))
    (h4 : InI64 ((y1 - y0) * (x - x0))) :
    lerp x0 x1 y0 y1 x = y0 + (if 0 < x1 - x0 then (y1 - y0) * (x - x0) / (x1 - x0) else 0) := by
  unfold lerp
  split
  · rename_i h
    rw [floorDiv64_toInt _ _ (by rw [toInt_ofInt_of h3]; exact h), Int64.toInt_mul, toInt_ofInt_of h1,
      toInt_ofInt_of h2, toInt_ofInt_of h3, bmod64_of h4]
  · rfl


theorem amgm (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  have : ((a : Int) - b) * ((a : Int) - b) ≥ 0 := by
    by_cases hab : (b : Int) ≤ a
    · exact Int.mul_nonneg (by omega) (by omega)
    · have : ((a : Int) - b) * ((a : Int) - b) = ((b : Int) - a) * ((b : Int) - a) := by grind
      rw [this]; exact Int.mul_nonneg (by omega) (by omega)
  have h : ((a + b) * (a + b) : Int) - 4 * (a * b) = ((a : Int) - b) * ((a : Int) - b) := by grind
  have : (4 * (a * b) : Int) ≤ (a + b) * (a + b) := by omega
  exact_mod_cast this

theorem isqrtAux_eq (n s : Nat) (hs1 : s * s ≤ n) (hs2 : n < (s + 1) * (s + 1)) :
    ∀ (f x : Nat), s ≤ x → x - s < 2 ^ f → isqrtAux n f x = s := by
  intro f
  induction f with
  | zero => intro x h1 h3; simp at h3; simp [isqrtAux]; omega
  | succ f ih =>
    intro x h1 h3
    simp only [isqrtAux]
    by_cases x0 : x = 0
    · subst x0; simp; omega
    have h2 : 0 < x := by omega
    by_cases hx : x = s
    · subst hx
      have : x ≤ n / x := (Nat.le_div_iff_mul_le h2).mpr hs1
      have : ¬ ((x + n / x) / 2 < x) := by omega
      simp [this]
    · have hgt : s < x := by omega
      have hq : n / x ≤ s := by
        have : n < (s + 1) * x := Nat.lt_of_lt_of_le hs2 (Nat.mul_le_mul_left _ hgt)
        have := (Nat.div_lt_iff_lt_mul h2).mpr this
        omega
      have hy : s ≤ (x + n / x) / 2 := by
        apply Nat.le_div_iff_mul_le (by decide) |>.mpr
        apply Nat.le_of_not_lt
        intro hlt
        have h4 := amgm (n / x + 1) x
        have h5 : n < (n / x + 1) * x := by
          have := Nat.lt_mul_div_succ n h2; rw [Nat.mul_comm] at this; exact this
        have h6 : (n / x + 1 + x) * (n / x + 1 + x) ≤ (2 * s) * (2 * s) := Nat.mul_self_le_mul_self (by omega)
        have : 4 * ((n / x + 1) * x) ≤ 4 * (s * s) := by
          have := Nat.le_trans h4 h6
          rw [show 2 * s * (2 * s) = 4 * (s * s) by grind] at this
          exact this
        omega
      have hlt : (x + n / x) / 2 < x := by omega
      simp only [hlt, ite_true]
      apply ih _ hy
      have : (x + n / x) / 2 - s ≤ (x - s) / 2 := by omega
      rw [Nat.pow_succ] at h3
      omega

theorem isqrt_eq_sqrt (n : Nat) (hn : n < 2 ^ 126) : isqrt n = n.sqrt := by
  have hs1 := Nat.sqrt_le n
  have hs2 := Nat.lt_succ_sqrt n
  unfold isqrt
  split
  · rename_i h
    unfold Nat.sqrt; simp; omega
  · rename_i h
    have hn0 : n ≠ 0 := by omega
    have L := Nat.lt_log2_self (n := n)
    have L2 : n.log2 < 126 := (Nat.log2_lt hn0).mpr hn
    have hx0 : 1 <<< (n.log2 / 2 + 1) = 2 ^ (n.log2 / 2 + 1) := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hx0]
    have big : n < 2 ^ (n.log2 / 2 + 1) * 2 ^ (n.log2 / 2 + 1) := by
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le L (Nat.pow_le_pow_right (by decide) (by omega))
    have hsx : n.sqrt < 2 ^ (n.log2 / 2 + 1) := by
      apply Nat.lt_of_not_le; intro hle
      have := Nat.mul_self_le_mul_self hle; omega
    have hs1' : 1 ≤ n.sqrt := by
      apply Nat.pos_of_ne_zero; intro h0; rw [h0] at hs2; simp at hs2; omega
    have hx64 : 2 ^ (n.log2 / 2 + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    exact isqrtAux_eq n n.sqrt hs1 (by simpa [Nat.succ_eq_add_one] using hs2) 64 _ (by omega) (by omega)

theorem sqrt_mono {n m : Nat} (h : n ≤ m) : n.sqrt ≤ m.sqrt := by
  apply Nat.le_of_not_lt; intro hlt
  have := Nat.mul_self_le_mul_self (show m.sqrt + 1 ≤ n.sqrt by omega)
  have := Nat.sqrt_le n
  have := Nat.lt_succ_sqrt m
  simp [Nat.succ_eq_add_one] at *; omega

end Jsb
