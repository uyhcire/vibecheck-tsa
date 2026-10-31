import Jsb.Interval
import Jsb.MathFacts

namespace Jsb
open Vibecheck

namespace Iv
variable {x y z w : Fx} {I J K L : Iv}

@[simp] theorem mem_top (x : Fx) : top.Mem x := trivial
@[simp] theorem mem_box {lo hi : Int} {x : Fx} : (box lo hi).Mem x ↔ lo ≤ x.raw ∧ x.raw ≤ hi := Iff.rfl

@[simp] theorem raw_add : (instScalarFx.add x y).raw = x.raw + y.raw := rfl
@[simp] theorem raw_sub : (instScalarFx.sub x y).raw = x.raw - y.raw := rfl
@[simp] theorem raw_neg : (instScalarFx.neg x).raw = -x.raw := rfl
@[simp] theorem raw_lit (r : Int) : (instScalarFx.lit r).raw = r := rfl
@[simp] theorem raw_max : (instScalarFx.max x y).raw = Max.max x.raw y.raw := by
  show (if x ≤ y then y else x).raw = _; split <;> simp_all [Fx.le_def] <;> omega
@[simp] theorem raw_min : (instScalarFx.min x y).raw = Min.min x.raw y.raw := by
  show (if x ≤ y then x else y).raw = _; split <;> simp_all [Fx.le_def] <;> omega
@[simp] theorem raw_abs : (instScalarFx.abs x).raw = if x.raw < 0 then -x.raw else x.raw := by
  show (Fx.abs x).raw = _; unfold Fx.abs; split <;> rfl

theorem hull_left (h : I.Mem x) : (hull I J).Mem x := by
  cases I <;> cases J <;> simp_all [hull] <;> omega
theorem hull_right (h : J.Mem x) : (hull I J).Mem x := by
  cases I <;> cases J <;> simp_all [hull] <;> omega

theorem add_sound (hx : I.Mem x) (hy : J.Mem y) : (add I J).Mem (instScalarFx.add x y) := by
  cases I <;> cases J <;> simp_all [add] <;> omega
theorem sub_sound (hx : I.Mem x) (hy : J.Mem y) : (sub I J).Mem (instScalarFx.sub x y) := by
  cases I <;> cases J <;> simp_all [sub] <;> omega
theorem neg_sound (hx : I.Mem x) : (neg I).Mem (instScalarFx.neg x) := by
  cases I <;> simp_all [neg] <;> omega
theorem max_sound (hx : I.Mem x) (hy : J.Mem y) : (max I J).Mem (instScalarFx.max x y) := by
  cases I <;> cases J <;> simp_all [max] <;> omega
theorem min_sound (hx : I.Mem x) (hy : J.Mem y) : (min I J).Mem (instScalarFx.min x y) := by
  cases I <;> cases J <;> simp_all [min] <;> omega
theorem lit_sound (r : Int) : (lit r).Mem (instScalarFx.lit r) := by
  simp [lit]
theorem abs_sound (hx : I.Mem x) : (abs I).Mem (instScalarFx.abs x) := by
  cases I <;> simp only [abs, mem_top] at * <;> (try trivial) <;> split <;> (try split) <;> (try split) <;> simp_all <;> omega
theorem selLt_sound (hx : I.Mem x) (hy : J.Mem y) (hz : K.Mem z) (hw : L.Mem w) :
    (selLt I J K L).Mem (instScalarFx.selLt x y z w) := by
  show (selLt I J K L).Mem (if x.raw < y.raw then z else w)
  cases I <;> cases J <;> simp only [selLt]
  all_goals first
    | (split <;> first | exact hull_left hz | exact hull_right hw)
    | skip
  rename_i a1 a2 b1 b2
  simp at hx hy
  split <;> split <;> (try split) <;> first | assumption | omega | exact hull_left hz | exact hull_right hw
theorem selLe_sound (hx : I.Mem x) (hy : J.Mem y) (hz : K.Mem z) (hw : L.Mem w) :
    (selLe I J K L).Mem (instScalarFx.selLe x y z w) := by
  show (selLe I J K L).Mem (if x.raw ≤ y.raw then z else w)
  cases I <;> cases J <;> simp only [selLe]
  all_goals first
    | (split <;> first | exact hull_left hz | exact hull_right hw)
    | skip
  rename_i a1 a2 b1 b2
  simp at hx hy
  split <;> split <;> (try split) <;> first | assumption | omega | exact hull_left hz | exact hull_right hw

theorem mulRange {x y : Int} (y1 y2 : Int) (hy : y1 ≤ y ∧ y ≤ y2) :
    Min.min (x * y1) (x * y2) ≤ x * y ∧ x * y ≤ Max.max (x * y1) (x * y2) := by
  by_cases h : 0 ≤ x
  · have := Int.mul_le_mul_of_nonneg_left hy.1 h; have := Int.mul_le_mul_of_nonneg_left hy.2 h; omega
  · have := Int.mul_le_mul_of_nonpos_left (show x ≤ 0 by omega) hy.1
    have := Int.mul_le_mul_of_nonpos_left (show x ≤ 0 by omega) hy.2; omega

theorem corners {a b c d x y : Int} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    (prods a b c d).1 ≤ x * y ∧ x * y ≤ (prods a b c d).2 := by
  have h1 := mulRange (x := x) c d hy
  have h2 := mulRange (x := c) a b hx
  have h3 := mulRange (x := d) a b hx
  simp only [prods, min4, max4]
  rw [Int.mul_comm c a, Int.mul_comm c b, Int.mul_comm c x] at h2
  rw [Int.mul_comm d a, Int.mul_comm d b, Int.mul_comm d x] at h3
  omega

theorem in64_of {a b : Int} (h : in64 a b = true) {x : Int} (hx : a ≤ x ∧ x ≤ b) : InI64 x := by
  simp only [in64, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold B63 at h; unfold InI64; omega

theorem mul_sound (hx : I.Mem x) (hy : J.Mem y) : (mul I J).Mem (instScalarFx.mul x y) := by
  cases I <;> cases J <;> simp only [mul] <;> try trivial
  rename_i a b c d
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have h1 := in64_of h.1 hx
    have h2 := in64_of h.2 hy
    have hc := corners hx hy
    show _ ≤ (fmul x y).raw ∧ (fmul x y).raw ≤ _
    rw [fmul_raw x y h1 h2]
    exact ⟨Int.ediv_le_ediv (by decide) hc.1, Int.ediv_le_ediv (by decide) hc.2⟩
  · trivial

theorem mulR_sound (hx : I.Mem x) (hy : J.Mem y) : (mulR I J).Mem (instScalarFx.mulR x y) := by
  cases I <;> cases J <;> simp only [mulR] <;> try trivial
  rename_i a b c d
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have h1 := in64_of h.1 hx
    have h2 := in64_of h.2 hy
    have hc := corners hx hy
    show _ ≤ (Jsb.mulR x y).raw ∧ (Jsb.mulR x y).raw ≤ _
    rw [mulR_raw x y h1 h2]
    exact ⟨Int.ediv_le_ediv (by decide) (by omega), Int.ediv_le_ediv (by decide) (by omega)⟩
  · trivial

theorem ediv_anti_pos {N y d : Int} (hN : 0 ≤ N) (hy : 0 < y) (hyd : y ≤ d) : N / d ≤ N / y := by
  rw [Int.le_ediv_iff_mul_le hy]
  have h0 : 0 ≤ N / d := Int.ediv_nonneg hN (by omega)
  have := Int.mul_le_mul_of_nonneg_left hyd h0
  have := Int.ediv_mul_le N (show d ≠ 0 by omega)
  omega

theorem ediv_mono_neg {N y c : Int} (hN : N < 0) (hc : 0 < c) (hcy : c ≤ y) : N / c ≤ N / y := by
  rw [Int.le_ediv_iff_mul_le (by omega)]
  have h0 : N / c < 0 := (ediv_bounds hc).2 hN |>.2
  have := Int.mul_le_mul_of_nonpos_left (show N / c ≤ 0 by omega) hcy
  have := Int.ediv_mul_le N (show c ≠ 0 by omega)
  omega

theorem div_range {N y c d : Int} (hc : 0 < c) (hy : c ≤ y ∧ y ≤ d) :
    Min.min (N / c) (N / d) ≤ N / y ∧ N / y ≤ Max.max (N / c) (N / d) := by
  by_cases hN : 0 ≤ N
  · have := ediv_anti_pos hN (by omega) hy.2; have := ediv_anti_pos hN hc hy.1; omega
  · have := ediv_mono_neg (show N < 0 by omega) hc hy.1
    have := ediv_mono_neg (show N < 0 by omega) (show 0 < y by omega) hy.2; omega

theorem div_sound (hx : I.Mem x) (hy : J.Mem y) : (div I J).Mem (instScalarFx.div x y) := by
  cases I <;> cases J <;> simp only [div] <;> try trivial
  rename_i a b c d
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 := in64_of h.1.1 hx
    have h2 := in64_of h.1.2 hy
    show _ ≤ (fdiv x y).raw ∧ (fdiv x y).raw ≤ _
    rw [fdiv_raw x y h1 h2]
    simp only [mem_box] at hx hy
    have l1 := div_range (N := a * 65536) h.2 hy
    have l2 := div_range (N := b * 65536) h.2 hy
    have m1 : a * 65536 / y.raw ≤ x.raw * 65536 / y.raw := Int.ediv_le_ediv (by omega) (by omega)
    have m2 : x.raw * 65536 / y.raw ≤ b * 65536 / y.raw := Int.ediv_le_ediv (by omega) (by omega)
    omega
  · trivial

theorem shrZ_mono {a b : Int} (k : Nat) (h : a ≤ b) : shrZ a k ≤ shrZ b k := by
  simp only [shrZ, Int.shiftRight_eq_div_pow]
  exact Int.ediv_le_ediv (by have := Nat.two_pow_pos k; omega) (by omega)

theorem shr_sound (hx : I.Mem x) (k : Nat) : (shr I k).Mem (instScalarFx.shr x k) := by
  cases I <;> simp only [shr] <;> try trivial
  simp only [mem_box] at hx
  exact ⟨shrZ_mono k hx.1, shrZ_mono k hx.2⟩

theorem ab3_sound (hx : I.Mem x) (hy : J.Mem y) (hz : K.Mem z) : (ab3 I J K).Mem (instScalarFx.ab3 x y z) := by
  cases I <;> cases J <;> cases K <;> simp only [ab3] <;> try trivial
  simp only [mem_box] at *
  show _ ≤ (23 * x.raw - 16 * y.raw + 5 * z.raw) / 12 ∧ (23 * x.raw - 16 * y.raw + 5 * z.raw) / 12 ≤ _
  constructor <;> apply Int.ediv_le_ediv (by decide) <;> omega

theorem sqrt_sound (hx : I.Mem x) : (sqrt I).Mem (instScalarFx.sqrt x) := by
  cases I <;> simp only [sqrt] <;> try trivial
  rename_i a b
  split
  · rename_i h
    simp only [mem_box] at hx
    show _ ≤ ((isqrt (x.raw.toNat * 65536) : Nat) : Int) ∧ ((isqrt (x.raw.toNat * 65536) : Nat) : Int) ≤ _
    have t1 : a.toNat ≤ x.raw.toNat := Int.toNat_le_toNat hx.1
    have t2 : x.raw.toNat ≤ b.toNat := Int.toNat_le_toNat hx.2
    have hb : b.toNat * 65536 < 2 ^ 126 := by
      have : b.toNat < 2 ^ 100 := by omega
      omega
    have hx' : x.raw.toNat * 65536 < 2 ^ 126 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ t2) hb
    have ha' : a.toNat * 65536 < 2 ^ 126 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ t1) hx'
    rw [isqrt_eq_sqrt _ ha', isqrt_eq_sqrt _ hx', isqrt_eq_sqrt _ hb]
    exact ⟨by exact_mod_cast sqrt_mono (Nat.mul_le_mul_right _ t1), by exact_mod_cast sqrt_mono (Nat.mul_le_mul_right _ t2)⟩
  · trivial

end Iv
end Jsb
