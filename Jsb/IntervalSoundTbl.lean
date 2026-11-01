import Jsb.IntervalSoundBase

/-! Soundness of the interval table lookups, atmosphere lookup and attitude renormalisation. -/

namespace Jsb
open Vibecheck

namespace Iv
variable {x y : Fx} {I J : Iv}

theorem lerpZ_y_mono {x0 x1 p y0 r y1 x : Int} (ht : 0 ≤ x - x0 ∧ x - x0 ≤ x1 - x0) (hp : p ≤ y0) (hr : r ≤ y1) :
    lerpZ x0 x1 p r x ≤ lerpZ x0 x1 y0 y1 x := by
  unfold lerpZ
  split
  · rename_i hd
    have e (a b : Int) : a + (b - a) * (x - x0) / (x1 - x0) = (a * ((x1 - x0) - (x - x0)) + b * (x - x0)) / (x1 - x0) := by
      have : a * ((x1 - x0) - (x - x0)) + b * (x - x0) = (b - a) * (x - x0) + (x1 - x0) * a := by
        simp only [Int.mul_sub, Int.sub_mul]; grind
      rw [this, Int.add_mul_ediv_left _ _ (by omega)]; omega
    rw [e, e]
    apply Int.ediv_le_ediv hd
    have := Int.mul_le_mul_of_nonneg_right hp (show 0 ≤ (x1 - x0) - (x - x0) by omega)
    have := Int.mul_le_mul_of_nonneg_right hr ht.1
    omega
  · omega

theorem lerpZ_x_range {x0 x1 y0 y1 xa xb x : Int} (_h0 : x0 ≤ xa) (h1 : xa ≤ x) (h2 : x ≤ xb) :
    Min.min (lerpZ x0 x1 y0 y1 xa) (lerpZ x0 x1 y0 y1 xb) ≤ lerpZ x0 x1 y0 y1 x ∧
    lerpZ x0 x1 y0 y1 x ≤ Max.max (lerpZ x0 x1 y0 y1 xa) (lerpZ x0 x1 y0 y1 xb) := by
  unfold lerpZ
  split
  · rename_i hd
    by_cases hy : 0 ≤ y1 - y0
    · have a1 := Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonneg_left (show xa - x0 ≤ x - x0 by omega) hy)
      have a2 := Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonneg_left (show x - x0 ≤ xb - x0 by omega) hy)
      omega
    · have a1 := Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonpos_left (show y1 - y0 ≤ 0 by omega) (show xa - x0 ≤ x - x0 by omega))
      have a2 := Int.ediv_le_ediv hd (Int.mul_le_mul_of_nonpos_left (show y1 - y0 ≤ 0 by omega) (show x - x0 ≤ xb - x0 by omega))
      omega
  · omega

theorem prod_abs_le {a b D E : Int} (ha : -D ≤ a ∧ a ≤ D) (hb : 0 ≤ b ∧ b ≤ E) : -(D * E) ≤ a * b ∧ a * b ≤ D * E := by
  have hD : 0 ≤ D := by omega
  have h1 := Int.mul_le_mul_of_nonneg_right ha.2 hb.1
  have h2 := Int.mul_le_mul_of_nonneg_right ha.1 hb.1
  have h3 := Int.mul_le_mul_of_nonneg_left hb.2 hD
  rw [Int.neg_mul] at h2
  omega

theorem lerpI_sound {x0 x1 p P r R xa xb y0 y1 x u v : Int} (h : lerpI x0 x1 p P r R xa xb = some (u, v))
    (hy0 : p ≤ y0 ∧ y0 ≤ P) (hy1 : r ≤ y1 ∧ y1 ≤ R) (hx : x0 ≤ xa ∧ xa ≤ x ∧ x ≤ xb ∧ xb ≤ x1) :
    u ≤ lerp x0 x1 y0 y1 x ∧ lerp x0 x1 y0 y1 x ≤ v := by
  unfold lerpI at h; simp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold B62 at hc
    have pb := prod_abs_le (a := y1 - y0) (b := x - x0) (D := Max.max (R - p) (P - r)) (E := x1 - x0)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    rw [lerp_eq _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
    have m1 := lerpZ_y_mono (x0 := x0) (x1 := x1) (x := x) ⟨by omega, by omega⟩ hy0.1 hy1.1
    have m2 := lerpZ_y_mono (x0 := x0) (x1 := x1) (x := x) ⟨by omega, by omega⟩ hy0.2 hy1.2
    have r1 := lerpZ_x_range (x0 := x0) (x1 := x1) (y0 := p) (y1 := r) hx.1 hx.2.1 hx.2.2.1
    have r2 := lerpZ_x_range (x0 := x0) (x1 := x1) (y0 := P) (y1 := R) hx.1 hx.2.1 hx.2.2.1
    unfold lerpZ at m1 m2 r1 r2 ⊢
    omega
  · simp at h

theorem segment_spec (xs : Array Int) (x : Int) :
    ∀ (n i : Nat), xs[i]! ≤ x → i + 2 ≤ xs.size → xs.size ≤ n + i + 2 →
      xs[segment xs x n i]! ≤ x ∧ segment xs x n i + 2 ≤ xs.size ∧
      (x < xs[segment xs x n i + 1]! ∨ segment xs x n i + 2 = xs.size) := by
  intro n
  induction n with
  | zero => intro i h1 h2 h3; simp only [segment]; omega
  | succ n ih =>
    intro i h1 h2 h3
    simp only [segment]
    split
    · rename_i h; exact ih (i + 1) h.2 (by omega) (by omega)
    · rename_i h
      refine ⟨h1, h2, ?_⟩
      by_cases hs : i + 2 < xs.size
      · left; have : ¬ xs[i + 1]! ≤ x := fun hh => h ⟨hs, hh⟩
        omega
      · right; omega

def AccHas (o : Option (Int × Int)) (V : Int) : Prop := ∃ a b, o = some (a, b) ∧ a ≤ V ∧ V ≤ b

theorem acc_keep {o : Option (Int × Int)} {V lo hi : Int} (h : AccHas o V) : AccHas (acc o lo hi) V := by
  obtain ⟨a, b, rfl, h1, h2⟩ := h
  exact ⟨_, _, rfl, by omega, by omega⟩

theorem acc_new (o : Option (Int × Int)) {V lo hi : Int} (h1 : lo ≤ V) (h2 : V ≤ hi) : AccHas (acc o lo hi) V := by
  cases o with
  | none => exact ⟨_, _, rfl, h1, h2⟩
  | some ab => obtain ⟨a, b⟩ := ab; exact ⟨_, _, rfl, by omega, by omega⟩

theorem ofAcc_mem {o : Option (Int × Int)} {V : Int} (h : AccHas o V) : (ofAcc (some o)).Mem ⟨V⟩ := by
  obtain ⟨a, b, rfl, h1, h2⟩ := h
  exact ⟨h1, h2⟩

/-- Segment `j` of a `segsI` run encloses `V` (whenever it meets the query range). -/
def SegHas (xs : Array Int) (val : Nat → Option (Int × Int × Int × Int)) (lo hi : Int) (j : Nat) (V : Int) : Prop :=
  ∀ p P r R u v, val j = some (p, P, r, R) →
    lerpI xs[j]! xs[j + 1]! p P r R (Max.max lo xs[j]!) (Min.min hi xs[j + 1]!) = some (u, v) → u ≤ V ∧ V ≤ v

theorem segsI_sound (xs : Array Int) (val : Nat → Option (Int × Int × Int × Int)) (lo hi V : Int) :
    ∀ (n i : Nat) (o o' : Option (Int × Int)), segsI xs val lo hi n i o = some o' →
      (AccHas o V → AccHas o' V) ∧
      (∀ j, i ≤ j → j < i + n → Max.max lo xs[j]! ≤ Min.min hi xs[j + 1]! → SegHas xs val lo hi j V → AccHas o' V) := by
  intro n
  induction n with
  | zero =>
    intro i o o' h
    simp only [segsI, Option.some.injEq] at h; subst h
    exact ⟨id, fun j h1 h2 => by omega⟩
  | succ n ih =>
    intro i o o' h
    simp only [segsI] at h
    split at h
    · rename_i hab
      split at h
      · rename_i p P r R hv
        split at h
        · rename_i u v hl
          have := ih (i + 1) _ _ h
          refine ⟨fun hh => this.1 (acc_keep hh), ?_⟩
          intro j h1 h2 h3 h4
          by_cases hj : j = i
          · subst hj
            have hb := h4 p P r R u v hv hl
            exact this.1 (acc_new _ hb.1 hb.2)
          · exact this.2 j (by omega) (by omega) h3 h4
        · simp at h
      · simp at h
    · have := ih (i + 1) _ _ h
      refine ⟨this.1, ?_⟩
      intro j h1 h2 h3 h4
      by_cases hj : j = i
      · subst hj; omega
      · exact this.2 j (by omega) (by omega) h3 h4

theorem mem_of_acc {o : Option (Int × Int)} {e : Fx} (h : AccHas o e.raw) : (ofAcc (some o)).Mem e := ofAcc_mem h

theorem tbl1_sound (t : Tbl1) (hx : I.Mem x) : (tbl1 t I).Mem (instScalarFx.tbl1 t x) := by
  cases I with
  | top => trivial
  | box lo hi =>
  simp only [mem_box] at hx
  show (tbl1 t (box lo hi)).Mem (Tbl1.eval t x)
  -- the final step of `tbl1`: whatever accumulator reaches `ofAcc` encloses the value
  suffices H : ∀ o' : Option (Int × Int),
      (AccHas (if t.xs[t.xs.size - 1]! ≤ hi then acc (if lo ≤ t.xs[0]! then some (t.ys[0]!, t.ys[0]!) else none)
        t.ys[t.xs.size - 1]! t.ys[t.xs.size - 1]! else (if lo ≤ t.xs[0]! then some (t.ys[0]!, t.ys[0]!) else none))
        (Tbl1.eval t x).raw → AccHas o' (Tbl1.eval t x).raw) →
      (∀ j, 0 ≤ j → j < 0 + (t.xs.size - 1) →
        Max.max (Max.max lo (t.xs[0]! + 1)) t.xs[j]! ≤ Min.min (Min.min hi (t.xs[t.xs.size - 1]! - 1)) t.xs[j + 1]! →
        SegHas t.xs (fun i => some (t.ys[i]!, t.ys[i]!, t.ys[i + 1]!, t.ys[i + 1]!))
          (Max.max lo (t.xs[0]! + 1)) (Min.min hi (t.xs[t.xs.size - 1]! - 1)) j (Tbl1.eval t x).raw →
        AccHas o' (Tbl1.eval t x).raw) → AccHas o' (Tbl1.eval t x).raw by
    simp only [tbl1]
    split
    · split
      · rename_i o' hs
        exact mem_of_acc (H o' (segsI_sound _ _ _ _ _ _ _ _ _ hs).1 (segsI_sound _ _ _ _ _ _ _ _ _ hs).2)
      · trivial
    · exact mem_of_acc (H _ id (fun j _ _ h3 _ => by omega))
  intro o' hk hseg
  by_cases h0 : x.raw ≤ t.xs[0]!
  · have hV : (Tbl1.eval t x).raw = t.ys[0]! := by unfold Tbl1.eval; simp [h0]
    rw [hV] at hk ⊢
    apply hk
    have : AccHas (if lo ≤ t.xs[0]! then some (t.ys[0]!, t.ys[0]!) else none) t.ys[0]! := by
      simp only [show lo ≤ t.xs[0]! by omega, ite_true]; exact ⟨_, _, rfl, by omega, by omega⟩
    split
    · exact acc_keep this
    · exact this
  by_cases h1 : t.xs[t.xs.size - 1]! ≤ x.raw
  · have hV : (Tbl1.eval t x).raw = t.ys[t.xs.size - 1]! := by unfold Tbl1.eval; simp [h0, h1]
    rw [hV] at hk ⊢
    apply hk
    simp only [show t.xs[t.xs.size - 1]! ≤ hi by omega, ite_true]
    exact acc_new _ (by omega) (by omega)
  have hn : 2 ≤ t.xs.size := by
    apply Nat.le_of_not_lt; intro hlt
    have : t.xs.size - 1 = 0 := by omega
    rw [this] at h1; omega
  have sp := segment_spec t.xs x.raw t.xs.size 0 (by omega) hn (by omega)
  have hj1 : x.raw ≤ t.xs[segment t.xs x.raw t.xs.size 0 + 1]! := by
    rcases sp.2.2 with h | h
    · omega
    · rw [show segment t.xs x.raw t.xs.size 0 + 1 = t.xs.size - 1 by omega]; omega
  have hV : (Tbl1.eval t x).raw = lerp t.xs[segment t.xs x.raw t.xs.size 0]! t.xs[segment t.xs x.raw t.xs.size 0 + 1]!
      t.ys[segment t.xs x.raw t.xs.size 0]! t.ys[segment t.xs x.raw t.xs.size 0 + 1]! x.raw := by
    unfold Tbl1.eval; simp [h0, h1]
  rw [hV] at hseg ⊢
  apply hseg (segment t.xs x.raw t.xs.size 0) (by omega) (by omega) (by omega)
  intro p P r R u v hv hl
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
  exact lerpI_sound hl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩

theorem ofAcc_mem' {R : Option (Option (Int × Int))} {e : Fx} (h : ∀ o', R = some o' → AccHas o' e.raw) :
    (ofAcc R).Mem e := by
  cases R with
  | none => trivial
  | some o => exact mem_of_acc (h o rfl)

theorem clamp_mono {a b u v : Int} (h : u ≤ v) : Max.max a (Min.min b u) ≤ Max.max a (Min.min b v) := by omega

/-- The segment of a clamped query contains it. -/
theorem seg_of_clamped (xs : Array Int) (q : Int) (hn : 2 ≤ xs.size) (h0 : xs[0]! ≤ q) (h1 : q ≤ xs[xs.size - 1]!) :
    xs[segment xs q xs.size 0]! ≤ q ∧ q ≤ xs[segment xs q xs.size 0 + 1]! ∧ segment xs q xs.size 0 + 2 ≤ xs.size := by
  have sp := segment_spec xs q xs.size 0 h0 hn (by omega)
  refine ⟨sp.1, ?_, sp.2.1⟩
  rcases sp.2.2 with h | h
  · omega
  · rw [show segment xs q xs.size 0 + 1 = xs.size - 1 by omega]; exact h1

theorem tbl2_sound (t : Tbl2) (hx : I.Mem x) (hy : J.Mem y) : (tbl2 t I J).Mem (instScalarFx.tbl2 t x y) := by
  cases I with
  | top => trivial
  | box rlo rhi =>
  cases J with
  | top => simp only [tbl2]; trivial
  | box clo chi =>
  simp only [mem_box] at hx hy
  show (tbl2 t (box rlo rhi) (box clo chi)).Mem (Tbl2.eval t x y)
  simp only [tbl2]
  split
  · rename_i hc
    obtain ⟨hnr, hnc, hr0, hc0⟩ := hc
    apply ofAcc_mem'
    intro o' hs
    · have hS := (segsI_sound _ _ _ _ (Tbl2.eval t x y).raw _ _ _ _ hs).2
      have rc0 := clamp_mono (a := t.rows[0]!) (b := t.rows[t.rows.size - 1]!) hx.1
      have rc1 := clamp_mono (a := t.rows[0]!) (b := t.rows[t.rows.size - 1]!) hx.2
      have cc0 := clamp_mono (a := t.cols[0]!) (b := t.cols[t.cols.size - 1]!) hy.1
      have cc1 := clamp_mono (a := t.cols[0]!) (b := t.cols[t.cols.size - 1]!) hy.2
      have si := seg_of_clamped t.rows (Max.max t.rows[0]! (Min.min t.rows[t.rows.size - 1]! x.raw)) hnr
        (by omega) (by omega)
      have sj := seg_of_clamped t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) hnc
        (by omega) (by omega)
      -- each interval row encloses the `Fx` column interpolation of that row
      have hrow : ∀ (a : Nat) (p P : Int),
          (segsI t.cols (fun j => some (t.data[a * t.cols.size + j]!, t.data[a * t.cols.size + j]!,
            t.data[a * t.cols.size + j + 1]!, t.data[a * t.cols.size + j + 1]!))
            (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! clo))
            (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! chi)) (t.cols.size - 1) 0 none).bind id
            = some (p, P) →
          p ≤ lerp t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]!
            t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]!
            t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]!
            t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]!
            (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) ∧
          lerp t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]!
            t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]!
            t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]!
            t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]!
            (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) ≤ P := by
        intro a p P hb
        cases hs2 : segsI t.cols _ _ _ (t.cols.size - 1) 0 none with
        | none => rw [hs2] at hb; simp at hb
        | some o2 =>
          rw [hs2] at hb
          simp only [Option.bind_some, id] at hb
          subst hb
          have := (segsI_sound _ _ _ _ (lerp t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]! t.cols[segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]! t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0]! t.data[a * t.cols.size + segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0 + 1]! (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw))) _ _ _ _ hs2).2
            (segment t.cols (Max.max t.cols[0]! (Min.min t.cols[t.cols.size - 1]! y.raw)) t.cols.size 0) (by omega) (by omega) (by omega) (by
            intro p' P' r' R' u v hv hl
            simp only [Option.some.injEq, Prod.mk.injEq] at hv
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
            exact lerpI_sound hl ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩)
          obtain ⟨a', b', hab, h1, h2⟩ := this
          simp only [Option.some.injEq, Prod.mk.injEq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          exact ⟨h1, h2⟩
      apply hS (segment t.rows (Max.max t.rows[0]! (Min.min t.rows[t.rows.size - 1]! x.raw)) t.rows.size 0)
        (by omega) (by omega) (by omega)
      intro p P r R u v hv hl
      simp only [] at hv
      split at hv
      · rename_i p1 P1 r1 R1 e1 e2
        simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
        have b1 := hrow _ _ _ e1
        have b2 := hrow _ _ _ e2
        unfold Tbl2.eval
        simp only [← Nat.add_assoc]
        exact lerpI_sound hl ⟨b1.1, b1.2⟩ ⟨b2.1, b2.2⟩ ⟨by omega, by omega, by omega, by omega⟩
      · simp at hv
  · trivial

def CellHas (tab : Array Int) (lo hi : Int) (j : Nat) (V : Int) : Prop :=
  ∀ u v, lerpI 0 (50 * 65536) tab[j]! tab[j]! tab[j + 1]! tab[j + 1]! (Max.max 0 (Min.min (50 * 65536) (lo - j * (50 * 65536))))
    (Max.max 0 (Min.min (50 * 65536) (hi - j * (50 * 65536)))) = some (u, v) → u ≤ V ∧ V ≤ v

theorem atmCells_sound (tab : Array Int) (lo hi V : Int) :
    ∀ (n i : Nat) (o o' : Option (Int × Int)), atmCells tab lo hi n i o = some o' →
      (AccHas o V → AccHas o' V) ∧ (∀ j, i ≤ j → j < i + n → CellHas tab lo hi j V → AccHas o' V) := by
  intro n
  induction n with
  | zero =>
    intro i o o' h
    simp only [atmCells, Option.some.injEq] at h; subst h
    exact ⟨id, fun j h1 h2 => by omega⟩
  | succ n ih =>
    intro i o o' h
    simp only [atmCells] at h
    split at h
    · rename_i u v hl
      have := ih (i + 1) _ _ h
      refine ⟨fun hh => this.1 (acc_keep hh), ?_⟩
      intro j h1 h2 h4
      by_cases hj : j = i
      · subst hj
        have hb := h4 u v hl
        exact this.1 (acc_new _ hb.1 hb.2)
      · exact this.2 j (by omega) (by omega) h4
    · simp at h

theorem atm_sound (t : Array Int) (hx : I.Mem x) : (atm t I).Mem (instScalarFx.atm t x) := by
  cases I with
  | top => trivial
  | box lo hi =>
  simp only [mem_box] at hx
  show (atm t (box lo hi)).Mem (atmLookup t x)
  simp only [atm]
  simp only [show lo ≤ hi by omega, ite_true]
  apply ofAcc_mem'
  intro o' hs
  have hS := (atmCells_sound t lo hi (atmLookup t x).raw _ _ _ _ hs).2
  have hc : InI64 (Max.max 0 (Min.min (50 * 65536 * 159) x.raw)) := ⟨by omega, by omega⟩
  have fd := floorDiv_eq _ (50 * 65536) hc ⟨by omega, by omega⟩ (by omega)
  have m1 : Max.max 0 (Min.min (50 * 65536 * 159) lo) / (50 * 65536) ≤ Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536) :=
    Int.ediv_le_ediv (by omega) (by omega)
  have m2 : Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536) ≤ Max.max 0 (Min.min (50 * 65536 * 159) hi) / (50 * 65536) :=
    Int.ediv_le_ediv (by omega) (by omega)
  have n0 : 0 ≤ Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536) := Int.ediv_nonneg (by omega) (by omega)
  have n1 : 0 ≤ Max.max 0 (Min.min (50 * 65536 * 159) lo) / (50 * 65536) := Int.ediv_nonneg (by omega) (by omega)
  have key : (atmLookup t x).raw = lerp 0 (50 * 65536) t[(Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat]!
      t[(Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat + 1]!
      (Max.max 0 (Min.min (50 * 65536) (x.raw - ((Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat : Int) * (50 * 65536)))) := by
    unfold atmLookup lerp
    simp only [Int.sub_zero, show (0 : Int) < 50 * 65536 by decide, ite_true]
    rw [show (50 * 65536 : Int) * 159 = 50 * 65536 * 159 by rfl, fd]
  rw [key] at hS ⊢
  apply hS ((Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat) (by omega) (by omega)
  intro u v hl
  have := lerpI_sound hl (y0 := t[(Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat]!)
    (y1 := t[(Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat + 1]!)
    (x := Max.max 0 (Min.min (50 * 65536) (x.raw - ((Max.max 0 (Min.min (50 * 65536 * 159) x.raw) / (50 * 65536)).toNat : Int) * (50 * 65536))))
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
  exact this

theorem hullPieces_sound (f : Iv → Iv) (t : Nat → Int) (x : Fx) (V : Fx)
    (hf : ∀ a b, a ≤ x.raw → x.raw ≤ b → (f (box a b)).Mem V) :
    ∀ m, 1 ≤ m → t 0 ≤ x.raw → x.raw ≤ t m → (hullPieces f t m).Mem V := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ h0 h1
    match m, ih with
    | 0, _ => exact hf _ _ h0 h1
    | m + 1, ih =>
      simp only [hullPieces]
      by_cases hx : x.raw ≤ t (m + 1)
      · exact hull_left (ih (by omega) h0 hx)
      · exact hull_right (hf _ _ (by omega) h1)

theorem splitMap_sound (f : Iv → Iv) {x : Fx} {V : Fx} (hI : I.Mem x)
    (hf : ∀ C, C.Mem x → (f C).Mem V) : (splitMap f I).Mem V := by
  cases I with
  | top => exact hf top trivial
  | box a b =>
    simp only [mem_box] at hI
    simp only [splitMap, rnSplit]
    apply hullPieces_sound f _ x V (fun a' b' h1 h2 => hf _ ⟨h1, h2⟩) 8 (by decide)
    · simp; omega
    · simp; omega

theorem rnPiece_sound {C J : Iv} {c s : Fx} (hc : C.Mem c) (hs : J.Mem s) :
    (mulR C (rnFactorI C J)).Mem (instScalarFx.rnC c s) :=
  mulR_sound hc (sub_sound (div_sound (lit_sound _) (lit_sound _))
    (div_sound (add_sound (mul_sound hc hc) (mul_sound hs hs)) (lit_sound _)))

theorem rnPieceS_sound {C J : Iv} {c s : Fx} (hc : C.Mem c) (hs : J.Mem s) :
    (mulR J (rnFactorI C J)).Mem (instScalarFx.rnS c s) :=
  mulR_sound hs (sub_sound (div_sound (lit_sound _) (lit_sound _))
    (div_sound (add_sound (mul_sound hc hc) (mul_sound hs hs)) (lit_sound _)))

theorem rnC_sound (hx : I.Mem x) (hy : J.Mem y) : (rnC I J).Mem (instScalarFx.rnC x y) :=
  splitMap_sound _ hx (fun _ hC => rnPiece_sound hC hy)

theorem rnS_sound (hx : I.Mem x) (hy : J.Mem y) : (rnS I J).Mem (instScalarFx.rnS x y) :=
  splitMap_sound _ hx (fun _ hC => rnPieceS_sound hC hy)

end Iv
end Jsb
