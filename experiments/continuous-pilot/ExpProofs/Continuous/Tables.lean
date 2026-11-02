import ExpProofs.Continuous.RealModel

/-! Facts about the real piecewise-linear interpolant `pl`: constant beyond the knots, monotone where the
segments it crosses rise, and the c172p table values the vertical-acceleration bound uses. -/

namespace ExpJsb.Cont
open ExpJsb.C172

theorem clamp_mono {x0 x1 x y : ℝ} (h : x ≤ y) : max x0 (min x x1) ≤ max x0 (min y x1) :=
  max_le_max le_rfl (min_le_min h le_rfl)

/-- Every segment either rises or does not meet the open interval `(a, b)`. -/
def SegOK (a b : ℝ) : List ℝ → List ℝ → Prop
  | x0 :: x1 :: xs, y0 :: y1 :: ys => (y0 ≤ y1 ∨ x1 ≤ a ∨ b ≤ x0 ∨ x1 ≤ x0) ∧ SegOK a b (x1 :: xs) (y1 :: ys)
  | _, _ => True

theorem plAux_mono (a b : ℝ) : ∀ (xs ys : List ℝ), SegOK a b xs ys → ∀ x y, a ≤ x → x ≤ y → y ≤ b →
    plAux xs ys x ≤ plAux xs ys y
  | x0 :: x1 :: xs, y0 :: y1 :: ys, ⟨hs, hr⟩, x, y, hax, hxy, hyb => by
    simp only [plAux]
    refine add_le_add ?_ (plAux_mono a b _ _ hr x y hax hxy hyb)
    rcases hs with h | h | h | h
    · rcases le_or_gt x1 x0 with h' | h'
      · have e1 : max x0 (min x x1) = x0 := max_eq_left (le_trans (min_le_right _ _) h')
        have e2 : max x0 (min y x1) = x0 := max_eq_left (le_trans (min_le_right _ _) h')
        rw [e1, e2]
      · exact mul_le_mul_of_nonneg_left (by linarith [clamp_mono (x0 := x0) (x1 := x1) hxy])
          (div_nonneg (by linarith) (by linarith))
    · have e1 : min x x1 = x1 := min_eq_right (by linarith)
      have e2 : min y x1 = x1 := min_eq_right (by linarith)
      rw [e1, e2]
    · have e1 : max x0 (min x x1) = x0 := max_eq_left (le_trans (min_le_left _ _) (by linarith))
      have e2 : max x0 (min y x1) = x0 := max_eq_left (le_trans (min_le_left _ _) (by linarith))
      rw [e1, e2]
    · have e1 : max x0 (min x x1) = x0 := max_eq_left (le_trans (min_le_right _ _) h)
      have e2 : max x0 (min y x1) = x0 := max_eq_left (le_trans (min_le_right _ _) h)
      rw [e1, e2]
  | [], _, _, x, y, _, _, _ => by simp [plAux]
  | [_], _, _, x, y, _, _, _ => by simp [plAux]
  | _ :: _ :: _, [], _, x, y, _, _, _ => by simp [plAux]
  | _ :: _ :: _, [_], _, x, y, _, _, _ => by simp [plAux]

theorem pl_mono {a b : ℝ} {xs ys : List ℝ} (h : SegOK a b xs ys) {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y)
    (hyb : y ≤ b) : pl xs ys x ≤ pl xs ys y := by
  unfold pl; linarith [plAux_mono a b xs ys h x y hax hxy hyb]

/-- `pl` is constant at or above its largest knot. -/
theorem plAux_hi (a : ℝ) : ∀ (xs ys : List ℝ), (∀ z ∈ xs, z ≤ a) → ∀ x, a ≤ x → plAux xs ys x = plAux xs ys a
  | x0 :: x1 :: xs, y0 :: y1 :: ys, h, x, hx => by
    simp only [plAux]
    have h1 : x1 ≤ a := h x1 (by simp)
    rw [min_eq_right (by linarith : x1 ≤ x), min_eq_right h1,
      plAux_hi a (x1 :: xs) (y1 :: ys) (fun z hz => h z (List.mem_cons_of_mem _ hz)) x hx]
  | [], _, _, x, _ => by simp [plAux]
  | [_], _, _, x, _ => by simp [plAux]
  | _ :: _ :: _, [], _, x, _ => by simp [plAux]
  | _ :: _ :: _, [_], _, x, _ => by simp [plAux]

/-- `pl` is constant at or below its smallest knot. -/
theorem plAux_lo (a : ℝ) : ∀ (xs ys : List ℝ), (∀ z ∈ xs, a ≤ z) → ∀ x, x ≤ a → plAux xs ys x = plAux xs ys a
  | x0 :: x1 :: xs, y0 :: y1 :: ys, h, x, hx => by
    simp only [plAux]
    have h0 : a ≤ x0 := h x0 (by simp)
    have e1 : max x0 (min x x1) = x0 := max_eq_left (le_trans (min_le_left _ _) (by linarith))
    have e2 : max x0 (min a x1) = x0 := max_eq_left (le_trans (min_le_left _ _) h0)
    rw [e1, e2, plAux_lo a (x1 :: xs) (y1 :: ys) (fun z hz => h z (List.mem_cons_of_mem _ hz)) x hx]
  | [], _, _, x, _ => by simp [plAux]
  | [_], _, _, x, _ => by simp [plAux]
  | _ :: _ :: _, [], _, x, _ => by simp [plAux]
  | _ :: _ :: _, [_], _, x, _ => by simp [plAux]

theorem pl_hi {xs ys : List ℝ} {a : ℝ} (h : ∀ z ∈ xs, z ≤ a) {x : ℝ} (hx : a ≤ x) : pl xs ys x = pl xs ys a := by
  unfold pl; rw [plAux_hi a xs ys h x hx]

theorem pl_lo {xs ys : List ℝ} {a : ℝ} (h : ∀ z ∈ xs, a ≤ z) {x : ℝ} (hx : x ≤ a) : pl xs ys x = pl xs ys a := by
  unfold pl; rw [plAux_lo a xs ys h x hx]

/-- Simp set that evaluates a concrete table at a numeral. -/
macro "tbl_norm" : tactic => `(tactic| norm_num [pl, plAux, rawList, ofRaw, max_def, min_def, List.range_succ])

-- ground-effect factors are exactly 1 at least 1.1 wing spans up
theorem kCLge_hi {x : ℝ} (hx : 72090 / 65536 ≤ x) : tbl1R tbl_x_2 x = 1 := by
  unfold tbl1R; rw [pl_hi (a := 72090 / 65536) (by simp [rawList, ofRaw, tbl_x_2]; norm_num) hx]
  simp [tbl_x_2]; tbl_norm


theorem kCDge_hi {x : ℝ} (hx : 72090 / 65536 ≤ x) : tbl1R tbl_x_1 x = 1 := by
  unfold tbl1R; rw [pl_hi (a := 72090 / 65536) (by simp [rawList, ofRaw, tbl_x_1]; norm_num) hx]
  simp [tbl_x_1]; tbl_norm

theorem flapCL_zero : tbl1R tbl_x_6 0 = 0 := by unfold tbl1R; simp [tbl_x_6]; tbl_norm
theorem flapCD_zero : tbl1R tbl_x_3 0 = 0 := by unfold tbl1R; simp [tbl_x_3]; tbl_norm

theorem col_x4 : col tbl_x_4 0 = #[269, 85, 7, 20, 131, 341, 649, 1062, 1573, 2189, 2897, 3709, 4627, 5636, 6305,
    7006, 7733, 8507, 9332, 10256, 11318, 11679, 11246, 10604, 9667, 7189] := by decide +kernel
theorem col_x5 : col tbl_x_5 0 = #[-14418, 16384, 47841, 54395, 60293, 66847, 70779, 74056, 77988, 81920, 88474,
    94372, 96338, 93716, 90440, 85197, 75366] := by decide +kernel

theorem tbl2R_x5_col0 (r : ℝ) : tbl2R tbl_x_5 r 0 = pl (rawList tbl_x_5.rows) (rawList (col tbl_x_5 0)) r := by
  have h0 : hat tbl_x_5 0 0 = 1 := by unfold hat; simp [tbl_x_5]; tbl_norm
  have h1 : hat tbl_x_5 1 0 = 0 := by unfold hat; simp [tbl_x_5]; tbl_norm
  have hs : tbl_x_5.cols.size = 2 := rfl
  unfold tbl2R; rw [hs]; simp [List.range_succ, h0, h1]

theorem tbl2R_x4_col0 (r : ℝ) : tbl2R tbl_x_4 r 0 = pl (rawList tbl_x_4.rows) (rawList (col tbl_x_4 0)) r := by
  have h0 : hat tbl_x_4 0 0 = 1 := by unfold hat; simp [tbl_x_4]; tbl_norm
  have h1 : hat tbl_x_4 1 0 = 0 := by unfold hat; simp [tbl_x_4]; tbl_norm
  have h2 : hat tbl_x_4 2 0 = 0 := by unfold hat; simp [tbl_x_4]; tbl_norm
  have h3 : hat tbl_x_4 3 0 = 0 := by unfold hat; simp [tbl_x_4]; tbl_norm
  have hs : tbl_x_4.cols.size = 4 := rfl
  unfold tbl2R; rw [hs]; simp [List.range_succ, h0, h1, h2, h3]

/-- Lift coefficient (no stall, no flap) on [0.1, 0.2] rad is at least its value at 0.1 rad. -/
theorem CL_lower {a : ℝ} (h0 : 0.1 ≤ a) (h1 : a ≤ 0.2) : 54390 / 65536 ≤ tbl2R tbl_x_5 a 0 := by
  rw [tbl2R_x5_col0, col_x5]
  have hok : SegOK 0.1 0.2 (rawList tbl_x_5.rows) (rawList #[-14418, 16384, 47841, 54395, 60293, 66847, 70779,
      74056, 77988, 81920, 88474, 94372, 96338, 93716, 90440, 85197, 75366]) := by
    simp [SegOK, rawList, ofRaw, tbl_x_5]; norm_num
  refine le_trans ?_ (pl_mono hok le_rfl h0 h1)
  simp [tbl_x_5]; tbl_norm

/-- Drag coefficient due to alpha (no flap) on [0.1, 0.2] rad. -/
theorem CD_bounds {a : ℝ} (h0 : 0.1 ≤ a) (h1 : a ≤ 0.2) : 0 ≤ tbl2R tbl_x_4 a 0 ∧ tbl2R tbl_x_4 a 0 ≤ 8100 / 65536 := by
  rw [tbl2R_x4_col0, col_x4]
  have hok : SegOK 0.1 0.2 (rawList tbl_x_4.rows) (rawList #[269, 85, 7, 20, 131, 341, 649, 1062, 1573, 2189, 2897,
      3709, 4627, 5636, 6305, 7006, 7733, 8507, 9332, 10256, 11318, 11679, 11246, 10604, 9667, 7189]) := by
    simp [SegOK, rawList, ofRaw, tbl_x_4]; norm_num
  constructor
  · refine le_trans ?_ (pl_mono hok le_rfl h0 h1); simp [tbl_x_4]; tbl_norm
  · refine le_trans (pl_mono hok h0 h1 le_rfl) ?_; simp [tbl_x_4]; tbl_norm

theorem plAux_neg : ∀ (xs ys : List ℝ) (x : ℝ), plAux xs (ys.map (- ·)) x = - plAux xs ys x
  | x0 :: x1 :: xs, y0 :: y1 :: ys, x => by
    simp only [List.map, plAux]; rw [← List.map, plAux_neg (x1 :: xs) (y1 :: ys) x]; ring
  | [], _, _ => by simp [plAux]
  | [_], _, _ => by simp [plAux]
  | _ :: _ :: _, [], _ => by simp [plAux]
  | _ :: _ :: _, [_], _ => by simp [plAux]

theorem pl_neg (xs ys : List ℝ) (x : ℝ) : pl xs (ys.map (- ·)) x = - pl xs ys x := by
  unfold pl; rw [plAux_neg]; cases ys <;> simp; ring

theorem pl_anti {a b : ℝ} {xs ys : List ℝ} (h : SegOK a b xs (ys.map (- ·))) {x y : ℝ} (hax : a ≤ x)
    (hxy : x ≤ y) (hyb : y ≤ b) : pl xs ys y ≤ pl xs ys x := by
  have := pl_mono h hax hxy hyb; rw [pl_neg, pl_neg] at this; linarith

/-- Propeller thrust coefficient is positive up to advance ratio 1.1. -/
theorem CT_pos {x : ℝ} (h1 : x ≤ 72090 / 65536) : 0 ≤ tbl1R tblCT x := by
  unfold tbl1R
  rcases le_or_gt x 0 with h | h
  · rw [pl_lo (a := 0) (by simp [rawList, ofRaw, tblCT]; norm_num) h]; simp [tblCT]; tbl_norm
  · have hok : SegOK 0 (72090 / 65536) (rawList tblCT.xs) ((rawList tblCT.ys).map (- ·)) := by
      simp [SegOK, rawList, ofRaw, tblCT]; norm_num
    refine le_trans ?_ (pl_anti hok h.le h1 le_rfl); simp [tblCT]; tbl_norm

theorem CTMach_pos (x : ℝ) : 0 ≤ tbl1R tblCTMach x := by
  unfold tbl1R
  have hok : SegOK (55706 / 65536) (68813 / 65536) (rawList tblCTMach.xs) ((rawList tblCTMach.ys).map (- ·)) := by
    simp [SegOK, rawList, ofRaw, tblCTMach]; norm_num
  rcases le_or_gt x (55706 / 65536) with h | h
  · rw [pl_lo (a := 55706 / 65536) (by simp [rawList, ofRaw, tblCTMach]; norm_num) h]; simp [tblCTMach]; tbl_norm
  rcases le_or_gt x (68813 / 65536) with h' | h'
  · refine le_trans ?_ (pl_anti hok h.le h' le_rfl); simp [tblCTMach]; tbl_norm
  · rw [pl_hi (a := 68813 / 65536) (by simp [rawList, ofRaw, tblCTMach]; norm_num) h'.le]; simp [tblCTMach]; tbl_norm

-- the 160-entry atmosphere table unfolds past the default recursion depth
set_option maxRecDepth 20000 in
/-- Air density between 600 m and 1250 m is at least its value at 1250 m. -/
theorem rho_lower {h : ℝ} (h0 : 600 ≤ h) (h1 : h ≤ 1250) : 71083 / 65536 ≤ atmR atmRho h := by
  unfold atmR
  have hok : SegOK 600 1250 ((List.range atmRho.size).map fun i => (50 * i : ℝ)) ((rawList atmRho).map (- ·)) := by
    simp [SegOK, rawList, ofRaw, atmRho, List.range_succ]; norm_num
  refine le_trans ?_ (pl_anti hok h0 h1 le_rfl)
  simp [atmRho]; tbl_norm

end ExpJsb.Cont
