import Spec.EndSets

/-! # End sets: decidable sufficient conditions for `Helix.Geo` and `Ray.Geo` on a concrete map, exact in `Rat`. -/

namespace CitySafety.EndSets
open CitySafety

/-! ## Terrain, one grid square at a time -/

/-- The unclamped grid square of coordinate `x` along an axis: `⌊(x + half) / spacing⌋`. -/
def cellOf (M : CityMap) (x : Rat) : Int := ((x + M.half) / M.spacing).floor

/-- The grid square `CityMap.terrain` reads for unclamped square `k`: `k` clamped to `[0, n - 2]`. -/
def clampIdx (M : CityMap) (k : Int) : Nat := min k.toNat (M.n - 2)

/-- West (or south) edge of unclamped square `k` (m). -/
def edge (M : CityMap) (k : Int) : Rat := -M.half + (k : Rat) * M.spacing

/-- The highest of the four vertex heights of grid square `(i, j)`. -/
def sqMax (M : CityMap) (i j : Nat) : Rat :=
  max (max (M.height i j) (M.height (i + 1) j)) (max (M.height i (j + 1)) (M.height (i + 1) (j + 1)))

theorem clampR_eq_zero {N f : Rat} (hN : 0 ≤ N) (h : f ≤ 0) : clampR 0 N f = 0 := by
  simp only [clampR]; grind

theorem natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  have := Rat.natCast_le_natCast.mpr (Nat.zero_le n); simpa using this

theorem floor_zero : (0 : Rat).floor = 0 := by decide

theorem idx_eq (n : Nat) (f : Rat) :
    min (clampR 0 ((n - 1 : Nat) : Rat) f).floor.toNat (n - 2) = min f.floor.toNat (n - 2) := by
  have hN := natCast_nonneg (n - 1)
  by_cases h0 : f ≤ 0
  · rw [clampR_eq_zero hN h0, floor_zero]
    have hf : f.floor ≤ 0 := by have := Rat.floor_monotone h0; rwa [floor_zero] at this
    omega
  · by_cases h1 : ((n - 1 : Nat) : Rat) ≤ f
    · have hc : clampR 0 ((n - 1 : Nat) : Rat) f = (((n - 1 : Nat) : Int) : Rat) := by
        simp only [clampR, Rat.intCast_natCast]; grind
      have hfl : ((n - 1 : Nat) : Int) ≤ f.floor := Rat.le_floor_iff.mpr (by rwa [Rat.intCast_natCast])
      rw [hc, Rat.floor_intCast]
      omega
    · have hc : clampR 0 ((n - 1 : Nat) : Rat) f = f := by simp only [clampR]; grind
      rw [hc]

theorem frac_bounds {n : Nat} (hn : 2 ≤ n) (f : Rat) :
    0 ≤ clampR 0 ((n - 1 : Nat) : Rat) f - ((min (clampR 0 ((n - 1 : Nat) : Rat) f).floor.toNat (n - 2) : Nat) : Rat) ∧
    clampR 0 ((n - 1 : Nat) : Rat) f - ((min (clampR 0 ((n - 1 : Nat) : Rat) f).floor.toNat (n - 2) : Nat) : Rat) ≤ 1 := by
  generalize hfx : clampR 0 ((n - 1 : Nat) : Rat) f = fx
  have hN := natCast_nonneg (n - 1)
  have hlo : 0 ≤ fx := by rw [← hfx]; simp only [clampR]; grind
  have hhi : fx ≤ ((n - 1 : Nat) : Rat) := by rw [← hfx]; simp only [clampR]; grind
  have hfl0 : (0 : Int) ≤ fx.floor := Rat.le_floor_iff.mpr (by simpa using hlo)
  have hfl := Rat.floor_le fx
  have hlt := Rat.lt_floor_add_one fx
  have hcast : ((fx.floor.toNat : Nat) : Rat) = ((fx.floor : Int) : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hfl0]
  have hmin : ((min fx.floor.toNat (n - 2) : Nat) : Rat) ≤ ((fx.floor.toNat : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr (Nat.min_le_left _ _)
  constructor
  · grind
  · by_cases hc : fx.floor.toNat ≤ n - 2
    · rw [Nat.min_eq_left hc, hcast]
      simp only [Rat.intCast_add] at hlt
      grind
    · rw [Nat.min_eq_right (by omega)]
      have : ((n - 1 : Nat) : Rat) = ((n - 2 : Nat) : Rat) + 1 := by
        rw [show n - 1 = (n - 2) + 1 by omega]; simp [Rat.natCast_add]
      grind

theorem interp_le {h00 h10 h01 h11 u v H : Rat} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (a : h00 ≤ H) (b : h10 ≤ H) (c : h01 ≤ H) (d : h11 ≤ H) :
    (if v ≤ u then h00 + u * (h10 - h00) + v * (h11 - h10) else h00 + v * (h01 - h00) + u * (h11 - h01)) ≤ H := by
  split
  · have e1 := Rat.mul_le_mul_of_nonneg_left a (show 0 ≤ 1 - u by grind)
    have e2 := Rat.mul_le_mul_of_nonneg_left b (show 0 ≤ u - v by grind)
    have e3 := Rat.mul_le_mul_of_nonneg_left d hv0
    grind
  · have e1 := Rat.mul_le_mul_of_nonneg_left a (show 0 ≤ 1 - v by grind)
    have e2 := Rat.mul_le_mul_of_nonneg_left c (show 0 ≤ v - u by grind)
    have e3 := Rat.mul_le_mul_of_nonneg_left d hu0
    grind

theorem terrain_le_sqMax {M : CityMap} (hn : 2 ≤ M.n) (x y : Rat) :
    M.terrain x y ≤ sqMax M (clampIdx M (cellOf M x)) (clampIdx M (cellOf M y)) := by
  have hi := idx_eq M.n ((x + M.half) / M.spacing)
  have hj := idx_eq M.n ((y + M.half) / M.spacing)
  have fu := frac_bounds hn ((x + M.half) / M.spacing)
  have fv := frac_bounds hn ((y + M.half) / M.spacing)
  simp only [CityMap.terrain, clampIdx, cellOf]
  rw [← hi, ← hj]
  generalize clampR 0 ((M.n - 1 : Nat) : Rat) ((x + M.half) / M.spacing) = fx at fu ⊢
  generalize clampR 0 ((M.n - 1 : Nat) : Rat) ((y + M.half) / M.spacing) = fy at fv ⊢
  generalize min fx.floor.toNat (M.n - 2) = i at fu ⊢
  generalize min fy.floor.toNat (M.n - 2) = j at fv ⊢
  exact interp_le fu.1 fu.2 fv.1 fv.2 (by simp only [sqMax]; grind) (by simp only [sqMax]; grind)
    (by simp only [sqMax]; grind) (by simp only [sqMax]; grind)

theorem div_mul_cancel' {a s : Rat} (hs : 0 < s) : a / s * s = a := Rat.div_mul_cancel (by grind)

theorem div_le_div_right' {a b s : Rat} (hs : 0 < s) (h : a ≤ b) : a / s ≤ b / s := by
  apply Rat.le_of_mul_le_mul_right _ hs
  rw [div_mul_cancel' hs, div_mul_cancel' hs]; exact h

theorem edge_le {M : CityMap} (hs : 0 < M.spacing) (x : Rat) : edge M (cellOf M x) ≤ x := by
  have h := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le ((x + M.half) / M.spacing)) (Rat.le_of_lt hs)
  rw [div_mul_cancel' hs] at h
  simp only [edge, cellOf]; grind

theorem le_edge_succ {M : CityMap} (hs : 0 < M.spacing) (x : Rat) : x ≤ edge M (cellOf M x + 1) := by
  have h := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (Rat.lt_floor_add_one ((x + M.half) / M.spacing)))
    (Rat.le_of_lt hs)
  rw [div_mul_cancel' hs] at h
  simp only [edge, cellOf]; grind

theorem cellOf_mono {M : CityMap} (hs : 0 < M.spacing) {x y : Rat} (h : x ≤ y) : cellOf M x ≤ cellOf M y :=
  Rat.floor_monotone (div_le_div_right' hs (by grind))

/-- The integers `lo, lo + 1, …, hi`. -/
def intRange (lo hi : Int) : List Int := (List.range (hi - lo + 1).toNat).map fun (m : Nat) => lo + (m : Int)

theorem mem_intRange {lo hi k : Int} (h1 : lo ≤ k) (h2 : k ≤ hi) : k ∈ intRange lo hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  exact ⟨(k - lo).toNat, by omega, by omega⟩

/-- Every unclamped grid square meeting `[x0, x1] × [y0, y1]` satisfies `P`. -/
def allSquares (M : CityMap) (x0 x1 y0 y1 : Rat) (P : Int → Int → Bool) : Bool :=
  (intRange (cellOf M x0) (cellOf M x1)).all fun kx => (intRange (cellOf M y0) (cellOf M y1)).all fun ky => P kx ky

theorem allSquares_at {M : CityMap} (hs : 0 < M.spacing) {x0 x1 y0 y1 : Rat} {P : Int → Int → Bool}
    (h : allSquares M x0 x1 y0 y1 P = true) {x y : Rat} (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    P (cellOf M x) (cellOf M y) = true := by
  simp only [allSquares, List.all_eq_true] at h
  exact h _ (mem_intRange (cellOf_mono hs hx0) (cellOf_mono hs hx1)) _
    (mem_intRange (cellOf_mono hs hy0) (cellOf_mono hs hy1))

/-! ## Rectangles against an annulus -/

/-- Squared distance from `c` to the nearest point of `[x0, x1]`. -/
def gap2 (c x0 x1 : Rat) : Rat := if c < x0 then (x0 - c) * (x0 - c) else if x1 < c then (c - x1) * (c - x1) else 0

/-- Squared distance from `c` to the farthest point of `[x0, x1]`. -/
def far2 (c x0 x1 : Rat) : Rat := max ((x0 - c) * (x0 - c)) ((x1 - c) * (x1 - c))

theorem gap2_le {c x0 x1 x : Rat} (h0 : x0 ≤ x) (h1 : x ≤ x1) : gap2 c x0 x1 ≤ (x - c) * (x - c) := by
  unfold gap2
  split
  · exact sq_le_sq (by grind) (by grind)
  · split
    · have := sq_le_sq (show 0 ≤ c - x1 by grind) (show c - x1 ≤ c - x by grind)
      have e : (c - x) * (c - x) = (x - c) * (x - c) := by grind
      grind
    · exact sq_nonneg _

theorem le_far2 {c x0 x1 x : Rat} (h0 : x0 ≤ x) (h1 : x ≤ x1) : (x - c) * (x - c) ≤ far2 c x0 x1 := by
  unfold far2
  rcases (Rat.le_total : c ≤ x ∨ x ≤ c) with h | h
  · have := sq_le_sq (show 0 ≤ x - c by grind) (show x - c ≤ x1 - c by grind); grind
  · have := sq_le_sq (show 0 ≤ c - x by grind) (show c - x ≤ c - x0 by grind)
    have e1 : (c - x) * (c - x) = (x - c) * (x - c) := by grind
    have e2 : (c - x0) * (c - x0) = (x0 - c) * (x0 - c) := by grind
    grind

/-- The rectangle `[x0, x1] × [y0, y1]` misses the annulus `InAnnulus cx cy lo hi`. -/
def offAnnulus (cx cy lo hi x0 x1 y0 y1 : Rat) : Bool :=
  decide (hi * hi < gap2 cx x0 x1 + gap2 cy y0 y1) || decide (0 < lo ∧ far2 cx x0 x1 + far2 cy y0 y1 < lo * lo)

theorem not_inAnnulus {cx cy lo hi x0 x1 y0 y1 : Rat} (h : offAnnulus cx cy lo hi x0 x1 y0 y1 = true) {q : Pt}
    (hx0 : x0 ≤ q.x) (hx1 : q.x ≤ x1) (hy0 : y0 ≤ q.y) (hy1 : q.y ≤ y1) : ¬ InAnnulus cx cy lo hi q := by
  rintro ⟨ha1, ha2⟩
  have g1 := gap2_le (c := cx) hx0 hx1
  have g2 := gap2_le (c := cy) hy0 hy1
  have f1 := le_far2 (c := cx) hx0 hx1
  have f2 := le_far2 (c := cy) hy0 hy1
  simp only [offAnnulus, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [dist2] at ha1 ha2
  grind

/-! ## The helix check -/

/-- **Helix `Geo`, decided**: every building either tops out below `z0 - e` or misses the widened annulus, and so
does every grid square (clamped beyond the edge) within its bounding square. -/
def Helix.geoB (M : CityMap) (H : Helix) (e e' : Rat) : Bool :=
  let lo := H.r - H.δ - e'
  let hi := H.r + H.δ + e'
  let zf := H.z0 - e
  decide (2 ≤ M.n) && decide (0 < M.spacing) && decide (0 ≤ hi) &&
  M.boxes.all (fun b => decide (b.z1 < zf) || offAnnulus H.cx H.cy lo hi b.x0 b.x1 b.y0 b.y1) &&
  allSquares M (H.cx - hi) (H.cx + hi) (H.cy - hi) (H.cy + hi) fun kx ky =>
    decide (sqMax M (clampIdx M kx) (clampIdx M ky) < zf) ||
    offAnnulus H.cx H.cy lo hi (edge M kx) (edge M (kx + 1)) (edge M ky) (edge M (ky + 1))

theorem Helix.geo_of_geoB {M : CityMap} {H : Helix} {e e' : Rat} (h : H.geoB M e e' = true) : H.Geo M e e' := by
  simp only [Helix.geoB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hs⟩, hhi⟩, hb⟩, hsq⟩ := h
  intro q hsol ha
  rcases hsol with ht | ⟨b, hbm, hc⟩
  · have hxy := ha.2
    simp only [dist2] at hxy
    have s1 := sq_nonneg (q.x - H.cx)
    have s2 := sq_nonneg (q.y - H.cy)
    have bx := abs_le_of_sq_le hhi (show (q.x - H.cx) * (q.x - H.cx) ≤ _ by grind)
    have by' := abs_le_of_sq_le hhi (show (q.y - H.cy) * (q.y - H.cy) ≤ _ by grind)
    have hc := allSquares_at hs hsq (x := q.x) (y := q.y) (by grind) (by grind) (by grind) (by grind)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · have := terrain_le_sqMax hn q.x q.y; grind
    · exact absurd ha (not_inAnnulus hc (edge_le hs _) (le_edge_succ hs _) (edge_le hs _) (le_edge_succ hs _))
  · simp only [Box.Contains] at hc
    rcases hb b hbm with hb | hb
    · grind
    · exact absurd ha (not_inAnnulus hb (by grind) (by grind) (by grind) (by grind))

end CitySafety.EndSets
