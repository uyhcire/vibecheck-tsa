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

/-! ## The ray check -/

/-- The least value of `(x - p) a` over `x ∈ [x0, x1]`. -/
def linMin (p a x0 x1 : Rat) : Rat := min ((x0 - p) * a) ((x1 - p) * a)

/-- The greatest value of `(x - p) a` over `x ∈ [x0, x1]`. -/
def linMax (p a x0 x1 : Rat) : Rat := max ((x0 - p) * a) ((x1 - p) * a)

theorem lin_bounds {p a x0 x1 x : Rat} (h0 : x0 ≤ x) (h1 : x ≤ x1) :
    linMin p a x0 x1 ≤ (x - p) * a ∧ (x - p) * a ≤ linMax p a x0 x1 := by
  unfold linMin linMax
  rcases (Rat.le_total : 0 ≤ a ∨ a ≤ 0) with ha | ha
  · have e1 := Rat.mul_le_mul_of_nonneg_right (show x0 - p ≤ x - p by grind) ha
    have e2 := Rat.mul_le_mul_of_nonneg_right (show x - p ≤ x1 - p by grind) ha
    constructor <;> grind
  · have hna : 0 ≤ -a := by grind
    have e1 := Rat.mul_le_mul_of_nonneg_right (show x0 - p ≤ x - p by grind) hna
    have e2 := Rat.mul_le_mul_of_nonneg_right (show x - p ≤ x1 - p by grind) hna
    simp only [Rat.mul_neg] at e1 e2
    constructor <;> grind

/-- The least along-track distance over the rectangle `[x0, x1] × [y0, y1]`. -/
def Ray.alongMin (R : Ray) (x0 x1 y0 y1 : Rat) : Rat := linMin R.px R.a x0 x1 + linMin R.py R.b y0 y1

/-- The greatest along-track distance over the rectangle. -/
def Ray.alongMax (R : Ray) (x0 x1 y0 y1 : Rat) : Rat := linMax R.px R.a x0 x1 + linMax R.py R.b y0 y1

/-- The least lateral offset over the rectangle. -/
def Ray.latMin (R : Ray) (x0 x1 y0 y1 : Rat) : Rat := linMin R.py R.a y0 y1 - linMax R.px R.b x0 x1

/-- The greatest lateral offset over the rectangle. -/
def Ray.latMax (R : Ray) (x0 x1 y0 y1 : Rat) : Rat := linMax R.py R.a y0 y1 - linMin R.px R.b x0 x1

/-- Solids up to `ztop` over the rectangle `[x0, x1] × [y0, y1]` are clear of the corridor short of along-track
distance `T`: the rectangle misses it laterally, lies behind it, lies beyond `T`, or tops out below the floor at
the rectangle's nearest along-track distance. -/
def Ray.rectOK (R : Ray) (e T x0 x1 y0 y1 ztop : Rat) : Bool :=
  let W := R.w + R.reach e
  decide (R.latMax x0 x1 y0 y1 < -W) || decide (W < R.latMin x0 x1 y0 y1) ||
  decide (R.alongMax x0 x1 y0 y1 < -R.reach e) || decide (T ≤ R.alongMin x0 x1 y0 y1) ||
  decide (ztop < R.floorAt e (R.alongMin x0 x1 y0 y1))

/-- Along-track distance from which the corridor floor is above `top` (needs `0 < g`). -/
def Ray.horizon (R : Ray) (e top : Rat) : Rat := R.reach e + (top + e - R.z0 + 1) / R.g

/-- `top` bounds every grid height and every building top. -/
def TopOK (M : CityMap) (top : Rat) : Bool :=
  (List.range M.n).all (fun i => (List.range M.n).all fun j => decide (M.height i j ≤ top)) &&
  M.boxes.all fun b => decide (b.z1 ≤ top)

/-- **Ray `Geo`, decided** given a bound `top` on all solids: every building and every grid square (clamped beyond
the edge) in the bounding box of the corridor up to `Ray.horizon` passes `Ray.rectOK`; past the horizon the floor is
above `top`. -/
def Ray.geoB (M : CityMap) (R : Ray) (e top : Rat) : Bool :=
  let W := R.w + R.reach e
  let T := R.horizon e top
  let D := R.a * R.a + R.b * R.b
  let L := max (R.reach e) T
  let bx := (L * absR R.a + W * absR R.b) / D
  let by' := (L * absR R.b + W * absR R.a) / D
  decide (2 ≤ M.n) && decide (0 < M.spacing) && decide (0 < R.g) && decide (0 < D) && TopOK M top &&
  M.boxes.all (fun b => R.rectOK e T b.x0 b.x1 b.y0 b.y1 b.z1) &&
  allSquares M (R.px - bx) (R.px + bx) (R.py - by') (R.py + by') fun kx ky =>
    R.rectOK e T (edge M kx) (edge M (kx + 1)) (edge M ky) (edge M (ky + 1)) (sqMax M (clampIdx M kx) (clampIdx M ky))

theorem Ray.floorAt_mono {R : Ray} {e t t' : Rat} (hg : 0 ≤ R.g) (h : t ≤ t') : R.floorAt e t ≤ R.floorAt e t' := by
  have hm : max 0 (t - R.reach e) ≤ max 0 (t' - R.reach e) := by grind
  have := Rat.mul_le_mul_of_nonneg_left hm hg
  simp only [Ray.floorAt]; grind

theorem Ray.rectOK_sound {R : Ray} {e T x0 x1 y0 y1 ztop : Rat} (hg : 0 ≤ R.g) (h : R.rectOK e T x0 x1 y0 y1 ztop = true)
    {q : Pt} (hx0 : x0 ≤ q.x) (hx1 : q.x ≤ x1) (hy0 : y0 ≤ q.y) (hy1 : q.y ≤ y1) (hz : q.z ≤ ztop)
    (hl1 : -(R.w + R.reach e) ≤ R.lateral q) (hl2 : R.lateral q ≤ R.w + R.reach e) (ha : -R.reach e ≤ R.along q)
    (hT : R.along q < T) : q.z < R.floorAt e (R.along q) := by
  have ax := lin_bounds (p := R.px) (a := R.a) hx0 hx1
  have ay := lin_bounds (p := R.py) (a := R.b) hy0 hy1
  have bx := lin_bounds (p := R.px) (a := R.b) hx0 hx1
  have byy := lin_bounds (p := R.py) (a := R.a) hy0 hy1
  have hmin : R.alongMin x0 x1 y0 y1 ≤ R.along q := by simp only [Ray.alongMin, Ray.along]; grind
  have hmax : R.along q ≤ R.alongMax x0 x1 y0 y1 := by simp only [Ray.alongMax, Ray.along]; grind
  have lmin : R.latMin x0 x1 y0 y1 ≤ R.lateral q := by simp only [Ray.latMin, Ray.lateral]; grind
  have lmax : R.lateral q ≤ R.latMax x0 x1 y0 y1 := by simp only [Ray.latMax, Ray.lateral]; grind
  simp only [Ray.rectOK, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · grind
  · grind
  · grind
  · grind
  · have := Ray.floorAt_mono (e := e) hg hmin; grind

theorem topOK_le {M : CityMap} {top : Rat} (h : TopOK M top = true) (hn : 2 ≤ M.n) {q : Pt} (hs : Solid M q) :
    q.z ≤ top := by
  simp only [TopOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hh, hb⟩ := h
  rcases hs with ht | ⟨b, hbm, hc⟩
  · have := terrain_le_sqMax hn q.x q.y
    have hi : clampIdx M (cellOf M q.x) + 1 < M.n := by simp only [clampIdx]; omega
    have hj : clampIdx M (cellOf M q.y) + 1 < M.n := by simp only [clampIdx]; omega
    have h1 := hh _ (by omega) _ (by omega)
    have h2 := hh _ hi _ (show clampIdx M (cellOf M q.y) < M.n by omega)
    have h3 := hh _ (show clampIdx M (cellOf M q.x) < M.n by omega) _ hj
    have h4 := hh _ hi _ hj
    simp only [sqMax] at this
    grind
  · have := hb b hbm; simp only [Box.Contains] at hc; grind

theorem Ray.geo_of_geoB {M : CityMap} {R : Ray} {e top : Rat} (h : R.geoB M e top = true) : R.Geo M e := by
  simp only [Ray.geoB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hs⟩, hg⟩, hD⟩, htop⟩, hb⟩, hsq⟩ := h
  intro q hsol hl1 hl2 ha
  have hg0 : 0 ≤ R.g := Rat.le_of_lt hg
  by_cases hT : R.horizon e top ≤ R.along q
  · -- past the horizon the floor is above every solid
    have hq := topOK_le htop hn hsol
    have hcan : R.g * ((top + e - R.z0 + 1) / R.g) = top + e - R.z0 + 1 := by
      rw [Rat.mul_comm]; exact div_mul_cancel' hg
    have hm : (top + e - R.z0 + 1) / R.g ≤ max 0 (R.along q - R.reach e) := by
      simp only [Ray.horizon] at hT; grind
    have := Rat.mul_le_mul_of_nonneg_left hm hg0
    simp only [Ray.floorAt]; grind
  · have hT' : R.along q < R.horizon e top := Rat.not_le.mp hT
    rcases hsol with ht | ⟨b, hbm, hc⟩
    · -- the corridor short of the horizon lies in the bounding box, so its squares were checked
      generalize hL : max (R.reach e) (R.horizon e top) = L at hsq
      have hLa : -L ≤ R.along q ∧ R.along q ≤ L := by
        have := absR_nonneg R.a; have := absR_nonneg R.b
        constructor <;> grind
      have ma := mul_abs_bound R.a hLa.1 hLa.2
      have mb := mul_abs_bound R.b hLa.1 hLa.2
      have la := mul_abs_bound R.a hl1 hl2
      have lb := mul_abs_bound R.b hl1 hl2
      have ex : (R.a * R.a + R.b * R.b) * (q.x - R.px) = R.along q * R.a - R.lateral q * R.b := by
        simp only [Ray.along, Ray.lateral]; grind
      have ey : (R.a * R.a + R.b * R.b) * (q.y - R.py) = R.along q * R.b + R.lateral q * R.a := by
        simp only [Ray.along, Ray.lateral]; grind
      have dx := div_mul_cancel' (a := L * absR R.a + (R.w + R.reach e) * absR R.b) hD
      have dy := div_mul_cancel' (a := L * absR R.b + (R.w + R.reach e) * absR R.a) hD
      generalize (L * absR R.a + (R.w + R.reach e) * absR R.b) / (R.a * R.a + R.b * R.b) = bx at hsq dx
      generalize (L * absR R.b + (R.w + R.reach e) * absR R.a) / (R.a * R.a + R.b * R.b) = by' at hsq dy
      have bx1 : q.x - R.px ≤ bx := Rat.le_of_mul_le_mul_left (c := R.a * R.a + R.b * R.b) (by grind) hD
      have bx2 : -bx ≤ q.x - R.px := Rat.le_of_mul_le_mul_left (c := R.a * R.a + R.b * R.b) (by grind) hD
      have by1 : q.y - R.py ≤ by' := Rat.le_of_mul_le_mul_left (c := R.a * R.a + R.b * R.b) (by grind) hD
      have by2 : -by' ≤ q.y - R.py := Rat.le_of_mul_le_mul_left (c := R.a * R.a + R.b * R.b) (by grind) hD
      have hc := allSquares_at hs hsq (x := q.x) (y := q.y) (by grind) (by grind) (by grind) (by grind)
      have := terrain_le_sqMax hn q.x q.y
      exact Ray.rectOK_sound hg0 hc (edge_le hs _) (le_edge_succ hs _) (edge_le hs _) (le_edge_succ hs _)
        (by grind) hl1 hl2 ha hT'
    · simp only [Box.Contains] at hc
      exact Ray.rectOK_sound hg0 (hb b hbm) (by grind) (by grind) (by grind) (by grind) (by grind) hl1 hl2 ha hT'

end CitySafety.EndSets
