import Spec.CitySafetyChecks

/-!
# End sets: helix and ray funnel clearance (`Geo`), independent of the aircraft model

Bounds on a reported position `p` (`Helix.Conf`, `Ray.Conf`) plus map clearance (`Helix.Geo`, `Ray.Geo`) give an
axis box `[p ± e]` with nothing solid in it; with `AirframeWithin e s` that rules out the spec's `Crash M s`.
Distances are compared squared, and the ray's direction is a rational vector whose length is the distance unit.
-/

namespace CitySafety.EndSets
open CitySafety JsbExact

/-! ## Algebra helpers (core only, no Mathlib) -/

theorem sq_nonneg (x : Rat) : 0 ≤ x * x := by
  rcases (Rat.le_total : (0 : Rat) ≤ x ∨ x ≤ 0) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (show (0:Rat) ≤ -x by grind) (show (0:Rat) ≤ -x by grind)
    rwa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this

theorem sq_le_sq {a b : Rat} (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  have h1 := Rat.mul_le_mul_of_nonneg_left h ha
  have h2 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_trans ha h)
  exact Rat.le_trans h1 h2

theorem le_of_sq_le {x y : Rat} (hy : 0 ≤ y) (h : x * x ≤ y * y) : x ≤ y := by
  apply Classical.byContradiction
  intro hn
  have hlt : y < x := Rat.not_le.mp hn
  have hx : 0 < x := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hlt) hy
  have h2 := Rat.mul_lt_mul_of_pos_left hlt hx
  grind

/-- `-e ≤ v ≤ e` gives `v² ≤ e²`. -/
theorem sq_le_of_abs {v e : Rat} (h1 : -e ≤ v) (h2 : v ≤ e) : v * v ≤ e * e := by
  rcases (Rat.le_total : (0 : Rat) ≤ v ∨ v ≤ 0) with h | h
  · exact sq_le_sq h h2
  · have := sq_le_sq (show (0:Rat) ≤ -v by grind) (show -v ≤ e by grind)
    rwa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this

/-- `x² ≤ h²` and `0 ≤ h` give `-h ≤ x ≤ h`. -/
theorem abs_le_of_sq_le {x h : Rat} (hh : 0 ≤ h) (hx : x * x ≤ h * h) : -h ≤ x ∧ x ≤ h := by
  refine ⟨?_, le_of_sq_le hh hx⟩
  have : -x ≤ h := le_of_sq_le hh (by rwa [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg])
  grind

/-- Cauchy–Schwarz in the plane, squared bounds only: `|w| ≤ k`, `|v| ≤ m` give `w · v ≤ k m`. -/
theorem dot_le {wx wy vx vy k m : Rat} (hk : 0 ≤ k) (hm : 0 ≤ m) (hw : wx * wx + wy * wy ≤ k * k)
    (hv : vx * vx + vy * vy ≤ m * m) : wx * vx + wy * vy ≤ k * m := by
  have hkm : 0 ≤ k * m := Rat.mul_nonneg hk hm
  have lag := sq_nonneg (wx * vy - wy * vx)
  have p1 := Rat.mul_le_mul_of_nonneg_right hw (sq_nonneg' vx vy)
  have p2 := Rat.mul_le_mul_of_nonneg_left hv (sq_nonneg k)
  apply le_of_sq_le hkm
  grind
where
  sq_nonneg' (vx vy : Rat) : 0 ≤ vx * vx + vy * vy := Rat.add_nonneg (sq_nonneg vx) (sq_nonneg vy)

/-- The triangle inequality, squared: `|w| ≤ k` and `|v| ≤ m` give `|w + v| ≤ k + m`. -/
theorem tri_le {wx wy vx vy k m : Rat} (hk : 0 ≤ k) (hm : 0 ≤ m) (hw : wx * wx + wy * wy ≤ k * k)
    (hv : vx * vx + vy * vy ≤ m * m) : (wx + vx) * (wx + vx) + (wy + vy) * (wy + vy) ≤ (k + m) * (k + m) := by
  have := dot_le hk hm hw hv
  grind

/-- The triangle inequality, squared, strict in the first term: `|w| < k` and `|v| ≤ m` give `|w + v| < k + m`. -/
theorem tri_lt {wx wy vx vy k m : Rat} (hk : 0 ≤ k) (hm : 0 ≤ m) (hw : wx * wx + wy * wy < k * k)
    (hv : vx * vx + vy * vy ≤ m * m) : (wx + vx) * (wx + vx) + (wy + vy) * (wy + vy) < (k + m) * (k + m) := by
  have := dot_le hk hm (Rat.le_of_lt hw) hv
  grind

/-- `|x|` for rationals. -/
def absR (x : Rat) : Rat := if x < 0 then -x else x

theorem absR_nonneg (x : Rat) : 0 ≤ absR x := by
  unfold absR; split <;> grind

/-- `-m ≤ v ≤ m` bounds `v · a` by `m |a|`. -/
theorem mul_abs_bound {v m : Rat} (a : Rat) (h1 : -m ≤ v) (h2 : v ≤ m) : -(m * absR a) ≤ v * a ∧ v * a ≤ m * absR a := by
  unfold absR
  split
  · rename_i ha
    have hna : 0 ≤ -a := by grind
    have e1 := Rat.mul_le_mul_of_nonneg_right h1 hna
    have e2 := Rat.mul_le_mul_of_nonneg_right h2 hna
    simp only [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg] at e1 e2
    constructor <;> grind
  · rename_i ha
    have ha' : 0 ≤ a := by grind
    have e1 := Rat.mul_le_mul_of_nonneg_right h1 ha'
    have e2 := Rat.mul_le_mul_of_nonneg_right h2 ha'
    simp only [Rat.neg_mul] at e1
    constructor <;> grind

/-! ## Airframe extent -/

/-- `q` lies in the closed axis box of half-size `e` around `c`: within `e` of `c` along each map axis. -/
def InBox (e : Rat) (c q : Pt) : Prop :=
  c.x - e ≤ q.x ∧ q.x ≤ c.x + e ∧ c.y - e ≤ q.y ∧ q.y ≤ c.y + e ∧ c.z - e ≤ q.z ∧ q.z ≤ c.z + e

/-- The reported CG of state `s` on the map (m): `mapPoint`'s base point, east = ECEF y, north = ECEF z, up = the
altitude above sea level, read exactly from the plant's `report`; `none` if one of them is not finite. -/
def reportedCG (s : State Float) : Option Pt := do
  let rep := report s
  return ⟨(← ratOf rep.loc.y) * ft, (← ratOf rep.loc.z) * ft, (← ratOf rep.hsl) * ft⟩

/-- The airframe points of state `s` (as `airframe` places them) are defined and lie within `e` of `c` per axis.
With `c` the gate's reported position this is the bridge's `AirframeNearAt` (`CityGate/EndSets.lean`). -/
def AirframeWithinOf (e : Rat) (s : State Float) (c : Pt) : Prop :=
  ∃ ps, airframe s = some ps ∧ ∀ q ∈ ps, InBox e c q

/-- **Airframe extent**: every airframe point of state `s` lies within `e` per axis of the reported CG. A hypothesis,
supplied later (from bounds on the reported rotation matrix, or checked); not proved for all states. -/
def AirframeWithin (e : Rat) (s : State Float) : Prop :=
  ∀ c, reportedCG s = some c → AirframeWithinOf e s c

/-- The axis box is convex: the hull of points in it stays in it. -/
theorem inBox_hull {e : Rat} {c : Pt} {ps : List Pt} (hp : ∀ q ∈ ps, InBox e c q) {q : Pt} (hq : InHull ps q) :
    InBox e c q := by
  have g := fun cx cy cz k (f : ∀ r ∈ ps, k ≤ cx * r.x + cy * r.y + cz * r.z) => hull_lin_ge cx cy cz k f hq
  have l1 := g 1 0 0 (c.x - e) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  have l2 := g (-1) 0 0 (-(c.x + e)) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  have l3 := g 0 1 0 (c.y - e) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  have l4 := g 0 (-1) 0 (-(c.y + e)) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  have l5 := g 0 0 1 (c.z - e) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  have l6 := g 0 0 (-1) (-(c.z + e)) (fun r hr => by have := hp r hr; simp only [InBox] at this; grind)
  simp only [InBox]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- **No crash from a clear box**: if the airframe lies within `e` of `c` and the box `[c ± e]` holds nothing solid,
the state is not a crash. -/
theorem not_crash_of_clear {M : CityMap} {s : State Float} {e : Rat} {c : Pt} (ha : AirframeWithinOf e s c)
    (hclr : ∀ q, InBox e c q → ¬ Solid M q) : ¬ Crash M s := by
  obtain ⟨ps, hps, hin⟩ := ha
  simp only [Crash, hps]
  rintro ⟨q, hq, hs⟩
  exact hclr q (inBox_hull hin hq) hs

/-- The horizontal offset of a point in the box `[p ± e]` from `p` is at most `e'` long when `2 e² ≤ e'²`. -/
theorem box_horiz {e e' : Rat} {p q : Pt} (he : 2 * e * e ≤ e' * e') (hq : InBox e p q) :
    (q.x - p.x) * (q.x - p.x) + (q.y - p.y) * (q.y - p.y) ≤ e' * e' := by
  simp only [InBox] at hq
  have h1 := sq_le_of_abs (show -e ≤ q.x - p.x by grind) (show q.x - p.x ≤ e by grind)
  have h2 := sq_le_of_abs (show -e ≤ q.y - p.y by grind) (show q.y - p.y ≤ e by grind)
  grind

/-! ## The helix tube -/

/-- Squared horizontal distance from `(cx, cy)` to `q`. -/
def dist2 (cx cy : Rat) (q : Pt) : Rat := (q.x - cx) * (q.x - cx) + (q.y - cy) * (q.y - cy)

/-- The horizontal distance from `(cx, cy)` to `q` is in `[lo, hi]`, compared squared (`lo ≤ 0`: no lower bound). -/
def InAnnulus (cx cy lo hi : Rat) (q : Pt) : Prop :=
  (lo ≤ 0 ∨ lo * lo ≤ dist2 cx cy q) ∧ dist2 cx cy q ≤ hi * hi

/-- A climbing-helix funnel: centre `(cx, cy)`, radius `r`, radial slack `δ` at entry, widening `s` m per metre
climbed (the centre's drift), entry altitude `z0` and release altitude `zTop` (m), above which nothing is solid. -/
structure Helix where
  cx : Rat
  cy : Rat
  r : Rat
  δ : Rat
  s : Rat
  z0 : Rat
  zTop : Rat
  deriving DecidableEq, Repr

/-- Radial slack at altitude `z`: `δ + s (z - z0)`. -/
def Helix.slack (H : Helix) (z : Rat) : Rat := H.δ + H.s * (z - H.z0)

/-- **The helix funnel's `Dyn` bounds** on a reported position `p`: at or above `zTop`, or at or above `z0` with
horizontal distance to the centre within `r ± slack p.z`. -/
def Helix.Conf (H : Helix) (p : Pt) : Prop :=
  H.zTop ≤ p.z ∨ (H.z0 ≤ p.z ∧ InAnnulus H.cx H.cy (H.r - H.slack p.z) (H.r + H.slack p.z) p)

/-- **The helix funnel's `Geo`**: every solid point is below `zTop - e`, and below `z0 - e` if its horizontal
distance to the centre is within `r ± (slack (q.z + e) + e')`; `e'` covers the box's half-diagonal. -/
def Helix.Geo (M : CityMap) (H : Helix) (e e' : Rat) : Prop :=
  ∀ q, Solid M q → q.z < H.zTop - e ∧
    (InAnnulus H.cx H.cy (H.r - H.slack (q.z + e) - e') (H.r + H.slack (q.z + e) + e') q → q.z < H.z0 - e)

theorem Helix.slack_mono {H : Helix} (hs : 0 ≤ H.s) {z z' : Rat} (h : z ≤ z') : H.slack z ≤ H.slack z' := by
  have := Rat.mul_le_mul_of_nonneg_left (show z - H.z0 ≤ z' - H.z0 by grind) hs
  simp only [Helix.slack]; grind

/-- **Helix clearance (G)**: in the helix funnel with `Geo`, the box `[p ± e]` around the reported position holds
nothing solid. -/
theorem Helix.clear {M : CityMap} {H : Helix} {e e' : Rat} (hr : 0 ≤ H.r + H.δ) (hs : 0 ≤ H.s) (he' : 0 ≤ e')
    (he : 2 * e * e ≤ e' * e') {p : Pt} (hp : H.Conf p) (hg : H.Geo M e e') : ∀ q, InBox e p q → ¬ Solid M q := by
  intro q hq hsol
  have hqz : p.z - e ≤ q.z := hq.2.2.2.2.1
  obtain ⟨htop, hlow⟩ := hg q hsol
  rcases hp with hp | ⟨hz, hlo, hhi⟩
  · grind
  have hv := box_horiz he hq
  have hw : H.slack p.z ≤ H.slack (q.z + e) := Helix.slack_mono hs (by grind)
  have hw0 : H.δ ≤ H.slack p.z := by
    have := Rat.mul_nonneg hs (show 0 ≤ p.z - H.z0 by grind); simp only [Helix.slack]; grind
  suffices hin : InAnnulus H.cx H.cy (H.r - H.slack (q.z + e) - e') (H.r + H.slack (q.z + e) + e') q by
    have := hlow hin; grind
  refine ⟨?_, ?_⟩
  · by_cases h0 : H.r - H.slack (q.z + e) - e' ≤ 0
    · exact .inl h0
    · refine .inr (Rat.not_lt.mp fun hlt => ?_)
      have hk : 0 ≤ H.r - H.slack (q.z + e) - e' := by grind
      have hwq : (q.x - H.cx) * (q.x - H.cx) + (q.y - H.cy) * (q.y - H.cy) <
          (H.r - H.slack (q.z + e) - e') * (H.r - H.slack (q.z + e) - e') := hlt
      have hv' : (p.x - q.x) * (p.x - q.x) + (p.y - q.y) * (p.y - q.y) ≤ e' * e' := by grind
      have t := tri_lt hk he' hwq hv'
      have m := sq_le_sq (show 0 ≤ H.r - H.slack (q.z + e) - e' + e' by grind)
        (show H.r - H.slack (q.z + e) - e' + e' ≤ H.r - H.slack p.z by grind)
      rcases hlo with hlo | hlo
      · grind
      · simp only [dist2] at hlo; grind
  · have t := tri_le (show 0 ≤ H.r + H.slack p.z by grind) he' hhi hv
    have m := sq_le_sq (show 0 ≤ H.r + H.slack p.z + e' by grind)
      (show H.r + H.slack p.z + e' ≤ H.r + H.slack (q.z + e) + e' by grind)
    simp only [dist2] at t ⊢; grind

/-- **Helix funnel, spec crash**: with the airframe within `e` of the reported CG, a CG in the helix funnel and the
funnel's `Geo`, the state is not a `Crash`. -/
theorem Helix.not_crash {M : CityMap} {H : Helix} {e e' : Rat} (hr : 0 ≤ H.r + H.δ) (hs : 0 ≤ H.s) (he' : 0 ≤ e')
    (he : 2 * e * e ≤ e' * e') {st : State Float} {c : Pt} (hc : reportedCG st = some c) (hconf : H.Conf c)
    (ha : AirframeWithin e st) (hg : H.Geo M e e') : ¬ Crash M st :=
  not_crash_of_clear (ha c hc) (H.clear hr hs he' he hconf hg)

/-! ## The ray tube -/

/-- A climbing-ray funnel: start `(px, py)`, direction `(a, b)` (any nonzero rational vector; its length is the unit
of along-track and lateral distance, so a unit vector gives metres), lateral bound `w` at entry widening `s` per metre
climbed, climb `g` (m) per unit of along-track distance, entry altitude `z0` and release altitude `zTop` (m). -/
structure Ray where
  px : Rat
  py : Rat
  a : Rat
  b : Rat
  w : Rat
  s : Rat
  z0 : Rat
  g : Rat
  zTop : Rat
  deriving DecidableEq, Repr

/-- Along-track distance of `q` from the start, in units of the direction's length. -/
def Ray.along (R : Ray) (q : Pt) : Rat := (q.x - R.px) * R.a + (q.y - R.py) * R.b

/-- Signed lateral offset of `q` from the line, in units of the direction's length (positive to the left). -/
def Ray.lateral (R : Ray) (q : Pt) : Rat := (q.y - R.py) * R.a - (q.x - R.px) * R.b

/-- Lateral bound at altitude `z`: `w + s (z - z0)`. -/
def Ray.halfWidth (R : Ray) (z : Rat) : Rat := R.w + R.s * (z - R.z0)

/-- **The ray funnel's `Dyn` bounds** on a reported position `p`: at or above `zTop`, or lateral offset within
`halfWidth p.z`, along-track distance at least 0 and altitude at least `z0 + g · along`. -/
def Ray.Conf (R : Ray) (p : Pt) : Prop :=
  R.zTop ≤ p.z ∨
    (-R.halfWidth p.z ≤ R.lateral p ∧ R.lateral p ≤ R.halfWidth p.z ∧ 0 ≤ R.along p ∧ R.z0 + R.g * R.along p ≤ p.z)

/-- How far, in along-track and lateral units, a box of half-size `e` reaches: `e (|a| + |b|)`. -/
def Ray.reach (R : Ray) (e : Rat) : Rat := e * (absR R.a + absR R.b)

/-- The corridor floor at along-track distance `t` for boxes of half-size `e`: solids there must stay below it. -/
def Ray.floorAt (R : Ray) (e t : Rat) : Rat := R.z0 + R.g * max 0 (t - R.reach e) - e

/-- **The ray funnel's `Geo`**: every solid point is below `zTop - e`, and below the corridor floor at its along-track
distance if it is within `halfWidth (q.z + e) + reach` laterally and at least `-reach` along. -/
def Ray.Geo (M : CityMap) (R : Ray) (e : Rat) : Prop :=
  ∀ q, Solid M q → q.z < R.zTop - e ∧
    (-(R.halfWidth (q.z + e) + R.reach e) ≤ R.lateral q → R.lateral q ≤ R.halfWidth (q.z + e) + R.reach e →
      -R.reach e ≤ R.along q → q.z < R.floorAt e (R.along q))

theorem Ray.halfWidth_mono {R : Ray} (hs : 0 ≤ R.s) {z z' : Rat} (h : z ≤ z') : R.halfWidth z ≤ R.halfWidth z' := by
  have := Rat.mul_le_mul_of_nonneg_left (show z - R.z0 ≤ z' - R.z0 by grind) hs
  simp only [Ray.halfWidth]; grind

/-- Moving by at most `e` per axis changes along-track distance and lateral offset by at most `reach e`. -/
theorem Ray.shift {R : Ray} {e : Rat} {p q : Pt} (hq : InBox e p q) :
    -R.reach e ≤ R.along q - R.along p ∧ R.along q - R.along p ≤ R.reach e ∧
    -R.reach e ≤ R.lateral q - R.lateral p ∧ R.lateral q - R.lateral p ≤ R.reach e := by
  simp only [InBox] at hq
  have bx := fun c => mul_abs_bound c (show -e ≤ q.x - p.x by grind) (show q.x - p.x ≤ e by grind)
  have by' := fun c => mul_abs_bound c (show -e ≤ q.y - p.y by grind) (show q.y - p.y ≤ e by grind)
  have ha := bx R.a
  have hb := bx R.b
  have ha' := by' R.a
  have hb' := by' R.b
  simp only [Ray.along, Ray.lateral, Ray.reach]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- **Ray clearance (G)**: in the ray funnel with `Geo`, a non-negative climb and widening, the box `[p ± e]` around
the reported position holds nothing solid. -/
theorem Ray.clear {M : CityMap} {R : Ray} {e : Rat} (hg0 : 0 ≤ R.g) (hs : 0 ≤ R.s) {p : Pt} (hp : R.Conf p)
    (hg : R.Geo M e) : ∀ q, InBox e p q → ¬ Solid M q := by
  intro q hq hsol
  have hqz : p.z - e ≤ q.z := hq.2.2.2.2.1
  obtain ⟨htop, hlow⟩ := hg q hsol
  rcases hp with hp | ⟨hl1, hl2, ha0, hz⟩
  · grind
  obtain ⟨s1, s2, s3, s4⟩ := Ray.shift (R := R) hq
  have hw : R.halfWidth p.z ≤ R.halfWidth (q.z + e) := Ray.halfWidth_mono hs (by grind)
  have hlt := hlow (by grind) (by grind) (by grind)
  have hm : max 0 (R.along q - R.reach e) ≤ R.along p := by
    rcases (Rat.le_total : (0 : Rat) ≤ R.along q - R.reach e ∨ _) with h | h
    · rw [Rat.max_def]; split <;> grind
    · rw [Rat.max_def]; split <;> grind
  have := Rat.mul_le_mul_of_nonneg_left hm hg0
  simp only [Ray.floorAt] at hlt
  grind

/-- **Ray funnel, spec crash**: with the airframe within `e` of the reported CG, a CG in the ray funnel and the
funnel's `Geo`, the state is not a `Crash`. -/
theorem Ray.not_crash {M : CityMap} {R : Ray} {e : Rat} (hg0 : 0 ≤ R.g) (hs : 0 ≤ R.s) {st : State Float} {c : Pt}
    (hc : reportedCG st = some c) (hconf : R.Conf c) (ha : AirframeWithin e st) (hg : R.Geo M e) : ¬ Crash M st :=
  not_crash_of_clear (ha c hc) (R.clear hg0 hs hconf hg)

end CitySafety.EndSets
