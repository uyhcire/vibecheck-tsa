import CityGate.Map
import CityGate.Plant
import VcFilter.Exact
import CityGate.Landing
import Spec.CitySafety

/-! What a crash is (trusted surface), the clearance test the gate runs on every frame of every rollout, and its
soundness (`clear_sound`). -/

namespace CityGate
open VcFilter (ratOfFloat)

/-! ### What a crash is (trusted surface) -/

/-- Terrain height (m) at grid node `(i, j)`: `x = gridX0 + i · gridStep`, `y = gridY0 + j · gridStep`, raised to the
world floor `Landing.rwyZ` (the runway surface and JSBSim's ground plane). -/
def node (i j : Nat) : Rat := max Landing.rwyZ (terrain.getD (j * gridN + i) 0)

/-- Grid coordinate of `x` (m) along an axis starting at `x0`, clamped to the grid `[0, gridN - 1]`. -/
def gridCoord (x0 : Int) (x : Rat) : Rat := max 0 (min ((gridN - 1 : Nat) : Rat) ((x - x0) / (gridStep : Rat)))

/-- The grid square containing grid coordinate `g` (the last square for the far edge). -/
def square (g : Rat) : Nat := min g.floor.toNat (gridN - 2)

/-- Terrain height (m) at map point `(x, y)`, as `data/map.json` defines it: positions outside the grid clamp to its
edge, and each grid square splits along its south-west to north-east diagonal and interpolates linearly. -/
def terrainAt (x y : Rat) : Rat :=
  let gx := gridCoord gridX0 x
  let gy := gridCoord gridY0 y
  let i := square gx
  let j := square gy
  let u := gx - i
  let v := gy - j
  if v ≤ u then node i j + u * (node (i + 1) j - node i j) + v * (node (i + 1) (j + 1) - node (i + 1) j)
  else node i j + v * (node i (j + 1) - node i j) + u * (node (i + 1) (j + 1) - node i (j + 1))

/-- Map point `(x, y, z)` (m) is solid: inside a building box (closed) or at or below the terrain surface. -/
def Solid (x y z : Rat) : Prop :=
  (∃ b ∈ boxes, b.xmin ≤ x ∧ x ≤ b.xmax ∧ b.ymin ≤ y ∧ y ≤ b.ymax ∧ b.zmin ≤ z ∧ z ≤ b.zmax) ∨
    z ≤ terrainAt x y

/-- Half-size (m) of the airframe envelope. -/
def envHalf : Rat := 6

/-- The aircraft's exact map position: its doubles (`Plane.pos`) decoded to the rationals they denote, if finite. -/
def exactPos (p : Plane) : Option (Rat × Rat × Rat) := do
  pure (← ratOfFloat p.pos.1, ← ratOfFloat p.pos.2.1, ← ratOfFloat p.pos.2.2)

/-- **A crash**: some point of the airframe envelope is solid, or the position is not finite. The envelope is the
cube of half-size `envHalf` = 6 m around the aircraft's reference point, edges along the map axes. It contains every
point within 6 m of the reference point, which covers the whole C172 (11 m span, 8.3 m long) at any attitude
provided the airframe lies within 6 m of that point. This is conservative relative to the contact shape still
open in `docs/safety-objective.md` (the hull of the 7 contact points lies inside it), so no crash here means no
contact there. -/
def Crash (p : Plane) : Prop :=
  match exactPos p with
  | some (x, y, z) => ∃ dx dy dz : Rat, -envHalf ≤ dx ∧ dx ≤ envHalf ∧ -envHalf ≤ dy ∧ dy ≤ envHalf ∧
      -envHalf ≤ dz ∧ dz ≤ envHalf ∧ Solid (x + dx) (y + dy) (z + dz)
  | none => True

/-! ### The clearance test

Fixed point at 16 units per metre, all in `Int`. The aircraft's position is rounded outward, the map is rounded
outward once (`boxesI`, `terrainI`), and a keep-out cube of half-size 8.5 m (the Rust gate's 4.5 m body radius + 4 m
margin) plus `extra` must contain no box (looked up in a 32 m cell index) and stay above every terrain node of the
grid squares under it. -/

/-- Fixed-point units per metre. -/
def S : Rat := 16

/-- Keep-out half-size (units): 8.5 m. At least `envHalf · S` (96), which is all soundness needs. -/
def keepBase : Nat := 136

/-- `extra` metres in units (any natural number keeps the test sound; negative or NaN give 0). -/
def extraUnits (e : Float) : Nat := if 0 < e && e < 1000 then (e * 16).ceil.toUInt64.toNat else 0

/-- A box rounded outward to units. -/
def roundOut (b : Box Rat) : Box Int :=
  ⟨(b.xmin * S).floor, (b.ymin * S).floor, (b.xmax * S).ceil, (b.ymax * S).ceil, (b.zmin * S).floor,
    (b.zmax * S).ceil⟩

def boxesI : List (Box Int) := boxes.toList.map roundOut

/-- Index cell of a coordinate (units): 32 m cells from -1600 m, 100 per side, clamped to the edge cells. -/
def cellIdx (v : Int) : Nat := min ((v + 25600) / 512).toNat 99

/-- Boxes whose y-range meets index row `j`. -/
def rowBoxes : Array (List (Box Int)) :=
  Array.ofFn (n := 100) fun j => boxesI.filter fun b => decide (cellIdx b.ymin ≤ j ∧ (j : Nat) ≤ cellIdx b.ymax)

/-- Boxes meeting index cell `(k % 100, k / 100)`. -/
def cellBoxes : Array (List (Box Int)) :=
  Array.ofFn (n := 100 * 100) fun k =>
    (rowBoxes.getD (k / 100) []).filter fun b => decide (cellIdx b.xmin ≤ k % 100 ∧ k % 100 ≤ cellIdx b.xmax)

/-- `[lo, hi]` meets `[a, b]`. -/
def meets (lo hi a b : Int) : Bool := a ≤ hi && lo ≤ b

/-- No box meets the keep-out box `[xl, xh] × [yl, yh] × [zl, zh]` (units). -/
def boxesClear (xl xh yl yh zl zh : Int) : Bool :=
  (List.range' (cellIdx xl) (cellIdx xh + 1 - cellIdx xl)).all fun i =>
    (List.range' (cellIdx yl) (cellIdx yh + 1 - cellIdx yl)).all fun j =>
      (cellBoxes.getD (j * 100 + i) []).all fun b =>
        !(meets xl xh b.xmin b.xmax && meets yl yh b.ymin b.ymax && meets zl zh b.zmin b.zmax)

/-- Terrain heights raised to the floor and rounded up to units. -/
def terrainI : Array Int := terrain.map fun q => (max Landing.rwyZ q * S).ceil

def nodeI (i j : Nat) : Int := terrainI.getD (j * gridN + i) ((max Landing.rwyZ 0 * S).ceil)

/-- Highest node (units) of grid square `(i, j)`. -/
def squareTop (i j : Nat) : Int := max (max (nodeI i j) (nodeI (i + 1) j)) (max (nodeI i (j + 1)) (nodeI (i + 1) (j + 1)))

/-- Grid square under the coordinate `v` (units). -/
def squareOf (x0 : Int) (v : Int) : Nat := square (gridCoord x0 ((v : Rat) / S))

/-- Every grid square under `[xl, xh] × [yl, yh]` (units) has all its nodes below `zl`. -/
def terrainClear (xl xh yl yh zl : Int) : Bool :=
  (List.range' (squareOf gridX0 xl) (squareOf gridX0 xh + 1 - squareOf gridX0 xl)).all fun i =>
    (List.range' (squareOf gridY0 yl) (squareOf gridY0 yh + 1 - squareOf gridY0 yl)).all fun j =>
      squareTop i j < zl

/-- The cube test (the gate's earlier clearance test): the keep-out cube of half-size 8.5 m + `extra` around the
aircraft's observed position meets no building and stays above the terrain. Sound for the cube `Crash`
(`clearCube_sound`); the gate now uses `clearAt`, sound for the spec's `Crash` (`CityGate.clear_spec_sound`). -/
def clearCube (extra : Float) (p : Plane) : Bool :=
  match exactPos p with
  | some (x, y, z) =>
    let k : Int := keepBase + extraUnits extra
    terrainClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k) ((z * S).floor - k) &&
      boxesClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k)
        ((z * S).floor - k) ((z * S).ceil + k)
  | none => false

/-! ### Soundness -/

/-- An envelope point, scaled to units, lies in the keep-out window. -/
theorem window (q d : Rat) (k : Int) (hd1 : -envHalf ≤ d) (hd2 : d ≤ envHalf) (hk : (96 : Rat) ≤ k) :
    (((q * S).floor - k : Int) : Rat) ≤ (q + d) * S ∧ (q + d) * S ≤ (((q * S).ceil + k : Int) : Rat) := by
  have h1 := Rat.floor_le (q * S)
  have h2 : q * S ≤ ((q * S).ceil : Rat) := Rat.le_ceil
  simp only [envHalf, S, Rat.intCast_sub, Rat.intCast_add] at *
  constructor <;> grind

theorem cellIdx_mono {a b : Int} (h : a ≤ b) : cellIdx a ≤ cellIdx b := by
  unfold cellIdx; omega

theorem cellIdx_lt (a : Int) : cellIdx a < 100 := by
  unfold cellIdx; omega

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (d : α) {k : Nat} (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD, hk]

theorem mem_cellBoxes {b : Box Int} (hb : b ∈ boxesI) {i j : Nat}
    (hi1 : cellIdx b.xmin ≤ i) (hi2 : i ≤ cellIdx b.xmax) (hj1 : cellIdx b.ymin ≤ j) (hj2 : j ≤ cellIdx b.ymax)
    (hi : i < 100) (hj : j < 100) : b ∈ cellBoxes.getD (j * 100 + i) [] := by
  have hk : j * 100 + i < 100 * 100 := by omega
  rw [cellBoxes, getD_ofFn _ _ hk]
  simp only [List.mem_filter, decide_eq_true_eq]
  rw [show (j * 100 + i) / 100 = j by omega, show (j * 100 + i) % 100 = i by omega]
  refine ⟨?_, hi1, hi2⟩
  rw [rowBoxes, getD_ofFn _ _ hj]
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨hb, hj1, hj2⟩

/-- `x · S` lies between `a · S` rounded down and `b · S` rounded up when `x ∈ [a, b]`. -/
theorem roundOut_bounds {a b x : Rat} (ha : a ≤ x) (hb : x ≤ b) :
    (((a * S).floor : Int) : Rat) ≤ x * S ∧ x * S ≤ (((b * S).ceil : Int) : Rat) := by
  have h1 := Rat.floor_le (a * S)
  have h2 : b * S ≤ ((b * S).ceil : Rat) := Rat.le_ceil
  have hS : (0 : Rat) ≤ S := by unfold S; decide
  exact ⟨Rat.le_trans h1 (Rat.mul_le_mul_of_nonneg_right ha hS),
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hb hS) h2⟩

/-- An integer window `[lo, hi]` and box side `[a, b]` that both contain the rational `t` meet. -/
theorem meets_of {lo hi a b : Int} {t : Rat} (h1 : (lo : Rat) ≤ t) (h2 : t ≤ (hi : Rat)) (h3 : (a : Rat) ≤ t)
    (h4 : t ≤ (b : Rat)) : a ≤ hi ∧ lo ≤ b ∧ a ≤ b :=
  ⟨Rat.intCast_le_intCast.mp (Rat.le_trans h3 h2), Rat.intCast_le_intCast.mp (Rat.le_trans h1 h4),
    Rat.intCast_le_intCast.mp (Rat.le_trans h3 h4)⟩

theorem box_case {xl xh yl yh zl zh : Int} (hc : boxesClear xl xh yl yh zl zh = true) {px py pz : Rat}
    (wx1 : (xl : Rat) ≤ px * S) (wx2 : px * S ≤ (xh : Rat)) (wy1 : (yl : Rat) ≤ py * S) (wy2 : py * S ≤ (yh : Rat))
    (wz1 : (zl : Rat) ≤ pz * S) (wz2 : pz * S ≤ (zh : Rat)) {b : Box Rat} (hb : b ∈ boxes)
    (h1 : b.xmin ≤ px) (h2 : px ≤ b.xmax) (h3 : b.ymin ≤ py) (h4 : py ≤ b.ymax) (h5 : b.zmin ≤ pz)
    (h6 : pz ≤ b.zmax) : False := by
  have hbI : roundOut b ∈ boxesI := List.mem_map.mpr ⟨b, Array.mem_toList_iff.mpr hb, rfl⟩
  obtain ⟨rx1, rx2⟩ := roundOut_bounds h1 h2
  obtain ⟨ry1, ry2⟩ := roundOut_bounds h3 h4
  obtain ⟨rz1, rz2⟩ := roundOut_bounds h5 h6
  obtain ⟨mx1, mx2, mx3⟩ := meets_of wx1 wx2 rx1 rx2
  obtain ⟨my1, my2, my3⟩ := meets_of wy1 wy2 ry1 ry2
  obtain ⟨mz1, mz2, _⟩ := meets_of wz1 wz2 rz1 rz2
  have hxx : xl ≤ xh := Rat.intCast_le_intCast.mp (Rat.le_trans wx1 wx2)
  have hyy : yl ≤ yh := Rat.intCast_le_intCast.mp (Rat.le_trans wy1 wy2)
  have cx1 := cellIdx_mono (a := xl) (b := max xl (b.xmin * S).floor) (by omega)
  have cx2 := cellIdx_mono (a := max xl (b.xmin * S).floor) (b := xh) (by omega)
  have cx3 := cellIdx_mono (a := (b.xmin * S).floor) (b := max xl (b.xmin * S).floor) (by omega)
  have cx4 := cellIdx_mono (a := max xl (b.xmin * S).floor) (b := (b.xmax * S).ceil) (by omega)
  have cy1 := cellIdx_mono (a := yl) (b := max yl (b.ymin * S).floor) (by omega)
  have cy2 := cellIdx_mono (a := max yl (b.ymin * S).floor) (b := yh) (by omega)
  have cy3 := cellIdx_mono (a := (b.ymin * S).floor) (b := max yl (b.ymin * S).floor) (by omega)
  have cy4 := cellIdx_mono (a := max yl (b.ymin * S).floor) (b := (b.ymax * S).ceil) (by omega)
  have hmem := mem_cellBoxes hbI cx3 cx4 cy3 cy4 (cellIdx_lt _) (cellIdx_lt _)
  have hi : cellIdx (max xl (b.xmin * S).floor) ∈ List.range' (cellIdx xl) (cellIdx xh + 1 - cellIdx xl) :=
    List.mem_range'.mpr ⟨cellIdx (max xl (b.xmin * S).floor) - cellIdx xl, by omega, by omega⟩
  have hj : cellIdx (max yl (b.ymin * S).floor) ∈ List.range' (cellIdx yl) (cellIdx yh + 1 - cellIdx yl) :=
    List.mem_range'.mpr ⟨cellIdx (max yl (b.ymin * S).floor) - cellIdx yl, by omega, by omega⟩
  simp only [boxesClear, List.all_eq_true] at hc
  have hno := hc _ hi _ hj _ hmem
  have hm : (meets xl xh (roundOut b).xmin (roundOut b).xmax && meets yl yh (roundOut b).ymin (roundOut b).ymax &&
      meets zl zh (roundOut b).zmin (roundOut b).zmax) = true := by
    simp [meets, roundOut, mx1, mx2, my1, my2, mz1, mz2]
  rw [hm] at hno
  exact absurd hno (by decide)

theorem gridCoord_mono (x0 : Int) {a b : Rat} (h : a ≤ b) : gridCoord x0 a ≤ gridCoord x0 b := by
  simp only [gridCoord, gridStep, gridN, Nat.reduceSub, Rat.natCast_ofNat]
  grind

theorem gridCoord_bounds (x0 : Int) (a : Rat) : 0 ≤ gridCoord x0 a ∧ gridCoord x0 a ≤ 300 := by
  simp only [gridCoord, gridStep, gridN, Nat.reduceSub, Rat.natCast_ofNat]
  grind

theorem square_mono {g g' : Rat} (h : g ≤ g') : square g ≤ square g' := by
  have := Rat.floor_monotone h
  unfold square; omega

/-- The grid square's local coordinate `g - square g` lies in `[0, 1]`. -/
theorem square_frac {g : Rat} (h0 : 0 ≤ g) (h1 : g ≤ 300) : 0 ≤ g - (square g : Rat) ∧ g - (square g : Rat) ≤ 1 := by
  have hf := Rat.floor_le g
  have hl := Rat.lt_floor_add_one g
  have hf0 : (0 : Int) ≤ g.floor := Rat.le_floor_iff.mpr (by simpa using h0)
  have hsq : ((square g : Nat) : Int) = min g.floor 299 := by unfold square gridN; omega
  have hcast : ((square g : Nat) : Rat) = ((min g.floor 299 : Int) : Rat) := by
    rw [← hsq, Rat.intCast_natCast]
  rw [hcast]
  by_cases hm : g.floor ≤ 299
  · rw [Int.min_eq_left hm]
    simp only [Rat.intCast_add] at hl
    constructor <;> grind
  · have hm' : (300 : Int) ≤ g.floor := by omega
    rw [Int.min_eq_right (by omega)]
    have : ((300 : Int) : Rat) ≤ g := Rat.le_trans (Rat.intCast_le_intCast.mpr hm') hf
    constructor <;> grind

/-- Linear interpolation over a triangle stays below the highest corner. -/
theorem interp_le {a b c d M u v : Rat} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha : a ≤ M)
    (hb : b ≤ M) (hc : c ≤ M) (hd : d ≤ M) :
    (if v ≤ u then a + u * (b - a) + v * (d - b) else a + v * (c - a) + u * (d - c)) ≤ M := by
  split
  · have h1 : 0 ≤ (1 - u) * (M - a) := Rat.mul_nonneg (by grind) (by grind)
    have h2 : 0 ≤ (u - v) * (M - b) := Rat.mul_nonneg (by grind) (by grind)
    have h3 : 0 ≤ v * (M - d) := Rat.mul_nonneg hv0 (by grind)
    grind
  · have h1 : 0 ≤ (1 - v) * (M - a) := Rat.mul_nonneg (by grind) (by grind)
    have h2 : 0 ≤ (v - u) * (M - c) := Rat.mul_nonneg (by grind) (by grind)
    have h3 : 0 ≤ u * (M - d) := Rat.mul_nonneg hu0 (by grind)
    grind

theorem nodeI_eq (i j : Nat) : nodeI i j = (node i j * S).ceil := by
  unfold nodeI node terrainI
  by_cases h : j * gridN + i < terrain.size
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- A node lies below the top of any square whose top bounds it in units. -/
theorem node_le_top {a b i j : Nat} (h : nodeI a b ≤ squareTop i j) : node a b ≤ (squareTop i j : Rat) / S := by
  have h1 : node a b * S ≤ (nodeI a b : Rat) := by rw [nodeI_eq]; exact Rat.le_ceil
  have h2 : (nodeI a b : Rat) ≤ (squareTop i j : Rat) := Rat.intCast_le_intCast.mpr h
  simp only [S] at *
  grind

theorem terrainAt_le (x y : Rat) :
    terrainAt x y * S ≤ (squareTop (square (gridCoord gridX0 x)) (square (gridCoord gridY0 y)) : Rat) := by
  obtain ⟨gx0, gx1⟩ := gridCoord_bounds gridX0 x
  obtain ⟨gy0, gy1⟩ := gridCoord_bounds gridY0 y
  obtain ⟨u0, u1⟩ := square_frac gx0 gx1
  obtain ⟨v0, v1⟩ := square_frac gy0 gy1
  unfold terrainAt
  dsimp only
  generalize gridCoord gridX0 x = gx at *
  generalize gridCoord gridY0 y = gy at *
  generalize square gx = i at *
  generalize square gy = j at *
  have hle := interp_le u0 u1 v0 v1 (node_le_top (a := i) (b := j) (i := i) (j := j) (by unfold squareTop; omega))
    (node_le_top (a := i + 1) (b := j) (i := i) (j := j) (by unfold squareTop; omega))
    (node_le_top (a := i) (b := j + 1) (i := i) (j := j) (by unfold squareTop; omega))
    (node_le_top (a := i + 1) (b := j + 1) (i := i) (j := j) (by unfold squareTop; omega))
  have h2 := Rat.mul_le_mul_of_nonneg_right hle (show (0 : Rat) ≤ S by unfold S; decide)
  have h3 : (squareTop i j : Rat) / S * S = squareTop i j := by simp only [S]; grind
  rw [h3] at h2
  exact h2

theorem terrain_case {xl xh yl yh zl : Int} (hc : terrainClear xl xh yl yh zl = true) {px py pz : Rat}
    (wx1 : (xl : Rat) ≤ px * S) (wx2 : px * S ≤ (xh : Rat)) (wy1 : (yl : Rat) ≤ py * S) (wy2 : py * S ≤ (yh : Rat))
    (wz1 : (zl : Rat) ≤ pz * S) (ht : pz ≤ terrainAt px py) : False := by
  have dx1 : (xl : Rat) / S ≤ px := by simp only [S] at *; grind
  have dx2 : px ≤ (xh : Rat) / S := by simp only [S] at *; grind
  have dy1 : (yl : Rat) / S ≤ py := by simp only [S] at *; grind
  have dy2 : py ≤ (yh : Rat) / S := by simp only [S] at *; grind
  have ax := square_mono (gridCoord_mono gridX0 dx1)
  have bx := square_mono (gridCoord_mono gridX0 dx2)
  have ay := square_mono (gridCoord_mono gridY0 dy1)
  have by' := square_mono (gridCoord_mono gridY0 dy2)
  have hi : square (gridCoord gridX0 px) ∈
      List.range' (squareOf gridX0 xl) (squareOf gridX0 xh + 1 - squareOf gridX0 xl) := by
    unfold squareOf
    exact List.mem_range'.mpr ⟨square (gridCoord gridX0 px) - square (gridCoord gridX0 ((xl : Rat) / S)),
      by omega, by omega⟩
  have hj : square (gridCoord gridY0 py) ∈
      List.range' (squareOf gridY0 yl) (squareOf gridY0 yh + 1 - squareOf gridY0 yl) := by
    unfold squareOf
    exact List.mem_range'.mpr ⟨square (gridCoord gridY0 py) - square (gridCoord gridY0 ((yl : Rat) / S)),
      by omega, by omega⟩
  simp only [terrainClear, List.all_eq_true, decide_eq_true_eq] at hc
  have htop := Rat.intCast_lt_intCast.mpr (hc _ hi _ hj)
  have hle := terrainAt_le px py
  have hS : (0 : Rat) ≤ S := by unfold S; decide
  have hmul : pz * S ≤ terrainAt px py * S := Rat.mul_le_mul_of_nonneg_right ht hS
  grind

/-- **The cube test is sound**: if it passes, no point of the airframe envelope is solid. -/
theorem clearCube_sound (e : Float) (p : Plane) : clearCube e p = true → ¬ Crash p := by
  intro hc hcr
  unfold clearCube at hc
  unfold Crash at hcr
  cases hp : exactPos p with
  | none => simp [hp] at hc
  | some pos =>
    obtain ⟨x, y, z⟩ := pos
    simp only [hp, Bool.and_eq_true] at hc hcr
    obtain ⟨ht, hb⟩ := hc
    obtain ⟨dx, dy, dz, h1, h2, h3, h4, h5, h6, hs⟩ := hcr
    have hk : (96 : Rat) ≤ (((keepBase + extraUnits e : Nat) : Int) : Rat) := by
      have : (96 : Int) ≤ ((keepBase + extraUnits e : Nat) : Int) := by simp [keepBase]; omega
      exact Rat.intCast_le_intCast.mpr this
    obtain ⟨wx1, wx2⟩ := window x dx _ h1 h2 hk
    obtain ⟨wy1, wy2⟩ := window y dy _ h3 h4 hk
    obtain ⟨wz1, wz2⟩ := window z dz _ h5 h6 hk
    rcases hs with ⟨b, hbm, b1, b2, b3, b4, b5, b6⟩ | hter
    · exact box_case hb wx1 wx2 wy1 wy2 wz1 wz2 hbm b1 b2 b3 b4 b5 b6
    · exact terrain_case ht wx1 wx2 wy1 wy2 wz1 hter

/-- A plane whose reported position is `(x, y, z)` (map metres), for checks. -/
def planeAt (x y z : Float) : Plane := { st := CityJsb.template, ob := ⟨#[y, x, z]⟩, ox := 0, oy := 0 }

#guard clearCube 0 (planeAt (-120) (-180) 60) && !clearCube 0 (planeAt 63 63 300) &&
  !clearCube 0 (planeAt (-120) (-180) 5)

/-! ### The clearance test against the spec's airframe (`CityGate.clear_spec_sound`)

The positions are the plant's own reported ones (`CitySafety.report`), decoded exactly, as the spec places the
airframe. Every airframe point's offset from the reported CG is bounded per map axis by the row sums of
`|Tb2l| · |Ts2b| · M`, where `M` bounds `|r - cg|` per body axis over the 20 points; the box around the CG, widened by
2.5 m plus `extra`, must meet no building and stay above the terrain. -/

/-- `|x|`. -/
def rabs (x : Rat) : Rat := max x (-x)

/-- Per-axis range (structural inches) of the 20 points of `CitySafety.airframe`, rounded outward. -/
def ptMinX : Rat := -119
def ptMaxX : Rat := 255
def ptMinY : Rat := -233
def ptMaxY : Rat := 233
def ptMinZ : Rat := -22
def ptMaxZ : Rat := 91

/-- Every airframe point decodes and lies in that range (a constant). -/
def ptsOK : Bool := (CitySafety.contactPoints ++ CitySafety.flightGearPoints).all fun r =>
  match CitySafety.ratOf r.x, CitySafety.ratOf r.y, CitySafety.ratOf r.z with
  | some x, some y, some z => decide (ptMinX ≤ x ∧ x ≤ ptMaxX ∧ ptMinY ≤ y ∧ y ≤ ptMaxY ∧ ptMinZ ≤ z ∧ z ≤ ptMaxZ)
  | _, _, _ => false

/-- The structural-to-body matrix, decoded (a constant). -/
def ts2bL : Option (List Rat) := JsbExact.Gen.Ts2b.toList.mapM CitySafety.ratOf

/-- `CitySafety.mulRows` with every entry's absolute value. -/
def absRows (m : List Rat) (v : Rat × Rat × Rat) : Rat × Rat × Rat := CitySafety.mulRows (m.map rabs) v

/-- Keep-out margin beyond the airframe's bounding box (units): 2.5 m. -/
def keepSpec : Nat := 40

/-- The map box `[xlo, xhi] × [ylo, yhi] × [zlo, zhi]` (m), widened by `k` units, meets no building and stays above
the terrain. -/
def boxClear (k : Int) (xlo xhi ylo yhi zlo zhi : Rat) : Bool :=
  terrainClear ((xlo * S).floor - k) ((xhi * S).ceil + k) ((ylo * S).floor - k) ((yhi * S).ceil + k)
      ((zlo * S).floor - k) &&
    boxesClear ((xlo * S).floor - k) ((xhi * S).ceil + k) ((ylo * S).floor - k) ((yhi * S).ceil + k)
      ((zlo * S).floor - k) ((zhi * S).ceil + k)

/-- The clearance test on the plant's reported pose; `none` (not clear) if a reported number is not finite. -/
def clearSpec (extra : Float) (s : JsbExact.State Float) : Option Bool := do
  let rep := CitySafety.report s
  let ts ← ts2bL
  let tb ← [rep.tb2l.a11, rep.tb2l.a12, rep.tb2l.a13, rep.tb2l.a21, rep.tb2l.a22, rep.tb2l.a23,
    rep.tb2l.a31, rep.tb2l.a32, rep.tb2l.a33].mapM CitySafety.ratOf
  let cx ← CitySafety.ratOf s.cg.x
  let cy ← CitySafety.ratOf s.cg.y
  let cz ← CitySafety.ratOf s.cg.z
  let ly ← CitySafety.ratOf rep.loc.y
  let lz ← CitySafety.ratOf rep.loc.z
  let h ← CitySafety.ratOf rep.hsl
  let _ ← CitySafety.sinkRate s
  let m := (max (ptMaxX - cx) (cx - ptMinX), max (ptMaxY - cy) (cy - ptMinY), max (ptMaxZ - cz) (cz - ptMinZ))
  let dd := absRows tb (absRows ts m)
  let k : Int := keepSpec + extraUnits extra
  return ptsOK && boxClear k ((ly - dd.2.1) * CitySafety.ft) ((ly + dd.2.1) * CitySafety.ft)
    ((lz - dd.1) * CitySafety.ft) ((lz + dd.1) * CitySafety.ft)
    ((h - dd.2.2) * CitySafety.ft + 9) ((h + dd.2.2) * CitySafety.ft + 9)

/-- **The clearance test** the gate runs on every frame of every rollout: the spec's airframe, placed by the plant's
reported pose, is boxed and the box (2.5 m + `extra` wider) meets no building and stays above the terrain. -/
def clearAt (extra : Float) (p : Plane) : Bool := (clearSpec extra p.st).getD false

-- the box part: a level aircraft (±6 m, ±1.5 m) mid-street is clear, one inside the tallest tower is not
#guard boxClear 40 (-126) (-114) (-186) (-174) (117 / 2) (123 / 2) && !boxClear 40 57 69 57 69 (597 / 2) (603 / 2)

end CityGate
