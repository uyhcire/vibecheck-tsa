import CityGate.Map
import CityGate.Plant
import VcFilter.Exact
import Spec.CitySafety

/-! What a crash is (trusted surface), the clearance test the gate runs on every frame of every rollout, and its
soundness (`clear_sound`). -/

namespace CityGate

/-! ### What a crash is (trusted surface) -/

/-- Terrain height (m) at grid vertex `(i, j)` of `M`: `x = M.x0 + i · gridStep`, `y = M.y0 + j · gridStep`. -/
def GateMap.node (M : GateMap) (i j : Nat) : Rat := M.terrain.getD (j * M.nx + i) 0

/-- Grid coordinate of `x` (m) along an axis of `n` vertices starting at `x0`, clamped to `[0, n - 1]`. -/
def gridCoordN (n : Nat) (x0 : Int) (x : Rat) : Rat := max 0 (min ((n - 1 : Nat) : Rat) ((x - x0) / (gridStep : Rat)))

/-- The grid square (of `n` vertices) containing grid coordinate `g` (the last square for the far edge). -/
def squareN (n : Nat) (g : Rat) : Nat := min g.floor.toNat (n - 2)

/-- Terrain height (m) at map point `(x, y)`, as `data/map.json` defines it: positions outside the grid clamp to its
edge, and each grid square splits along its south-west to north-east diagonal and interpolates linearly. -/
def GateMap.terrainAt (M : GateMap) (x y : Rat) : Rat :=
  let gx := gridCoordN M.nx M.x0 x
  let gy := gridCoordN M.ny M.y0 y
  let i := squareN M.nx gx
  let j := squareN M.ny gy
  let u := gx - i
  let v := gy - j
  if v ≤ u then M.node i j + u * (M.node (i + 1) j - M.node i j) + v * (M.node (i + 1) (j + 1) - M.node (i + 1) j)
  else M.node i j + v * (M.node i (j + 1) - M.node i j) + u * (M.node (i + 1) (j + 1) - M.node i (j + 1))

/-- Map point `(x, y, z)` (m) is solid on `M`: inside a building box (closed) or at or below the terrain surface. -/
def GateMap.Solid (M : GateMap) (x y z : Rat) : Prop :=
  (∃ k < M.nb, (M.box k).xmin ≤ x ∧ x ≤ (M.box k).xmax ∧ (M.box k).ymin ≤ y ∧ y ≤ (M.box k).ymax ∧
    (M.box k).zmin ≤ z ∧ z ≤ (M.box k).zmax) ∨
    z ≤ M.terrainAt x y

/-- Half-size (m) of the airframe envelope. -/
def envHalf : Rat := 6

/-- The aircraft's exact map position (m), as the spec places the CG (`CitySafety.mapPoint`): the plant's reported
CG (`CitySafety.report`: east = ECEF y, north = ECEF z, up = altitude above sea level, ft) read exactly, converted
to metres in `Rat`, plus the map offset `(ox, oy)`; `none` if a number involved is not finite. -/
def exactPos (p : Plane) : Option (Rat × Rat × Rat) := do
  let r := CitySafety.report p.st
  pure ((← CitySafety.ratOf p.ox) + (← CitySafety.ratOf r.loc.y) * CitySafety.ft,
    (← CitySafety.ratOf p.oy) + (← CitySafety.ratOf r.loc.z) * CitySafety.ft,
    (← CitySafety.ratOf r.hsl) * CitySafety.ft)

/-- **A crash on `M`**: some point of the airframe envelope is solid, or the position is not finite. The envelope is
the cube of half-size `envHalf` = 6 m around the aircraft's reference point, edges along the map axes. It contains
every point within 6 m of the reference point, which covers the whole C172 (11 m span, 8.3 m long) at any attitude
provided the airframe lies within 6 m of that point. This is conservative relative to the contact shape still
open in `docs/safety-objective.md` (the hull of the 7 contact points lies inside it), so no crash here means no
contact there. -/
def CrashOn (M : GateMap) (p : Plane) : Prop :=
  match exactPos p with
  | some (x, y, z) => ∃ dx dy dz : Rat, -envHalf ≤ dx ∧ dx ≤ envHalf ∧ -envHalf ≤ dy ∧ dy ≤ envHalf ∧
      -envHalf ≤ dz ∧ dz ≤ envHalf ∧ M.Solid (x + dx) (y + dy) (z + dz)
  | none => True

/-! The default city's names (`gridMap`). -/

def node (i j : Nat) : Rat := gridMap.node i j
def gridCoord (x0 : Int) (x : Rat) : Rat := gridCoordN gridN x0 x
def square (g : Rat) : Nat := squareN gridN g
def terrainAt (x y : Rat) : Rat := gridMap.terrainAt x y
def Solid (x y z : Rat) : Prop := gridMap.Solid x y z
/-- **A crash** in the default city. -/
def Crash (p : Plane) : Prop := CrashOn gridMap p

/-! ### The clearance test

Fixed point at 16 units per metre, all in `Int`. The aircraft's position is rounded outward, the map is rounded
outward once (`roundOut`, `terrI`), and a keep-out cube of half-size 8.5 m (the Rust gate's 4.5 m body radius + 4 m
margin) plus `extra` must contain no box (looked up in an index of 32 m cells) and stay above every terrain node of
the grid squares under it. -/

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

/-- The box index: `cx × cy` cells of `sz` units, cell `(0, 0)` starting at `(ox, oy)` (units); coordinates
outside clamp to the edge cells. -/
structure CellIndex where
  ox : Int
  oy : Int
  cx : Nat
  cy : Nat
  sz : Nat

/-- Index cell of a coordinate `v` (units) along an axis of `c` cells of `sz` starting at `o`, clamped to the edge
cells. -/
def cellIdxN (o : Int) (c sz : Nat) (v : Int) : Nat := min ((v - o) / (sz : Int)).toNat (c - 1)

/-- The boxes rounded outward to units. -/
def GateMap.boxesI (M : GateMap) : List (Box Int) := (List.range M.nb).map fun k => roundOut (M.box k)

/-- `b` added to the list of every index cell its x- and y-ranges meet. -/
def insertBox (I : CellIndex) (acc : Array (List (Box Int))) (b : Box Int) : Array (List (Box Int)) :=
  (List.range' (cellIdxN I.oy I.cy I.sz b.ymin) (cellIdxN I.oy I.cy I.sz b.ymax + 1 - cellIdxN I.oy I.cy I.sz b.ymin)).foldl
    (fun acc j => (List.range' (cellIdxN I.ox I.cx I.sz b.xmin) (cellIdxN I.ox I.cx I.sz b.xmax + 1 - cellIdxN I.ox I.cx I.sz b.xmin)).foldl
      (fun acc i => acc.modify (j * I.cx + i) (b :: ·)) acc) acc

/-- The index: for cell `(i, j)`, at `j * cx + i`, every box whose x- and y-ranges meet it (and possibly others). -/
def cellBoxesOf (bs : List (Box Int)) (I : CellIndex) : Array (List (Box Int)) :=
  bs.foldl (insertBox I) (Array.replicate (I.cy * I.cx) [])

/-- A map with what the clearance test reads precomputed: its boxes rounded outward and indexed, its terrain heights
rounded up to units. Not trusted: the fields' equations tie them to the map. -/
structure GateGeo where
  map : GateMap
  idx : CellIndex
  cells : Array (List (Box Int))
  terrI : Array Int
  cells_eq : cells = cellBoxesOf map.boxesI idx
  terrI_eq : terrI = map.terrain.map fun q => (q * S).ceil
  nx2 : 2 ≤ map.nx
  ny2 : 2 ≤ map.ny
  cx1 : 0 < idx.cx
  cy1 : 0 < idx.cy
  sz1 : 0 < idx.sz

/-- `M` with its index and rounded terrain computed, from its boxes rounded outward (`bs`, however computed). -/
def GateGeo.ofBoxesI (M : GateMap) (I : CellIndex) (bs : List (Box Int)) (hb : bs = M.boxesI) (h1 : 2 ≤ M.nx)
    (h2 : 2 ≤ M.ny) (h3 : 0 < I.cx) (h4 : 0 < I.cy) (h5 : 0 < I.sz) : GateGeo :=
  ⟨M, I, cellBoxesOf bs I, M.terrain.map fun q => (q * S).ceil, by rw [hb], rfl, h1, h2, h3, h4, h5⟩

/-- `[lo, hi]` meets `[a, b]`. -/
def meets (lo hi a b : Int) : Bool := a ≤ hi && lo ≤ b

/-- No box of `G` meets the keep-out box `[xl, xh] × [yl, yh] × [zl, zh]` (units). -/
def GateGeo.boxesClear (G : GateGeo) (xl xh yl yh zl zh : Int) : Bool :=
  let I := G.idx
  (List.range' (cellIdxN I.ox I.cx I.sz xl) (cellIdxN I.ox I.cx I.sz xh + 1 - cellIdxN I.ox I.cx I.sz xl)).all fun i =>
    (List.range' (cellIdxN I.oy I.cy I.sz yl) (cellIdxN I.oy I.cy I.sz yh + 1 - cellIdxN I.oy I.cy I.sz yl)).all fun j =>
      (G.cells.getD (j * I.cx + i) []).all fun b =>
        !(meets xl xh b.xmin b.xmax && meets yl yh b.ymin b.ymax && meets zl zh b.zmin b.zmax)

def GateGeo.nodeI (G : GateGeo) (i j : Nat) : Int := G.terrI.getD (j * G.map.nx + i) 0

/-- Highest node (units) of grid square `(i, j)`. -/
def GateGeo.squareTop (G : GateGeo) (i j : Nat) : Int :=
  max (max (G.nodeI i j) (G.nodeI (i + 1) j)) (max (G.nodeI i (j + 1)) (G.nodeI (i + 1) (j + 1)))

/-- Grid square (of `n` vertices from `x0`) under the coordinate `v` (units). -/
def squareOfN (n : Nat) (x0 : Int) (v : Int) : Nat := squareN n (gridCoordN n x0 ((v : Rat) / S))

/-- Every grid square under `[xl, xh] × [yl, yh]` (units) has all its nodes below `zl`. -/
def GateGeo.terrainClear (G : GateGeo) (xl xh yl yh zl : Int) : Bool :=
  let M := G.map
  (List.range' (squareOfN M.nx M.x0 xl) (squareOfN M.nx M.x0 xh + 1 - squareOfN M.nx M.x0 xl)).all fun i =>
    (List.range' (squareOfN M.ny M.y0 yl) (squareOfN M.ny M.y0 yh + 1 - squareOfN M.ny M.y0 yl)).all fun j =>
      G.squareTop i j < zl

/-- The clearance test on `G`: the keep-out cube of half-size 8.5 m + `extra` around the aircraft meets no building
and stays above the terrain. -/
def clearAtOn (G : GateGeo) (extra : Float) (p : Plane) : Bool :=
  match exactPos p with
  | some (x, y, z) =>
    let k : Int := keepBase + extraUnits extra
    G.terrainClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k) ((z * S).floor - k) &&
      G.boxesClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k)
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

theorem cellIdxN_mono (o : Int) (c : Nat) {sz : Nat} (hs : 0 < sz) {a b : Int} (h : a ≤ b) :
    cellIdxN o c sz a ≤ cellIdxN o c sz b := by
  unfold cellIdxN
  have : (a - o) / (sz : Int) ≤ (b - o) / (sz : Int) := Int.ediv_le_ediv (by omega) (by omega)
  omega

theorem cellIdxN_lt (o : Int) {c : Nat} (sz : Nat) (hc : 0 < c) (a : Int) : cellIdxN o c sz a < c := by
  unfold cellIdxN; omega

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (d : α) {k : Nat} (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD, hk]

theorem mem_modify {acc : Array (List (Box Int))} {k i : Nat} {b b' : Box Int} (h : b' ∈ acc.getD k []) :
    b' ∈ (acc.modify i (b :: ·)).getD k [] := by
  rw [Array.getD_eq_getD_getElem?] at h ⊢
  rw [Array.getElem?_modify]
  split
  · cases hx : acc[k]? with
    | none => simp [hx] at h
    | some l => simp only [hx, Option.map_some, Option.getD_some] at h ⊢; exact List.mem_cons_of_mem _ h
  · exact h

theorem mem_modify_self {acc : Array (List (Box Int))} {k : Nat} {b : Box Int} (hk : k < acc.size) :
    b ∈ (acc.modify k (b :: ·)).getD k [] := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hk]

theorem size_foldl_modify (b : Box Int) (j c : Nat) :
    ∀ (l : List Nat) (acc : Array (List (Box Int))),
      (l.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc).size = acc.size
  | [], _ => rfl
  | i :: l, acc => by simp only [List.foldl_cons]; rw [size_foldl_modify b j c l, Array.size_modify]

theorem mem_foldl_modify (b : Box Int) (j c : Nat) {k : Nat} {b' : Box Int} :
    ∀ (l : List Nat) (acc : Array (List (Box Int))), b' ∈ acc.getD k [] →
      b' ∈ (l.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc).getD k []
  | [], _, h => h
  | i :: l, acc, h => by simp only [List.foldl_cons]; exact mem_foldl_modify b j c l _ (mem_modify h)

theorem mem_foldl_modify_self (b : Box Int) (j c : Nat) {i : Nat} :
    ∀ (l : List Nat) (acc : Array (List (Box Int))), i ∈ l → j * c + i < acc.size →
      b ∈ (l.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc).getD (j * c + i) []
  | [], _, h, _ => absurd h List.not_mem_nil
  | i' :: l, acc, h, hs => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_modify b j c l _ (mem_modify_self hs)
    · exact mem_foldl_modify_self b j c l _ h (by rw [Array.size_modify]; exact hs)

theorem size_foldl_rows (b : Box Int) (c : Nat) (cols : List Nat) :
    ∀ (rows : List Nat) (acc : Array (List (Box Int))),
      (rows.foldl (fun acc j => cols.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc) acc).size = acc.size
  | [], _ => rfl
  | j :: l, acc => by simp only [List.foldl_cons]; rw [size_foldl_rows b c cols l, size_foldl_modify]

theorem mem_foldl_rows (b : Box Int) (c : Nat) (cols : List Nat) {k : Nat} {b' : Box Int} :
    ∀ (rows : List Nat) (acc : Array (List (Box Int))), b' ∈ acc.getD k [] →
      b' ∈ (rows.foldl (fun acc j => cols.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc) acc).getD k []
  | [], _, h => h
  | j :: l, acc, h => by simp only [List.foldl_cons]; exact mem_foldl_rows b c cols l _ (mem_foldl_modify b j c _ _ h)

theorem mem_foldl_rows_self (b : Box Int) (c : Nat) (cols : List Nat) {i j : Nat} (hi : i ∈ cols) :
    ∀ (rows : List Nat) (acc : Array (List (Box Int))), j ∈ rows → j * c + i < acc.size →
      b ∈ (rows.foldl (fun acc j => cols.foldl (fun acc i => acc.modify (j * c + i) (b :: ·)) acc) acc).getD (j * c + i) []
  | [], _, h, _ => absurd h List.not_mem_nil
  | j' :: l, acc, h, hs => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_rows b c cols l _ (mem_foldl_modify_self b j c cols acc hi hs)
    · exact mem_foldl_rows_self b c cols hi l _ h (by rw [size_foldl_modify]; exact hs)

theorem size_insertBox (I : CellIndex) (b : Box Int) (acc : Array (List (Box Int))) :
    (insertBox I acc b).size = acc.size := size_foldl_rows _ _ _ _ _

theorem mem_insertBox {I : CellIndex} {b b' : Box Int} {k : Nat} (acc : Array (List (Box Int)))
    (h : b' ∈ acc.getD k []) : b' ∈ (insertBox I acc b).getD k [] := mem_foldl_rows _ _ _ _ _ h

theorem mem_insertBox_self {I : CellIndex} {b : Box Int} {i j : Nat}
    (hi1 : cellIdxN I.ox I.cx I.sz b.xmin ≤ i) (hi2 : i ≤ cellIdxN I.ox I.cx I.sz b.xmax)
    (hj1 : cellIdxN I.oy I.cy I.sz b.ymin ≤ j) (hj2 : j ≤ cellIdxN I.oy I.cy I.sz b.ymax) (acc : Array (List (Box Int)))
    (hs : j * I.cx + i < acc.size) : b ∈ (insertBox I acc b).getD (j * I.cx + i) [] :=
  mem_foldl_rows_self b I.cx _
    (List.mem_range'.mpr ⟨i - cellIdxN I.ox I.cx I.sz b.xmin, by omega, by omega⟩) _ acc
    (List.mem_range'.mpr ⟨j - cellIdxN I.oy I.cy I.sz b.ymin, by omega, by omega⟩) hs

theorem mem_cellBoxesOf {bs : List (Box Int)} {I : CellIndex} {b : Box Int} (hb : b ∈ bs) {i j : Nat}
    (hi1 : cellIdxN I.ox I.cx I.sz b.xmin ≤ i) (hi2 : i ≤ cellIdxN I.ox I.cx I.sz b.xmax)
    (hj1 : cellIdxN I.oy I.cy I.sz b.ymin ≤ j) (hj2 : j ≤ cellIdxN I.oy I.cy I.sz b.ymax)
    (hi : i < I.cx) (hj : j < I.cy) : b ∈ (cellBoxesOf bs I).getD (j * I.cx + i) [] := by
  have hk : j * I.cx + i < I.cy * I.cx := by
    have : (j + 1) * I.cx ≤ I.cy * I.cx := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this; omega
  unfold cellBoxesOf
  have hkeep : ∀ (l : List (Box Int)) (acc : Array (List (Box Int))), b ∈ acc.getD (j * I.cx + i) [] →
      b ∈ (l.foldl (insertBox I) acc).getD (j * I.cx + i) [] := by
    intro l; induction l with
    | nil => intro _ h; exact h
    | cons c l ih => intro acc h; simp only [List.foldl_cons]; exact ih _ (mem_insertBox _ h)
  have hs0 : (Array.replicate (I.cy * I.cx) ([] : List (Box Int))).size = I.cy * I.cx := Array.size_replicate
  have main : ∀ (l : List (Box Int)) (acc : Array (List (Box Int))), b ∈ l → j * I.cx + i < acc.size →
      b ∈ (l.foldl (insertBox I) acc).getD (j * I.cx + i) [] := by
    intro l; induction l with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons c l ih =>
      intro acc h hs; simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact hkeep l _ (mem_insertBox_self hi1 hi2 hj1 hj2 acc hs)
      · exact ih _ h (by rw [size_insertBox]; exact hs)
  exact main bs _ hb (by rw [hs0]; exact hk)

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

theorem box_case {G : GateGeo} {xl xh yl yh zl zh : Int} (hc : G.boxesClear xl xh yl yh zl zh = true) {px py pz : Rat}
    (wx1 : (xl : Rat) ≤ px * S) (wx2 : px * S ≤ (xh : Rat)) (wy1 : (yl : Rat) ≤ py * S) (wy2 : py * S ≤ (yh : Rat))
    (wz1 : (zl : Rat) ≤ pz * S) (wz2 : pz * S ≤ (zh : Rat)) {k : Nat} (hk : k < G.map.nb)
    (h1 : (G.map.box k).xmin ≤ px) (h2 : px ≤ (G.map.box k).xmax) (h3 : (G.map.box k).ymin ≤ py)
    (h4 : py ≤ (G.map.box k).ymax) (h5 : (G.map.box k).zmin ≤ pz) (h6 : pz ≤ (G.map.box k).zmax) : False := by
  have hbI : roundOut (G.map.box k) ∈ G.map.boxesI := List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  generalize G.map.box k = b at hbI h1 h2 h3 h4 h5 h6
  obtain ⟨rx1, rx2⟩ := roundOut_bounds h1 h2
  obtain ⟨ry1, ry2⟩ := roundOut_bounds h3 h4
  obtain ⟨rz1, rz2⟩ := roundOut_bounds h5 h6
  obtain ⟨mx1, mx2, mx3⟩ := meets_of wx1 wx2 rx1 rx2
  obtain ⟨my1, my2, my3⟩ := meets_of wy1 wy2 ry1 ry2
  obtain ⟨mz1, mz2, _⟩ := meets_of wz1 wz2 rz1 rz2
  have hxx : xl ≤ xh := Rat.intCast_le_intCast.mp (Rat.le_trans wx1 wx2)
  have hyy : yl ≤ yh := Rat.intCast_le_intCast.mp (Rat.le_trans wy1 wy2)
  have hcx := G.cx1
  have hcy := G.cy1
  have hsz := G.sz1
  simp only [GateGeo.boxesClear, List.all_eq_true] at hc
  rw [G.cells_eq] at hc
  generalize G.map.boxesI = bs at hc hbI
  generalize G.idx = I at hc hcx hcy hsz
  have cx1 := cellIdxN_mono I.ox I.cx hsz (a := xl) (b := max xl (b.xmin * S).floor) (by omega)
  have cx2 := cellIdxN_mono I.ox I.cx hsz (a := max xl (b.xmin * S).floor) (b := xh) (by omega)
  have cx3 := cellIdxN_mono I.ox I.cx hsz (a := (b.xmin * S).floor) (b := max xl (b.xmin * S).floor) (by omega)
  have cx4 := cellIdxN_mono I.ox I.cx hsz (a := max xl (b.xmin * S).floor) (b := (b.xmax * S).ceil) (by omega)
  have cy1 := cellIdxN_mono I.oy I.cy hsz (a := yl) (b := max yl (b.ymin * S).floor) (by omega)
  have cy2 := cellIdxN_mono I.oy I.cy hsz (a := max yl (b.ymin * S).floor) (b := yh) (by omega)
  have cy3 := cellIdxN_mono I.oy I.cy hsz (a := (b.ymin * S).floor) (b := max yl (b.ymin * S).floor) (by omega)
  have cy4 := cellIdxN_mono I.oy I.cy hsz (a := max yl (b.ymin * S).floor) (b := (b.ymax * S).ceil) (by omega)
  have hmem := mem_cellBoxesOf hbI cx3 cx4 cy3 cy4 (cellIdxN_lt _ _ hcx _) (cellIdxN_lt _ _ hcy _)
  have hi : cellIdxN I.ox I.cx I.sz (max xl (b.xmin * S).floor) ∈
      List.range' (cellIdxN I.ox I.cx I.sz xl) (cellIdxN I.ox I.cx I.sz xh + 1 - cellIdxN I.ox I.cx I.sz xl) :=
    List.mem_range'.mpr ⟨cellIdxN I.ox I.cx I.sz (max xl (b.xmin * S).floor) - cellIdxN I.ox I.cx I.sz xl, by omega, by omega⟩
  have hj : cellIdxN I.oy I.cy I.sz (max yl (b.ymin * S).floor) ∈
      List.range' (cellIdxN I.oy I.cy I.sz yl) (cellIdxN I.oy I.cy I.sz yh + 1 - cellIdxN I.oy I.cy I.sz yl) :=
    List.mem_range'.mpr ⟨cellIdxN I.oy I.cy I.sz (max yl (b.ymin * S).floor) - cellIdxN I.oy I.cy I.sz yl, by omega, by omega⟩
  have hno := hc _ hi _ hj _ hmem
  have hm : (meets xl xh (roundOut b).xmin (roundOut b).xmax && meets yl yh (roundOut b).ymin (roundOut b).ymax &&
      meets zl zh (roundOut b).zmin (roundOut b).zmax) = true := by
    simp [meets, roundOut, mx1, mx2, my1, my2, mz1, mz2]
  rw [hm] at hno
  exact absurd hno (by decide)

theorem gridCoordN_mono (n : Nat) (x0 : Int) {a b : Rat} (h : a ≤ b) : gridCoordN n x0 a ≤ gridCoordN n x0 b := by
  simp only [gridCoordN, gridStep, Rat.natCast_ofNat]
  grind

theorem gridCoordN_bounds (n : Nat) (x0 : Int) (a : Rat) :
    0 ≤ gridCoordN n x0 a ∧ gridCoordN n x0 a ≤ ((n - 1 : Nat) : Rat) := by
  have : (0 : Rat) ≤ ((n - 1 : Nat) : Rat) := by
    have := Rat.natCast_le_natCast.mpr (Nat.zero_le (n - 1)); simpa using this
  simp only [gridCoordN, gridStep, Rat.natCast_ofNat]
  grind

theorem squareN_mono (n : Nat) {g g' : Rat} (h : g ≤ g') : squareN n g ≤ squareN n g' := by
  have := Rat.floor_monotone h
  unfold squareN; omega

/-- The grid square's local coordinate `g - squareN n g` lies in `[0, 1]`. -/
theorem squareN_frac {n : Nat} (hn : 2 ≤ n) {g : Rat} (h0 : 0 ≤ g) (h1 : g ≤ ((n - 1 : Nat) : Rat)) :
    0 ≤ g - (squareN n g : Rat) ∧ g - (squareN n g : Rat) ≤ 1 := by
  have hf := Rat.floor_le g
  have hl := Rat.lt_floor_add_one g
  have hf0 : (0 : Int) ≤ g.floor := Rat.le_floor_iff.mpr (by simpa using h0)
  have hsq : ((squareN n g : Nat) : Int) = min g.floor ((n - 2 : Nat) : Int) := by unfold squareN; omega
  have hcast : ((squareN n g : Nat) : Rat) = ((min g.floor ((n - 2 : Nat) : Int) : Int) : Rat) := by
    rw [← hsq, Rat.intCast_natCast]
  rw [hcast]
  by_cases hm : g.floor ≤ ((n - 2 : Nat) : Int)
  · rw [Int.min_eq_left hm]
    simp only [Rat.intCast_add] at hl
    constructor <;> grind
  · have hm' : ((n - 1 : Nat) : Int) ≤ g.floor := by omega
    rw [Int.min_eq_right (by omega)]
    have h2 : (((n - 1 : Nat) : Int) : Rat) ≤ g := Rat.le_trans (Rat.intCast_le_intCast.mpr hm') hf
    have e : (((n - 1 : Nat) : Int) : Rat) = (((n - 2 : Nat) : Int) : Rat) + 1 := by
      rw [show ((n - 1 : Nat) : Int) = ((n - 2 : Nat) : Int) + 1 by omega, Rat.intCast_add]; rfl
    rw [Rat.intCast_natCast] at h2
    rw [Rat.intCast_natCast] at e
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

theorem nodeI_eq (G : GateGeo) (i j : Nat) : G.nodeI i j = (G.map.node i j * S).ceil := by
  unfold GateGeo.nodeI GateMap.node
  rw [G.terrI_eq]
  by_cases h : j * G.map.nx + i < G.map.terrain.size
  · simp [Array.getD, h]
  · simp [Array.getD, h]; rfl

/-- A node lies below the top of any square whose top bounds it in units. -/
theorem node_le_top {G : GateGeo} {a b i j : Nat} (h : G.nodeI a b ≤ G.squareTop i j) :
    G.map.node a b ≤ (G.squareTop i j : Rat) / S := by
  have h1 : G.map.node a b * S ≤ (G.nodeI a b : Rat) := by rw [nodeI_eq]; exact Rat.le_ceil
  have h2 : (G.nodeI a b : Rat) ≤ (G.squareTop i j : Rat) := Rat.intCast_le_intCast.mpr h
  simp only [S] at *
  grind

theorem terrainAt_le (G : GateGeo) (x y : Rat) :
    G.map.terrainAt x y * S ≤
      (G.squareTop (squareN G.map.nx (gridCoordN G.map.nx G.map.x0 x)) (squareN G.map.ny (gridCoordN G.map.ny G.map.y0 y)) : Rat) := by
  obtain ⟨gx0, gx1⟩ := gridCoordN_bounds G.map.nx G.map.x0 x
  obtain ⟨gy0, gy1⟩ := gridCoordN_bounds G.map.ny G.map.y0 y
  obtain ⟨u0, u1⟩ := squareN_frac G.nx2 gx0 gx1
  obtain ⟨v0, v1⟩ := squareN_frac G.ny2 gy0 gy1
  unfold GateMap.terrainAt
  dsimp only
  generalize gridCoordN G.map.nx G.map.x0 x = gx at *
  generalize gridCoordN G.map.ny G.map.y0 y = gy at *
  generalize squareN G.map.nx gx = i at *
  generalize squareN G.map.ny gy = j at *
  have hle := interp_le u0 u1 v0 v1 (node_le_top (G := G) (a := i) (b := j) (i := i) (j := j) (by unfold GateGeo.squareTop; omega))
    (node_le_top (G := G) (a := i + 1) (b := j) (i := i) (j := j) (by unfold GateGeo.squareTop; omega))
    (node_le_top (G := G) (a := i) (b := j + 1) (i := i) (j := j) (by unfold GateGeo.squareTop; omega))
    (node_le_top (G := G) (a := i + 1) (b := j + 1) (i := i) (j := j) (by unfold GateGeo.squareTop; omega))
  have h2 := Rat.mul_le_mul_of_nonneg_right hle (show (0 : Rat) ≤ S by unfold S; decide)
  have h3 : (G.squareTop i j : Rat) / S * S = G.squareTop i j := by simp only [S]; grind
  rw [h3] at h2
  exact h2

theorem terrain_case {G : GateGeo} {xl xh yl yh zl : Int} (hc : G.terrainClear xl xh yl yh zl = true) {px py pz : Rat}
    (wx1 : (xl : Rat) ≤ px * S) (wx2 : px * S ≤ (xh : Rat)) (wy1 : (yl : Rat) ≤ py * S) (wy2 : py * S ≤ (yh : Rat))
    (wz1 : (zl : Rat) ≤ pz * S) (ht : pz ≤ G.map.terrainAt px py) : False := by
  have dx1 : (xl : Rat) / S ≤ px := by simp only [S] at *; grind
  have dx2 : px ≤ (xh : Rat) / S := by simp only [S] at *; grind
  have dy1 : (yl : Rat) / S ≤ py := by simp only [S] at *; grind
  have dy2 : py ≤ (yh : Rat) / S := by simp only [S] at *; grind
  have ax := squareN_mono G.map.nx (gridCoordN_mono G.map.nx G.map.x0 dx1)
  have bx := squareN_mono G.map.nx (gridCoordN_mono G.map.nx G.map.x0 dx2)
  have ay := squareN_mono G.map.ny (gridCoordN_mono G.map.ny G.map.y0 dy1)
  have by' := squareN_mono G.map.ny (gridCoordN_mono G.map.ny G.map.y0 dy2)
  have hi : squareN G.map.nx (gridCoordN G.map.nx G.map.x0 px) ∈
      List.range' (squareOfN G.map.nx G.map.x0 xl) (squareOfN G.map.nx G.map.x0 xh + 1 - squareOfN G.map.nx G.map.x0 xl) := by
    unfold squareOfN
    exact List.mem_range'.mpr ⟨squareN G.map.nx (gridCoordN G.map.nx G.map.x0 px) -
      squareN G.map.nx (gridCoordN G.map.nx G.map.x0 ((xl : Rat) / S)), by omega, by omega⟩
  have hj : squareN G.map.ny (gridCoordN G.map.ny G.map.y0 py) ∈
      List.range' (squareOfN G.map.ny G.map.y0 yl) (squareOfN G.map.ny G.map.y0 yh + 1 - squareOfN G.map.ny G.map.y0 yl) := by
    unfold squareOfN
    exact List.mem_range'.mpr ⟨squareN G.map.ny (gridCoordN G.map.ny G.map.y0 py) -
      squareN G.map.ny (gridCoordN G.map.ny G.map.y0 ((yl : Rat) / S)), by omega, by omega⟩
  simp only [GateGeo.terrainClear, List.all_eq_true, decide_eq_true_eq] at hc
  have htop := Rat.intCast_lt_intCast.mpr (hc _ hi _ hj)
  have hle := terrainAt_le G px py
  have hS : (0 : Rat) ≤ S := by unfold S; decide
  have hmul : pz * S ≤ G.map.terrainAt px py * S := Rat.mul_le_mul_of_nonneg_right ht hS
  grind

/-- **The clearance test is sound** on any map: if it passes, no point of the airframe envelope is solid. -/
theorem clear_sound_on (G : GateGeo) (e : Float) (p : Plane) : clearAtOn G e p = true → ¬ CrashOn G.map p := by
  intro hc hcr
  unfold clearAtOn at hc
  unfold CrashOn at hcr
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
    rcases hs with ⟨kb, hkb, b1, b2, b3, b4, b5, b6⟩ | hter
    · exact box_case hb wx1 wx2 wy1 wy2 wz1 wz2 hkb b1 b2 b3 b4 b5 b6
    · exact terrain_case ht wx1 wx2 wy1 wy2 wz1 hter

/-! ### The default city -/

/-- The default city's box index: 100 × 100 cells of 32 m from (-1600 m, -1600 m). -/
def gridIdx : CellIndex := ⟨-25600, -25600, 100, 100, 512⟩

def gridGeo : GateGeo :=
  GateGeo.ofBoxesI gridMap gridIdx gridMap.boxesI rfl (by show 2 ≤ gridN; decide) (by show 2 ≤ gridN; decide)
    (by decide) (by decide) (by decide)

/-- The clearance test in the default city. -/
def clearAt (extra : Float) (p : Plane) : Bool := clearAtOn gridGeo extra p

/-- **The clearance test is sound** in the default city. -/
theorem clear_sound (e : Float) (p : Plane) : clearAt e p = true → ¬ Crash p :=
  clear_sound_on gridGeo e p

/-- `clearAt`'s test at the exact position `(x, y, z)` (m). -/
def clearXYZ (x y z : Rat) : Bool :=
  let k : Int := keepBase
  gridGeo.terrainClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k) ((z * S).floor - k) &&
    gridGeo.boxesClear ((x * S).floor - k) ((x * S).ceil + k) ((y * S).floor - k) ((y * S).ceil + k)
      ((z * S).floor - k) ((z * S).ceil + k)

#guard clearXYZ (-120) (-180) 60 && !clearXYZ 63 63 300 && !clearXYZ (-120) (-180) 5

end CityGate
