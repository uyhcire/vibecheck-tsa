/-! Obstacles (terrain and buildings) as a 2D max-height grid, with a maximum over a rectangle. -/

namespace Envelope3D

/-- `cells[j * nx + i]` bounds every obstacle over `[x0 + i·wx, +wx) × [y0 + j·wy, +wy)`; `beyond` bounds the rest. -/
structure Grid where
  x0 : Rat
  y0 : Rat
  wx : Rat
  wy : Rat
  nx : Nat
  ny : Nat
  cells : Array Rat
  beyond : Rat

namespace Grid

def cellX (G : Grid) (x : Rat) : Int := ((x - G.x0) / G.wx).floor

def cellY (G : Grid) (y : Rat) : Int := ((y - G.y0) / G.wy).floor

/-- Height bound of cell `(i, j)`. -/
def cellHeight (G : Grid) (i j : Int) : Rat :=
  if 0 ≤ i ∧ i < G.nx ∧ 0 ≤ j ∧ j < G.ny then G.cells.getD (j.toNat * G.nx + i.toNat) G.beyond
  else G.beyond

def heightAt (G : Grid) (x y : Rat) : Rat := G.cellHeight (G.cellX x) (G.cellY y)

def clampX (G : Grid) (i : Int) : Int := max (-1) (min i G.nx)

def clampY (G : Grid) (j : Int) : Int := max (-1) (min j G.ny)

def rowMax (G : Grid) (j i : Int) : Nat → Rat
  | 0 => G.cellHeight i j
  | n + 1 => max (G.cellHeight i j) (G.rowMax j (i + 1) n)

def rectMax (G : Grid) (i : Int) (ni : Nat) (j : Int) : Nat → Rat
  | 0 => G.rowMax j i ni
  | n + 1 => max (G.rowMax j i ni) (G.rectMax i ni (j + 1) n)

def maxOver (G : Grid) (xlo xhi ylo yhi : Rat) : Rat :=
  let i := G.clampX (G.cellX xlo)
  let i' := G.clampX (G.cellX xhi)
  let j := G.clampY (G.cellY ylo)
  let j' := G.clampY (G.cellY yhi)
  G.rectMax i (i' - i).toNat j (j' - j).toNat

theorem cellX_mono (G : Grid) (hw : 0 < G.wx) {x y : Rat} (h : x ≤ y) : G.cellX x ≤ G.cellX y := by
  unfold cellX
  apply Rat.floor_monotone
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hw))

theorem cellY_mono (G : Grid) (hw : 0 < G.wy) {x y : Rat} (h : x ≤ y) : G.cellY x ≤ G.cellY y := by
  unfold cellY
  apply Rat.floor_monotone
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hw))

theorem cellHeight_clampX (G : Grid) (i j : Int) : G.cellHeight (G.clampX i) j = G.cellHeight i j := by
  unfold cellHeight clampX
  split <;> split
  · have : max (-1) (min i (G.nx : Int)) = i := by omega
    rw [this]
  all_goals first | rfl | omega

theorem cellHeight_clampY (G : Grid) (i j : Int) : G.cellHeight i (G.clampY j) = G.cellHeight i j := by
  unfold cellHeight clampY
  split <;> split
  · have : max (-1) (min j (G.ny : Int)) = j := by omega
    rw [this]
  all_goals first | rfl | omega

theorem le_rowMax (G : Grid) (j : Int) : ∀ (n : Nat) (i k : Int), i ≤ k → k ≤ i + n →
    G.cellHeight k j ≤ G.rowMax j i n
  | 0, i, k, h1, h2 => by
    have : k = i := by omega
    subst this; exact Rat.le_refl
  | n + 1, i, k, h1, h2 => by
    simp only [rowMax]
    by_cases hk : k = i
    · subst hk; grind
    · have := le_rowMax G j n (i + 1) k (by omega) (by omega); grind

theorem rowMax_le (G : Grid) (j : Int) {M : Rat} : ∀ (n : Nat) (i : Int),
    (∀ k, i ≤ k → k ≤ i + n → G.cellHeight k j ≤ M) → G.rowMax j i n ≤ M
  | 0, i, h => h i (by omega) (by omega)
  | n + 1, i, h => by
    simp only [rowMax]
    have a := h i (by omega) (by omega)
    have b := rowMax_le G j n (i + 1) (fun k h1 h2 => h k (by omega) (by omega))
    grind

theorem le_rectMax (G : Grid) (i : Int) (ni : Nat) : ∀ (n : Nat) (j k l : Int), i ≤ k → k ≤ i + ni →
    j ≤ l → l ≤ j + n → G.cellHeight k l ≤ G.rectMax i ni j n
  | 0, j, k, l, h1, h2, h3, h4 => by
    have : l = j := by omega
    subst this; exact G.le_rowMax l ni i k h1 h2
  | n + 1, j, k, l, h1, h2, h3, h4 => by
    simp only [rectMax]
    by_cases hl : l = j
    · subst hl; have := G.le_rowMax l ni i k h1 h2; grind
    · have := le_rectMax G i ni n (j + 1) k l h1 h2 (by omega) (by omega); grind

theorem rectMax_le (G : Grid) (i : Int) (ni : Nat) {M : Rat} : ∀ (n : Nat) (j : Int),
    (∀ k l, i ≤ k → k ≤ i + ni → j ≤ l → l ≤ j + n → G.cellHeight k l ≤ M) →
    G.rectMax i ni j n ≤ M
  | 0, j, h => G.rowMax_le j ni i (fun k h1 h2 => h k j h1 h2 (by omega) (by omega))
  | n + 1, j, h => by
    simp only [rectMax]
    have a := G.rowMax_le j ni i (fun k h1 h2 => h k j h1 h2 (by omega) (by omega))
    have b := rectMax_le G i ni n (j + 1) (fun k l h1 h2 h3 h4 => h k l h1 h2 (by omega) (by omega))
    grind

theorem cell_le_maxOver (G : Grid) {xlo xhi ylo yhi : Rat} {k l : Int}
    (h1 : G.clampX (G.cellX xlo) ≤ k) (h2 : k ≤ G.clampX (G.cellX xhi))
    (h3 : G.clampY (G.cellY ylo) ≤ l) (h4 : l ≤ G.clampY (G.cellY yhi)) :
    G.cellHeight k l ≤ G.maxOver xlo xhi ylo yhi := by
  unfold maxOver
  exact G.le_rectMax _ _ _ _ k l h1 (by omega) h3 (by omega)

theorem heightAt_le_maxOver (G : Grid) (hx : 0 < G.wx) (hy : 0 < G.wy) {xlo xhi ylo yhi x y : Rat}
    (h1 : xlo ≤ x) (h2 : x ≤ xhi) (h3 : ylo ≤ y) (h4 : y ≤ yhi) :
    G.heightAt x y ≤ G.maxOver xlo xhi ylo yhi := by
  have a := G.cellX_mono hx h1
  have b := G.cellX_mono hx h2
  have c := G.cellY_mono hy h3
  have d := G.cellY_mono hy h4
  unfold heightAt
  rw [← cellHeight_clampX, ← cellHeight_clampY]
  apply G.cell_le_maxOver <;> simp only [clampX, clampY] <;> omega

theorem maxOver_mono (G : Grid) (hx : 0 < G.wx) (hy : 0 < G.wy) {xlo xhi ylo yhi xlo' xhi' ylo' yhi' : Rat}
    (h1 : xlo ≤ xlo') (h2 : xhi' ≤ xhi) (h3 : ylo ≤ ylo') (h4 : yhi' ≤ yhi) (h5 : xlo' ≤ xhi')
    (h6 : ylo' ≤ yhi') :
    G.maxOver xlo' xhi' ylo' yhi' ≤ G.maxOver xlo xhi ylo yhi := by
  have a := G.cellX_mono hx h1
  have b := G.cellX_mono hx h2
  have c := G.cellY_mono hy h3
  have d := G.cellY_mono hy h4
  have e := G.cellX_mono hx h5
  have f := G.cellY_mono hy h6
  conv => lhs; unfold maxOver
  apply G.rectMax_le
  intro k l k1 k2 l1 l2
  apply G.cell_le_maxOver <;> simp only [clampX, clampY] at * <;> omega

end Grid
end Envelope3D
