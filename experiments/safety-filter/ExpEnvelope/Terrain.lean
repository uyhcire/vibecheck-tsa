/-! Terrain as a 1D max-height grid, with a swept maximum over an along-track interval
and a maximum over everything ahead of a point. -/

namespace ExpEnvelope

/-- Max-height grid: cell `i` bounds terrain on `[x0 + i·w, x0 + (i+1)·w)`; `beyond` bounds the rest. -/
structure Terrain where
  x0 : Rat
  w : Rat
  cells : Array Rat
  beyond : Rat
  deriving Repr

namespace Terrain

/-- Index of the cell containing `x`. -/
def cellOf (T : Terrain) (x : Rat) : Int := ((x - T.x0) / T.w).floor

/-- Height bound of cell `i` (`beyond` outside the grid). -/
def cellHeight (T : Terrain) (i : Int) : Rat :=
  if 0 ≤ i then T.cells.getD i.toNat T.beyond else T.beyond

/-- Terrain height bound at along-track position `x`. -/
def heightAt (T : Terrain) (x : Rat) : Rat := T.cellHeight (T.cellOf x)

/-- Max of `cellHeight` over indices `i, i+1, …, i+n`. -/
def maxFrom (T : Terrain) (i : Int) : Nat → Rat
  | 0 => T.cellHeight i
  | n + 1 => max (T.cellHeight i) (T.maxFrom (i + 1) n)

/-- Clamp an index into `[-1, size]`; heights are constant outside the grid. -/
def clampIdx (T : Terrain) (i : Int) : Int := max (-1) (min i T.cells.size)

/-- Upper bound on terrain height over `[lo, hi]`. -/
def maxOver (T : Terrain) (lo hi : Rat) : Rat :=
  let i := T.clampIdx (T.cellOf lo)
  let j := T.clampIdx (T.cellOf hi)
  T.maxFrom i (j - i).toNat

/-- Upper bound on terrain height at and after `lo`: a max over the cells from `lo`'s to the end
of the grid, and `beyond`. -/
def maxAhead (T : Terrain) (lo : Rat) : Rat :=
  let i := T.clampIdx (T.cellOf lo)
  T.maxFrom i (T.cells.size - i).toNat

theorem cellOf_mono (T : Terrain) (hw : 0 < T.w) {x y : Rat} (h : x ≤ y) :
    T.cellOf x ≤ T.cellOf y := by
  unfold cellOf
  apply Rat.floor_monotone
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hw))

theorem cellHeight_clamp (T : Terrain) (i : Int) : T.cellHeight (T.clampIdx i) = T.cellHeight i := by
  unfold cellHeight clampIdx
  by_cases h0 : 0 ≤ i
  · by_cases h1 : i ≤ T.cells.size
    · have : max (-1) (min i (T.cells.size : Int)) = i := by omega
      rw [this]
    · have : max (-1) (min i (T.cells.size : Int)) = T.cells.size := by omega
      rw [this]
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
      simp
  · have : max (-1) (min i (T.cells.size : Int)) = -1 := by omega
    rw [this]; simp [h0]

theorem le_maxFrom (T : Terrain) : ∀ (n : Nat) (i j : Int), i ≤ j → j ≤ i + n →
    T.cellHeight j ≤ T.maxFrom i n
  | 0, i, j, h1, h2 => by
    have : j = i := by omega
    subst this; exact Rat.le_refl
  | n + 1, i, j, h1, h2 => by
    simp only [maxFrom]
    by_cases hj : j = i
    · subst hj; grind
    · have := le_maxFrom T n (i + 1) j (by omega) (by omega); grind

theorem heightAt_le_maxOver (T : Terrain) (hw : 0 < T.w) {lo hi x : Rat} (h1 : lo ≤ x)
    (h2 : x ≤ hi) : T.heightAt x ≤ T.maxOver lo hi := by
  have a := T.cellOf_mono hw h1
  have b := T.cellOf_mono hw h2
  unfold heightAt maxOver
  rw [← cellHeight_clamp]
  apply le_maxFrom <;> simp only [clampIdx] <;> omega

theorem heightAt_le_maxAhead (T : Terrain) (hw : 0 < T.w) {lo x : Rat} (h : lo ≤ x) :
    T.heightAt x ≤ T.maxAhead lo := by
  have a := T.cellOf_mono hw h
  unfold heightAt maxAhead
  rw [← cellHeight_clamp]
  apply le_maxFrom <;> simp only [clampIdx] <;> omega

end Terrain
end ExpEnvelope
