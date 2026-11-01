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

end CitySafety.EndSets
