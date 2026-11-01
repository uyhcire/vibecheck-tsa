import CityGate.Geometry

/-! A fast `clearAt`, proved equal to it (`clearAt_eq_fast`) and swapped in by `@[csimp]`: the position's doubles are
decoded straight to fixed-point `Int` from sign, exponent and mantissa (`fix16`, no `Rat`), the grid squares are
found by integer division (`squareOfI`), and the cell and square ranges are loops instead of lists. Not trusted. -/

namespace CityGate
open VcFilter

theorem natRat_pos {d : Nat} (h : 0 < d) : (0 : Rat) < (d : Rat) := by
  have : ((0 : Nat) : Rat) < (d : Rat) := Rat.natCast_lt_natCast.mpr h
  simpa using this

theorem floor_div_nat (n d : Nat) (hd : 0 < d) : ((n : Rat) / (d : Rat)).floor = ((n / d : Nat) : Int) := by
  have hq := natRat_pos hd
  apply Int.le_antisymm
  · have h1 : (n : Rat) / d < (((n / d : Nat) : Int) + 1 : Int) := by
      rw [Rat.div_lt_iff hq]
      have : n < (n / d + 1) * d := by
        have := Nat.lt_div_mul_add (a := n) hd; rw [Nat.add_mul, Nat.one_mul]; exact this
      have := Rat.natCast_lt_natCast.mpr this
      simp only [Rat.natCast_mul, Rat.natCast_add] at this
      simp only [Rat.intCast_add, Rat.intCast_natCast, Rat.intCast_one]; exact this
    have := (Rat.floor_lt_iff).mpr h1
    omega
  · apply Rat.le_floor_iff.mpr
    rw [Rat.intCast_natCast]
    apply Rat.not_lt.mp
    rw [Rat.div_lt_iff hq]
    have : n / d * d ≤ n := Nat.div_mul_le_self n d
    have := Rat.natCast_le_natCast.mpr this
    simp only [Rat.natCast_mul] at this
    exact Rat.not_lt.mpr this

theorem ceil_div_nat (n d y : Nat) (hd : 0 < d) (h1 : n ≤ y * d) (h2 : y * d < n + d) :
    ((n : Rat) / (d : Rat)).ceil = (y : Int) := by
  have hq := natRat_pos hd
  have c1 := Rat.natCast_le_natCast.mpr h1
  have c2 := Rat.natCast_lt_natCast.mpr h2
  simp only [Rat.natCast_mul, Rat.natCast_add] at c1 c2
  apply Int.le_antisymm
  · apply Rat.ceil_le_iff.mpr
    rw [Rat.intCast_natCast]
    apply Rat.not_lt.mp
    rw [Rat.lt_div_iff hq]
    exact Rat.not_lt.mpr c1
  · have : ¬ ((n : Rat) / (d : Rat)).ceil ≤ (y : Int) - 1 := by
      rw [Rat.ceil_le_iff]
      apply Rat.not_le.mpr
      rw [Rat.lt_div_iff hq]
      simp only [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_one]
      grind
    omega

/-- `(⌊n / 2^s⌋, ⌈n / 2^s⌉)` by shifts. -/
def shiftFloorCeil (n s : Nat) : Nat × Nat :=
  let f := n >>> s
  (f, if f <<< s == n then f else f + 1)

theorem shiftFloorCeil_eq (n s : Nat) :
    (((shiftFloorCeil n s).1 : Nat) : Int) = ((n : Rat) / ((2 ^ s : Nat) : Rat)).floor ∧
    (((shiftFloorCeil n s).2 : Nat) : Int) = ((n : Rat) / ((2 ^ s : Nat) : Rat)).ceil := by
  have hd : 0 < 2 ^ s := Nat.pow_pos (by decide)
  refine ⟨?_, ?_⟩
  · simp only [shiftFloorCeil, Nat.shiftRight_eq_div_pow]; rw [floor_div_nat _ _ hd]
  · simp only [shiftFloorCeil, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have a1 := Nat.div_mul_le_self n (2 ^ s)
    have a2 := Nat.lt_div_mul_add (a := n) hd
    split
    · rename_i h
      have h' : n / 2 ^ s * 2 ^ s = n := by simpa using h
      rw [ceil_div_nat n _ (n / 2 ^ s) hd (by omega) (by omega)]
    · rename_i h
      have h' : n / 2 ^ s * 2 ^ s ≠ n := by simpa using h
      rw [ceil_div_nat n _ (n / 2 ^ s + 1) hd (by rw [Nat.add_mul]; omega) (by rw [Nat.add_mul]; omega)]

theorem dyadic_mul16 (m : Nat) (ex : Int) :
    dyadic (m : Int) ex * S = ((m <<< (ex + 4).toNat : Nat) : Rat) / ((2 ^ (-(ex + 4)).toNat : Nat) : Rat) := by
  simp only [dyadic, S, Nat.shiftLeft_eq, Rat.intCast_natCast]
  split
  · rename_i h
    have e1 : (ex + 4).toNat = ex.toNat + 4 := by omega
    have e2 : (-(ex + 4)).toNat = 0 := by omega
    rw [e1, e2, Nat.pow_add]
    simp only [Rat.natCast_mul, Nat.pow_zero]
    have : ((2 ^ 4 : Nat) : Rat) = 16 := by decide
    rw [this]; simp; grind
  · rename_i h
    by_cases h4 : -4 ≤ ex
    · have e2 : (-(ex + 4)).toNat = 0 := by omega
      rw [e2]
      have : ex = -1 ∨ ex = -2 ∨ ex = -3 ∨ ex = -4 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp <;> grind
    · have e1 : (ex + 4).toNat = 0 := by omega
      have e3 : (-ex).toNat = (-(ex + 4)).toNat + 4 := by omega
      rw [e1, e3, Nat.pow_add, Nat.pow_zero, Nat.mul_one]
      have hp : (0 : Rat) < ((2 ^ (-(ex + 4)).toNat : Nat) : Rat) := natRat_pos (Nat.pow_pos (by decide))
      simp only [Rat.natCast_mul]
      generalize ((2 ^ (-(ex + 4)).toNat : Nat) : Rat) = P at hp ⊢
      have : ((2 ^ 4 : Nat) : Rat) = 16 := by decide
      rw [this]
      grind

/-- `⌊16 v⌋` and `⌈16 v⌉` for the double `v` with bits `b`, from its sign, exponent and mantissa (as `ratOfBits`
decodes them); `none` if it is not finite. -/
def fix16 (b : UInt64) : Option (Int × Int) :=
  let neg := b >>> 63 == 1
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0x7FF then none
  else
    let (m, ex) : Nat × Int := if e == 0 then (frac, -1074) else (frac + 2 ^ 52, (e : Int) - 1075)
    let r := shiftFloorCeil (m <<< (ex + 4).toNat) (-(ex + 4)).toNat
    some (if neg then (-(r.2 : Int), -(r.1 : Int)) else ((r.1 : Int), (r.2 : Int)))

theorem floor_neg (a : Rat) : (-a).floor = -a.ceil := by
  rw [Rat.ceil_eq_neg_floor_neg]; omega

theorem ceil_neg (a : Rat) : (-a).ceil = -a.floor := by
  rw [Rat.ceil_eq_neg_floor_neg, Rat.neg_neg]

theorem fix16_eq (b : UInt64) : fix16 b = (ratOfBits b).map fun q => ((q * S).floor, (q * S).ceil) := by
  unfold fix16 ratOfBits
  dsimp only
  split
  · rfl
  · generalize (if ((b >>> 52) &&& 0x7FF).toNat == 0 then ((b &&& 0xFFFFFFFFFFFFF).toNat, (-1074 : Int))
      else ((b &&& 0xFFFFFFFFFFFFF).toNat + 2 ^ 52, (((b >>> 52) &&& 0x7FF).toNat : Int) - 1075)) = me
    obtain ⟨m, ex⟩ := me
    obtain ⟨hf, hc⟩ := shiftFloorCeil_eq (m <<< (ex + 4).toNat) (-(ex + 4)).toNat
    rw [← dyadic_mul16] at hf hc
    simp only [Option.map_some]
    split
    · rw [Rat.neg_mul, floor_neg, ceil_neg, hf, hc]
    · rw [hf, hc]

theorem floor_int_div (a : Int) (d : Nat) (hd : 0 < d) : (((a : Rat)) / (d : Rat)).floor = a / (d : Int) := by
  have hq := natRat_pos hd
  have hd' : (0 : Int) < d := by omega
  apply Int.le_antisymm
  · have h1 : (a : Rat) / d < ((a / (d : Int) + 1 : Int) : Rat) := by
      rw [Rat.div_lt_iff hq]
      have : a < (a / (d : Int) + 1) * d := Int.lt_ediv_add_one_mul_self a hd'
      have := Rat.intCast_lt_intCast.mpr this
      simp only [Rat.intCast_mul, Rat.intCast_natCast] at this
      exact this
    have := (Rat.floor_lt_iff).mpr h1
    omega
  · apply Rat.le_floor_iff.mpr
    apply Rat.not_lt.mp
    rw [Rat.div_lt_iff hq]
    have : a / (d : Int) * d ≤ a := Int.ediv_mul_le a (by omega)
    have := Rat.intCast_le_intCast.mpr this
    simp only [Rat.intCast_mul, Rat.intCast_natCast] at this
    exact Rat.not_lt.mpr this

/-- `squareOf` in integers: the grid square under `v` (units) along an axis from `x0` (m). -/
def squareOfI (x0 v : Int) : Nat := min ((v - 16 * x0) / 320).toNat 299

theorem squareOfI_eq (x0 v : Int) : squareOfI x0 v = squareOf x0 v := by
  have hg : ((v : Rat) / S - (x0 : Rat)) / (gridStep : Rat) = (((v - 16 * x0 : Int) : Rat)) / ((320 : Nat) : Rat) := by
    simp only [S, gridStep, Rat.intCast_sub, Rat.intCast_mul]
    grind
  have hfl := floor_int_div (v - 16 * x0) 320 (by decide)
  rw [← hg] at hfl
  unfold squareOfI squareOf square gridCoord
  generalize ((v : Rat) / S - (x0 : Rat)) / (gridStep : Rat) = g at hfl ⊢
  have h1 := Rat.floor_le g
  have h2 := Rat.lt_floor_add_one g
  rw [hfl] at h1 h2
  have e320 : ((320 : Nat) : Int) = 320 := rfl
  rw [e320] at h1 h2 hfl
  generalize (v - 16 * x0) / 320 = n at h1 h2 hfl ⊢
  simp only [gridN, Nat.reduceSub, Rat.natCast_ofNat]
  by_cases hn0 : n < 0
  · have : max 0 (min 300 g) = (0 : Rat) := by
      simp only [Rat.intCast_add] at h2
      have : g < 0 := by
        have : (n : Rat) + 1 ≤ 0 := by
          have := Rat.intCast_le_intCast.mpr (show n + 1 ≤ 0 by omega)
          simpa [Rat.intCast_add] using this
        grind
      grind
    rw [this]
    have : (0 : Rat).floor = 0 := rfl
    rw [this]; omega
  · by_cases hn3 : 300 ≤ n
    · have : max 0 (min 300 g) = (300 : Rat) := by
        have : (300 : Rat) ≤ n := by
          have := Rat.intCast_le_intCast.mpr hn3; simpa using this
        grind
      rw [this]
      have : (300 : Rat).floor = 300 := rfl
      rw [this]; omega
    · have : max 0 (min 300 g) = g := by
        have a : (0 : Rat) ≤ n := by
          have := Rat.intCast_le_intCast.mpr (show (0 : Int) ≤ n by omega); simpa using this
        have b : (n : Rat) + 1 ≤ 300 := by
          have := Rat.intCast_le_intCast.mpr (show n + 1 ≤ 300 by omega); simpa [Rat.intCast_add] using this
        simp only [Rat.intCast_add] at h2
        grind
      rw [this, hfl]

/-- `(List.range' a n).all f` as a loop. -/
@[specialize] def allFrom (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | a, n + 1 => f a && allFrom f (a + 1) n

theorem allFrom_eq (f : Nat → Bool) : ∀ a n, allFrom f a n = (List.range' a n).all f
  | _, 0 => rfl
  | a, n + 1 => by simp only [allFrom, List.range'_succ, List.all_cons, allFrom_eq f (a + 1) n]

def boxesClearI (xl xh yl yh zl zh : Int) : Bool :=
  allFrom (fun i => allFrom (fun j =>
      (cellBoxes.getD (j * 100 + i) []).all fun b =>
        !(meets xl xh b.xmin b.xmax && meets yl yh b.ymin b.ymax && meets zl zh b.zmin b.zmax))
    (cellIdx yl) (cellIdx yh + 1 - cellIdx yl)) (cellIdx xl) (cellIdx xh + 1 - cellIdx xl)

def terrainClearI (xl xh yl yh zl : Int) : Bool :=
  allFrom (fun i => allFrom (fun j => decide (squareTop i j < zl))
      (squareOfI gridY0 yl) (squareOfI gridY0 yh + 1 - squareOfI gridY0 yl))
    (squareOfI gridX0 xl) (squareOfI gridX0 xh + 1 - squareOfI gridX0 xl)

theorem boxesClearI_eq : @boxesClearI = @boxesClear := by
  funext xl xh yl yh zl zh
  simp only [boxesClearI, boxesClear, allFrom_eq]

theorem terrainClearI_eq : @terrainClearI = @terrainClear := by
  funext xl xh yl yh zl
  simp only [terrainClearI, terrainClear, allFrom_eq, squareOfI_eq]

/-- `clearAt` with the position decoded straight to units (`fix16`) and integer loops. -/
def clearAtFast (extra : Float) (p : Plane) : Bool :=
  let (x, y, z) := p.pos
  match fix16 x.toBits, fix16 y.toBits, fix16 z.toBits with
  | some (xf, xc), some (yf, yc), some (zf, zc) =>
    let k : Int := keepBase + extraUnits extra
    terrainClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) &&
      boxesClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) (zc + k)
  | _, _, _ => false

@[csimp] theorem clearAt_eq_fast : @clearAt = @clearAtFast := by
  funext e p
  simp only [clearAt, clearAtFast, exactPos, ratOfFloat, fix16_eq, boxesClearI_eq, terrainClearI_eq]
  cases ratOfBits p.pos.1.toBits <;> cases ratOfBits p.pos.2.1.toBits <;> cases ratOfBits p.pos.2.2.toBits <;> rfl
#guard [0.0, -0.0, 1.0, -1.0, 0.03125, -0.03125, 0.1, -0.1, 2999.97, -1234.5678, 5e-324, 1e300, -1e300].all fun f =>
  fix16 f.toBits == (ratOfFloat f).map fun q => ((q * S).floor, (q * S).ceil)
#guard fix16 (1.0 / 0.0 : Float).toBits == none && fix16 (0.0 / 0.0 : Float).toBits == none

end CityGate
