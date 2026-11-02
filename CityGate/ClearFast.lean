import CityGate.Geometry

/-! A fast `clearAt`, proved equal to it (`clearAt_eq_fast`) and swapped in by `@[csimp]`: the reported position's
doubles are decoded to mantissa and exponent (`decB`, no `Rat`), scaled exactly to fixed-point units in `Int`
(`comb`, `fcDy`), the grid squares are found by integer division (`squareOfI`), and the cell and square ranges are
loops instead of lists. Not trusted. -/

namespace CityGate
open VcFilter

theorem natRat_pos {d : Nat} (h : 0 < d) : (0 : Rat) < (d : Rat) := by
  have : ((0 : Nat) : Rat) < (d : Rat) := Rat.natCast_lt_natCast.mpr h
  simpa using this

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

theorem toNat_bits (b : UInt64) :
    ((b >>> 52) &&& 0x7FF).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 ∧ (b &&& 0xFFFFFFFFFFFFF).toNat = b.toNat % 2 ^ 52 ∧
    ((b >>> 63 == 1) = true ↔ b.toNat / 2 ^ 63 = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    rw [show (2047 : Nat) = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  · rw [UInt64.toNat_and]
    simp only [UInt64.reduceToNat]
    rw [show (4503599627370495 : Nat) = 2 ^ 52 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]


theorem two_pow_pos (k : Nat) : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by
  have : ((0 : Nat) : Rat) < ((2 ^ k : Nat) : Rat) := Rat.natCast_lt_natCast.mpr (Nat.pow_pos (by decide))
  simpa using this

theorem dyadic_normal (M e : Nat) : dyadic (M : Int) ((e : Int) - 1075) = (M : Rat) * 2 ^ e / 2 ^ 1075 := by
  have h1 : ((2 : Nat) : Rat) = 2 := rfl
  rw [← h1, ← Rat.natCast_pow, ← Rat.natCast_pow]
  unfold dyadic
  split
  · rename_i h
    have e1 : e = ((e : Int) - 1075).toNat + 1075 := by omega
    have hp := two_pow_pos 1075
    conv => rhs; rw [e1, Nat.pow_add, Rat.natCast_mul]
    generalize ((2 ^ ((e : Int) - 1075).toNat : Nat) : Rat) = A
    generalize ((2 ^ 1075 : Nat) : Rat) = B at hp ⊢
    rw [Rat.intCast_natCast]
    grind
  · rename_i h
    have e1 : 1075 = (-((e : Int) - 1075)).toNat + e := by omega
    have hp := two_pow_pos (-((e : Int) - 1075)).toNat
    have hq := two_pow_pos e
    conv => rhs; rw [e1, Nat.pow_add, Rat.natCast_mul]
    generalize ((2 ^ (-((e : Int) - 1075)).toNat : Nat) : Rat) = A at hp ⊢
    generalize ((2 ^ e : Nat) : Rat) = B at hq ⊢
    rw [Rat.intCast_natCast]
    grind

theorem ratOf_eq (f : Float) : CitySafety.ratOf f = ratOfBits f.toBits := by
  obtain ⟨he, hm, hs⟩ := toNat_bits f.toBits
  unfold CitySafety.ratOf ratOfBits
  simp only [he, hm]
  generalize f.toBits.toNat = b at hs
  have hbeq : ∀ a c : Nat, (a == c) = decide (a = c) := fun a c => rfl
  simp only [hbeq, show (0x7FF : Nat) = 2 ^ 11 - 1 from rfl]
  have hsub : ((2 : Rat) ^ 1074) = ((2 ^ 1074 : Nat) : Rat) := by rw [Rat.natCast_pow]; rfl
  by_cases h7 : b / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1
  · simp [h7]
  · simp only [h7, decide_false, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
    have hmag : (if b / 2 ^ 52 % 2 ^ 11 = 0 then ((b % 2 ^ 52 : Nat) : Rat) / 2 ^ 1074
        else ((2 ^ 52 + b % 2 ^ 52 : Nat) : Rat) * 2 ^ (b / 2 ^ 52 % 2 ^ 11) / 2 ^ 1075) =
        dyadic ((if b / 2 ^ 52 % 2 ^ 11 = 0 then (b % 2 ^ 52, (-1074 : Int))
          else (b % 2 ^ 52 + 2 ^ 52, ((b / 2 ^ 52 % 2 ^ 11 : Nat) : Int) - 1075)).1 : Nat)
          (if b / 2 ^ 52 % 2 ^ 11 = 0 then (b % 2 ^ 52, (-1074 : Int))
          else (b % 2 ^ 52 + 2 ^ 52, ((b / 2 ^ 52 % 2 ^ 11 : Nat) : Int) - 1075)).2 := by
      by_cases h0 : b / 2 ^ 52 % 2 ^ 11 = 0
      · simp only [h0, ↓reduceIte, dyadic]
        rw [hsub, Rat.intCast_natCast]; rfl
      · simp only [h0, ↓reduceIte]
        rw [dyadic_normal, Nat.add_comm]
    simp only [decide_eq_true_eq] at hmag ⊢
    rw [← hmag]
    by_cases hsg : b / 2 ^ 63 = 1
    · simp only [hsg, ↓reduceIte, hs.mpr hsg]
    · have : ¬ (f.toBits >>> 63 == 1) = true := fun h => hsg (hs.mp h)
      simp only [hsg, ↓reduceIte, this, Bool.false_eq_true]

theorem dyadic_zero (e : Int) : dyadic 0 e = 0 := by
  unfold dyadic; split <;> simp [Rat.div_def]

theorem dyadic_mul (c m k : Int) : dyadic (c * m) k = c * dyadic m k := by
  unfold dyadic; split <;> simp only [Rat.intCast_mul] <;> grind

theorem dyadic_shift (m : Int) {k e : Int} (h : k ≤ e) :
    dyadic m e = dyadic (m * ((2 ^ (e - k).toNat : Nat) : Int)) k := by
  unfold dyadic
  have hp := two_pow_pos (e - k).toNat
  by_cases hk : 0 ≤ k
  · have he : 0 ≤ e := by omega
    have e1 : e.toNat = (e - k).toNat + k.toNat := by omega
    simp only [he, hk, ↓reduceIte, e1, Nat.pow_add, Rat.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast]
    grind
  · by_cases he : 0 ≤ e
    · have e1 : (e - k).toNat = e.toNat + (-k).toNat := by omega
      have hq := two_pow_pos (-k).toNat
      simp only [he, hk, ↓reduceIte, e1, Nat.pow_add, Rat.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast]
      generalize ((2 ^ (-k).toNat : Nat) : Rat) = B at hq ⊢
      grind
    · have e1 : (-k).toNat = (-e).toNat + (e - k).toNat := by omega
      have hq := two_pow_pos (-e).toNat
      simp only [he, hk, ↓reduceIte, e1, Nat.pow_add, Rat.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast]
      generalize ((2 ^ (-e).toNat : Nat) : Rat) = B at hq ⊢
      generalize ((2 ^ (e - k).toNat : Nat) : Rat) = A at hp ⊢
      grind

theorem ediv_of {X q : Int} {d : Int} (hd : 0 < d) (h1 : d * q ≤ X) (h2 : X < d * q + d) : X / d = q :=
  ((Int.ediv_emod_unique (r := X - d * q) hd).mpr ⟨by omega, by omega, by omega⟩).1

/-- The table: `(X / den, -((-X) / den))` for `X = ±g1 ± g2`, `g1, g2 < den`. -/
@[inline] def fcTab (s1 s2 : Bool) (g1 g2 den : Nat) : Int × Int :=
  match s1, s2 with
  | false, false => let t := g1 + g2
    if t = 0 then (0, 0) else if t < den then (0, 1) else if t = den then (1, 1) else (1, 2)
  | true, true => let t := g1 + g2
    if t = 0 then (0, 0) else if t < den then (-1, 0) else if t = den then (-1, -1) else (-2, -1)
  | false, true => if g1 = g2 then (0, 0) else if g2 < g1 then (0, 1) else (-1, 0)
  | true, false => if g1 = g2 then (0, 0) else if g1 < g2 then (0, 1) else (-1, 0)

@[inline] def sgnI (s : Bool) (g : Nat) : Int := if s then -(g : Int) else g

theorem fcTab_eq (s1 s2 : Bool) {g1 g2 den : Nat} (h1 : g1 < den) (h2 : g2 < den) :
    fcTab s1 s2 g1 g2 den = ((sgnI s1 g1 + sgnI s2 g2) / (den : Int), -((-(sgnI s1 g1 + sgnI s2 g2)) / (den : Int))) := by
  have hd : (0 : Int) < den := by omega
  cases s1 <;> cases s2 <;> simp only [fcTab, sgnI, Bool.false_eq_true, ↓reduceIte] <;> (repeat' split) <;>
    (refine Prod.ext ?_ ?_ <;> simp only <;> first
      | (rw [ediv_of hd] <;> omega)
      | (rw [ediv_of hd (q := 1)] <;> omega)
      | (rw [ediv_of hd (q := -1)] <;> omega)
      | (rw [ediv_of hd (q := -2)] <;> omega)
      | (rw [ediv_of hd (q := 0)] <;> omega)
      | (rw [ediv_of hd (q := 2)] <;> omega))

def sgn (s : Bool) (q : Rat) : Rat := if s then -q else q

theorem dyadic_add4 (m e : Int) : dyadic m e * 16 = dyadic m (e + 4) := by
  rw [dyadic_shift m (show e ≤ e + 4 by omega), show (e + 4 - e).toNat = 4 by omega, Int.mul_comm, dyadic_mul]
  simp only [Nat.reducePow, Int.cast_ofNat_Int]; grind

theorem nat_div_mod_rat (n d : Nat) (hd : 0 < d) : (n : Rat) / d = ((n / d : Nat) : Rat) + ((n % d : Nat) : Rat) / d := by
  have h := Nat.div_add_mod n d
  have hq := natRat_pos hd
  conv => lhs; rw [← h]
  simp only [Rat.natCast_add, Rat.natCast_mul]
  grind

/-- `2 ^ k` by a machine shift when it fits (`Nat.pow` goes through GMP). -/
@[inline] def pow2 (k : Nat) : Nat := if k < 63 then ((1 : UInt64) <<< k.toUInt64).toNat else 2 ^ k

theorem pow2_eq (k : Nat) : pow2 k = 2 ^ k := by
  unfold pow2
  split
  · rename_i h
    rw [UInt64.toNat_shiftLeft]
    have hk : k.toUInt64.toNat = k := by simp; omega
    rw [hk, Nat.mod_eq_of_lt (by omega : k < 64), Nat.shiftLeft_eq]
    simp only [UInt64.reduceToNat, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · rfl

/-- `16·M·2^E` as `I + r/2^p`, `r < 2^p`. -/
@[inline] def split16 (M : Nat) (E : Int) : Nat × Nat × Nat :=
  if M = 0 then (0, 0, 0)
  else if 0 ≤ E + 4 then (M * pow2 (E + 4).toNat, 0, 0)
  else let p := (-(E + 4)).toNat; (M / pow2 p, M % pow2 p, p)

theorem split16_eq (M : Nat) (E : Int) :
    dyadic M E * S = ((split16 M E).1 : Rat) + ((split16 M E).2.1 : Rat) / ((2 ^ (split16 M E).2.2 : Nat) : Rat) ∧
      (split16 M E).2.1 < 2 ^ (split16 M E).2.2 := by
  unfold split16
  simp only [pow2_eq]
  split
  · rename_i h; subst h; simp [dyadic_zero, Rat.div_def, Rat.add_zero]
  · rw [show S = 16 from rfl, dyadic_add4]
    split
    · rename_i h
      simp only [dyadic, h, ↓reduceIte, Rat.intCast_natCast, Rat.natCast_mul]
      simp [Rat.div_def, Rat.add_zero]
    · rename_i h
      simp only [dyadic, h, ↓reduceIte, Rat.intCast_natCast]
      exact ⟨nat_div_mod_rat _ _ (Nat.pow_pos (by decide)), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- `16·ft·M·2^E = 381·M·2^(E+4) / 1250` as `I + r/(1250·2^q)`, `r < 1250·2^q`. -/
@[inline] def splitFt (M : Nat) (E : Int) : Nat × Nat × Nat :=
  if M = 0 then (0, 0, 0)
  else if 0 ≤ E + 4 then let n := 381 * M * pow2 (E + 4).toNat; (n / 1250, n % 1250, 0)
  else let q := (-(E + 4)).toNat; let K := 1250 * pow2 q; (381 * M / K, 381 * M % K, q)

theorem splitFt_eq (M : Nat) (E : Int) :
    dyadic M E * CitySafety.ft * S =
      ((splitFt M E).1 : Rat) + ((splitFt M E).2.1 : Rat) / ((1250 * 2 ^ (splitFt M E).2.2 : Nat) : Rat) ∧
      (splitFt M E).2.1 < 1250 * 2 ^ (splitFt M E).2.2 := by
  have hft : ∀ x : Rat, x * CitySafety.ft * S = x * 16 * 381 / 1250 := by
    intro x; simp only [CitySafety.ft, S]; grind
  unfold splitFt
  simp only [pow2_eq]
  split
  · rename_i h; subst h; simp [dyadic_zero, Rat.div_def, Rat.add_zero]
  · rw [hft, dyadic_add4]
    split
    · rename_i h
      simp only [dyadic, h, ↓reduceIte, Rat.intCast_natCast, Nat.pow_zero, Nat.mul_one]
      refine ⟨?_, Nat.mod_lt _ (by decide)⟩
      rw [← nat_div_mod_rat _ _ (by decide)]
      simp only [Rat.natCast_mul]; grind
    · rename_i h
      simp only [dyadic, h, ↓reduceIte, Rat.intCast_natCast]
      have hK : 0 < 1250 * 2 ^ (-(E + 4)).toNat := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      refine ⟨?_, Nat.mod_lt _ hK⟩
      rw [← nat_div_mod_rat _ _ hK]
      have hp := two_pow_pos (-(E + 4)).toNat
      simp only [Rat.natCast_mul]
      generalize ((2 ^ (-(E + 4)).toNat : Nat) : Rat) = B at hp ⊢
      grind

/-- `(⌊v⌋, ⌈v⌉)` for `v = ±(I₁ + r₁/2^p) ± (I₂ + r₂/(1250·2^q))`, in scalar `Nat`/`Int` arithmetic. -/
@[inline] def fc2 (s1 : Bool) (t1 : Nat × Nat × Nat) (s2 : Bool) (t2 : Nat × Nat × Nat) : Int × Int :=
  let r := max t1.2.2 t2.2.2
  let tab := fcTab s1 s2 (t1.2.1 * 1250 * pow2 (r - t1.2.2)) (t2.2.1 * pow2 (r - t2.2.2)) (1250 * pow2 r)
  let P : Int := sgnI s1 t1.1 + sgnI s2 t2.1
  (P + tab.1, P + tab.2)

theorem fc2_eq (s1 s2 : Bool) (t1 t2 : Nat × Nat × Nat) (h1 : t1.2.1 < 2 ^ t1.2.2) (h2 : t2.2.1 < 1250 * 2 ^ t2.2.2) :
    fc2 s1 t1 s2 t2 =
      ((sgn s1 ((t1.1 : Rat) + (t1.2.1 : Rat) / ((2 ^ t1.2.2 : Nat) : Rat)) +
          sgn s2 ((t2.1 : Rat) + (t2.2.1 : Rat) / ((1250 * 2 ^ t2.2.2 : Nat) : Rat))).floor,
       (sgn s1 ((t1.1 : Rat) + (t1.2.1 : Rat) / ((2 ^ t1.2.2 : Nat) : Rat)) +
          sgn s2 ((t2.1 : Rat) + (t2.2.1 : Rat) / ((1250 * 2 ^ t2.2.2 : Nat) : Rat))).ceil) := by
  obtain ⟨I1, r1, p⟩ := t1
  obtain ⟨I2, r2, q⟩ := t2
  simp only at h1 h2 ⊢
  have ep : 2 ^ max p q = 2 ^ p * 2 ^ (max p q - p) := by rw [← Nat.pow_add]; congr 1; omega
  have eq : 2 ^ max p q = 2 ^ q * 2 ^ (max p q - q) := by rw [← Nat.pow_add]; congr 1; omega
  have hA : 0 < 2 ^ (max p q - p) := Nat.pow_pos (by decide)
  have hB : 0 < 2 ^ (max p q - q) := Nat.pow_pos (by decide)
  have g1lt : r1 * 1250 * 2 ^ (max p q - p) < 1250 * 2 ^ max p q := by
    have := Nat.mul_lt_mul_of_pos_right h1 (Nat.mul_pos (show 0 < 1250 by decide) hA)
    rw [ep]; grind
  have g2lt : r2 * 2 ^ (max p q - q) < 1250 * 2 ^ max p q := by
    rw [eq, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right h2 hB
  have hden : 0 < 1250 * 2 ^ max p q := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  unfold fc2
  dsimp only
  simp only [pow2_eq]
  rw [fcTab_eq s1 s2 g1lt g2lt]
  generalize hX : sgnI s1 (r1 * 1250 * 2 ^ (max p q - p)) + sgnI s2 (r2 * 2 ^ (max p q - q)) = X
  have hv : sgn s1 ((I1 : Rat) + (r1 : Rat) / ((2 ^ p : Nat) : Rat)) +
      sgn s2 ((I2 : Rat) + (r2 : Rat) / ((1250 * 2 ^ q : Nat) : Rat)) =
      (X : Rat) / ((1250 * 2 ^ max p q : Nat) : Rat) + ((sgnI s1 I1 + sgnI s2 I2 : Int) : Rat) := by
    rw [← hX]
    have e1 : ((2 ^ max p q : Nat) : Rat) = ((2 ^ p : Nat) : Rat) * ((2 ^ (max p q - p) : Nat) : Rat) := by
      rw [ep, Rat.natCast_mul]
    have e2 : ((2 ^ max p q : Nat) : Rat) = ((2 ^ q : Nat) : Rat) * ((2 ^ (max p q - q) : Nat) : Rat) := by
      rw [eq, Rat.natCast_mul]
    have a1 := two_pow_pos p
    have a2 := two_pow_pos q
    have a3 := natRat_pos hA
    have a4 := natRat_pos hB
    cases s1 <;> cases s2 <;> simp only [sgn, sgnI, Bool.false_eq_true, ↓reduceIte, Rat.intCast_add, Rat.intCast_neg,
      Rat.intCast_natCast, Rat.natCast_mul] <;>
    (generalize ((2 ^ max p q : Nat) : Rat) = M at *
     generalize ((2 ^ p : Nat) : Rat) = P1 at *
     generalize ((2 ^ q : Nat) : Rat) = Q1 at *
     generalize ((2 ^ (max p q - p) : Nat) : Rat) = A at *
     generalize ((2 ^ (max p q - q) : Nat) : Rat) = B at *
     subst e1
     grind)
  rw [hv, Rat.floor_add_intCast, Rat.ceil_add_intCast, floor_int_div _ _ hden, Rat.ceil_eq_neg_floor_neg,
    show -((X : Rat) / ((1250 * 2 ^ max p q : Nat) : Rat)) = ((-X : Int) : Rat) / ((1250 * 2 ^ max p q : Nat) : Rat) by
      rw [Rat.intCast_neg]; grind, floor_int_div _ _ hden]
  refine Prod.ext ?_ ?_ <;> simp only <;> omega

theorem mantissa_toNat (b : UInt64) :
    ((b &&& 0xFFFFFFFFFFFFF) + 0x10000000000000).toNat = 2 ^ 52 + (b &&& 0xFFFFFFFFFFFFF).toNat := by
  have h : (b &&& 0xFFFFFFFFFFFFF).toNat ≤ 0xFFFFFFFFFFFFF := by
    rw [UInt64.toNat_and]; exact Nat.and_le_right
  rw [UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  omega

/-- `ratOfBits` as sign, mantissa and binary exponent, all in scalar range (an `Int` mantissa would not be). -/
@[inline] def decN (b : UInt64) : Option (Bool × Nat × Int) :=
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0x7FF then none
  else
    let (m, ex) : Nat × Int := if e == 0 then (frac, -1074)
      else (((b &&& 0xFFFFFFFFFFFFF) + 0x10000000000000).toNat, (e : Int) - 1075)
    some (b >>> 63 == 1, m, ex)

theorem ratOfBits_decN (b : UInt64) : ratOfBits b = (decN b).map fun x => sgn x.1 (dyadic x.2.1 x.2.2) := by
  unfold ratOfBits decN
  dsimp only
  rw [mantissa_toNat, Nat.add_comm]
  split
  · rfl
  · simp only [Option.map_some, sgn]

theorem fc_xy (sa : Bool) (a : Nat) (ea : Int) (sm : Bool) (m : Nat) (em : Int) :
    fc2 sa (split16 a ea) sm (splitFt m em) =
      (((sgn sa (dyadic a ea) + sgn sm (dyadic m em) * CitySafety.ft) * S).floor,
       ((sgn sa (dyadic a ea) + sgn sm (dyadic m em) * CitySafety.ft) * S).ceil) := by
  obtain ⟨e1, b1⟩ := split16_eq a ea
  obtain ⟨e2, b2⟩ := splitFt_eq m em
  rw [fc2_eq sa sm _ _ b1 b2, ← e1, ← e2]
  have : (sgn sa (dyadic a ea) + sgn sm (dyadic m em) * CitySafety.ft) * S =
      sgn sa (dyadic a ea * S) + sgn sm (dyadic m em * CitySafety.ft * S) := by
    cases sa <;> cases sm <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] <;> grind
  rw [this]

theorem fc_z (sh : Bool) (h : Nat) (eh : Int) :
    fc2 false (0, 0, 0) sh (splitFt h eh) =
      ((sgn sh (dyadic h eh) * CitySafety.ft * S).floor, (sgn sh (dyadic h eh) * CitySafety.ft * S).ceil) := by
  have h0 : split16 0 0 = (0, 0, 0) := rfl
  have := fc_xy false 0 0 sh h eh
  rw [h0] at this
  rw [this, show ((0 : Nat) : Int) = 0 from rfl, dyadic_zero]
  have e : (sgn false 0 + sgn sh (dyadic h eh) * CitySafety.ft) * S = sgn sh (dyadic h eh) * CitySafety.ft * S := by
    simp only [sgn, Bool.false_eq_true, ↓reduceIte]; grind
  rw [e]

section
open JsbExact JsbExact.S

/-- `locDerive`'s radius minus `seaLevelRadius`, computing only the geocentric latitude it needs. -/
@[inline] def hslOf (r : V3 Float) : Float :=
  let a : Float := lit Gen.a
  let ec := lit Gen.b / a
  let radius := r.mag
  let rxy := sqrt (mac r.x r.x (r.y * r.y))
  let lat := sif eq radius zero then zero else atan2 r.z rxy
  let e2 := one - ec * ec
  let cl := cos lat
  radius - a * ec / sqrt (nmac (e2 * cl) cl one)

theorem branch_float {β : Type} (j : β → β → β) (c : Bool) (t e : Unit → β) :
    Scalar.branch (α := Float) j c t e = if c then t () else e () := rfl

theorem hslOf_eq (r : V3 Float) : (locDerive r).radius - seaLevelRadius (locDerive r) = hslOf r := by
  simp only [locDerive, seaLevelRadius, hslOf, S.br, branch_float]
  split <;> rfl

/-- The reported CG's east, north and altitude (ft), as `CitySafety.report` computes them, without its `Tb2l`. -/
@[inline] def posFt (s : State Float) : Float × Float × Float :=
  let ce := cosS s.epa
  let se := sinS s.epa
  let ti2ec : M33 Float := M33.mk' ce se 0 (-se) ce 0 0 0 1
  let loc := ti2ec.mulV s.ri
  (loc.y, loc.z, hslOf loc)

end

theorem posFt_report (s : JsbExact.State Float) :
    posFt s = ((CitySafety.report s).loc.y, (CitySafety.report s).loc.z, (CitySafety.report s).hsl) := by
  simp only [posFt, CitySafety.report, ← hslOf_eq]

/-- `clearAt` in scalar integers: the position's doubles as sign, mantissa and exponent (`decN`), scaled exactly to
units by integer and remainder parts (`split16`, `splitFt`, `fc2`), and integer loops. -/
def clearAtFast (extra : Float) (p : Plane) : Bool :=
  let (ly, lz, hs) := posFt p.st
  match decN p.ox.toBits, decN ly.toBits, decN p.oy.toBits, decN lz.toBits, decN hs.toBits with
  | some (sa, a, ea), some (sm, m, em), some (sb, b, eb), some (sn, n, en), some (sh, h, eh) =>
    let (xf, xc) := fc2 sa (split16 a ea) sm (splitFt m em)
    let (yf, yc) := fc2 sb (split16 b eb) sn (splitFt n en)
    let (zf, zc) := fc2 false (0, 0, 0) sh (splitFt h eh)
    let k : Int := keepBase + extraUnits extra
    terrainClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) &&
      boxesClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) (zc + k)
  | _, _, _, _, _ => false

@[csimp] theorem clearAt_eq_fast : @clearAt = @clearAtFast := by
  funext e p
  simp only [clearAt, clearAtFast, exactPos, posFt_report, ratOf_eq, ratOfBits_decN, boxesClearI_eq, terrainClearI_eq]
  cases decN p.ox.toBits <;> cases decN (CitySafety.report p.st).loc.y.toBits <;>
    cases decN p.oy.toBits <;> cases decN (CitySafety.report p.st).loc.z.toBits <;>
    cases decN (CitySafety.report p.st).hsl.toBits <;> try rfl
  rename_i h n b m a
  obtain ⟨sa, a, ea⟩ := a; obtain ⟨sm, m, em⟩ := m; obtain ⟨sb, b, eb⟩ := b; obtain ⟨sn, n, en⟩ := n
  obtain ⟨sh, h, eh⟩ := h
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def, fc_xy, fc_z]

#guard [0.0, -0.0, 1.0, -1.0, 0.03125, 0.1, -0.1, 2999.97, -1234.5678, 5e-324, 1e300, -1e300].all fun f =>
  (decN f.toBits).map (fun x => sgn x.1 (dyadic x.2.1 x.2.2)) == CitySafety.ratOf f
#guard decN (1.0 / 0.0 : Float).toBits == none && decN (0.0 / 0.0 : Float).toBits == none
#guard [(-1234.5678, -3.25), (0.0, 7.5), (812.0, -40000.125), (-0.001, 0.002)].all fun (o, l) =>
  match decN o.toBits, decN l.toBits with
  | some (sa, a, ea), some (sm, m, em) =>
    let v := (sgn sa (dyadic a ea) + sgn sm (dyadic m em) * CitySafety.ft) * S
    fc2 sa (split16 a ea) sm (splitFt m em) == (v.floor, v.ceil)
  | _, _ => false

end CityGate
