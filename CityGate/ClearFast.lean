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

theorem dyadic_neg (m e : Int) : dyadic (-m) e = -dyadic m e := by
  unfold dyadic; split <;> simp only [Rat.intCast_neg] <;> grind

theorem dyadic_add (a b k : Int) : dyadic a k + dyadic b k = dyadic (a + b) k := by
  unfold dyadic; split <;> simp only [Rat.intCast_add] <;> grind

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

/-- `ratOfBits` as a signed mantissa and a binary exponent. -/
def decB (b : UInt64) : Option (Int × Int) :=
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0x7FF then none
  else
    let (m, ex) : Nat × Int := if e == 0 then (frac, -1074) else (frac + 2 ^ 52, (e : Int) - 1075)
    some (if b >>> 63 == 1 then -(m : Int) else m, ex)

theorem ratOfBits_dec (b : UInt64) : ratOfBits b = (decB b).map fun me => dyadic me.1 me.2 := by
  unfold ratOfBits decB
  dsimp only
  split
  · rfl
  · simp only [Option.map_some]
    split <;> simp [dyadic_neg]

/-- `⌊n·2^k / d⌋` and `⌈n·2^k / d⌉` in `Int`. -/
def fcDy (n k : Int) (d : Nat) : Int × Int :=
  if 0 ≤ k then let a := n * ((2 ^ k.toNat : Nat) : Int); (a / (d : Int), -((-a) / (d : Int)))
  else let D : Nat := 2 ^ (-k).toNat * d; (n / (D : Int), -((-n) / (D : Int)))

theorem fcDy_eq (n k : Int) {d : Nat} (hd : 0 < d) :
    fcDy n k d = ((dyadic n k / d).floor, (dyadic n k / d).ceil) := by
  unfold fcDy dyadic
  split
  · rename_i hk
    have e : (n : Rat) * ((2 ^ k.toNat : Nat) : Rat) = ((n * ((2 ^ k.toNat : Nat) : Int) : Int) : Rat) := by
      simp only [Rat.intCast_mul, Rat.intCast_natCast]
    have en : -(((n * ((2 ^ k.toNat : Nat) : Int) : Int) : Rat) / d) =
        ((-(n * ((2 ^ k.toNat : Nat) : Int)) : Int) : Rat) / d := by rw [Rat.intCast_neg]; grind
    simp only [e, Rat.ceil_eq_neg_floor_neg, en, floor_int_div _ _ hd]
  · rename_i hk
    have hD : 0 < 2 ^ (-k).toNat * d := Nat.mul_pos (Nat.pow_pos (by decide)) hd
    have hp := two_pow_pos (-k).toNat
    have hq := natRat_pos hd
    have e : (n : Rat) / ((2 ^ (-k).toNat : Nat) : Rat) / (d : Rat) = (n : Rat) / ((2 ^ (-k).toNat * d : Nat) : Rat) := by
      rw [Rat.natCast_mul]; grind
    have en : -((n : Rat) / ((2 ^ (-k).toNat * d : Nat) : Rat)) = ((-n : Int) : Rat) / ((2 ^ (-k).toNat * d : Nat) : Rat) := by
      rw [Rat.intCast_neg]; grind
    simp only [e, Rat.ceil_eq_neg_floor_neg, en, floor_int_div _ _ hD]

/-- `16 (a·2^ea + m·2^em · ft)` as `n·2^k / 1250` (`ft = 381/1250`); a zero mantissa takes the other exponent so
that `0 = 0·2^-1074` does not blow up the shift. -/
def comb (a ea m em : Int) : Int × Int :=
  let ea := if a = 0 then em else ea
  let em := if m = 0 then ea else em
  let k := min ea em
  (20000 * (a * ((2 ^ (ea - k).toNat : Nat) : Int)) + 6096 * (m * ((2 ^ (em - k).toNat : Nat) : Int)), k)

theorem comb_eq (a ea m em : Int) :
    dyadic (comb a ea m em).1 (comb a ea m em).2 / ((1250 : Nat) : Rat) = (dyadic a ea + dyadic m em * CitySafety.ft) * S := by
  have ha : dyadic a ea = dyadic a (if a = 0 then em else ea) := by
    by_cases h : a = 0 <;> simp [h, dyadic_zero]
  have hm : dyadic m em = dyadic m (if m = 0 then (if a = 0 then em else ea) else em) := by
    by_cases h : m = 0 <;> simp [h, dyadic_zero]
  rw [ha, hm]
  unfold comb
  dsimp only
  generalize (if a = 0 then em else ea) = ea'
  generalize (if m = 0 then ea' else em) = em'
  rw [← dyadic_add, dyadic_mul 20000, dyadic_mul 6096, ← dyadic_shift a (Int.min_le_left ea' em'),
    ← dyadic_shift m (Int.min_le_right ea' em')]
  simp only [CitySafety.ft, S]
  grind

theorem comb_z (h eh : Int) : dyadic (6096 * h) eh / ((1250 : Nat) : Rat) = dyadic h eh * CitySafety.ft * S := by
  rw [dyadic_mul]; simp only [CitySafety.ft, S]; grind

/-- The reported CG's east, north and altitude (ft), as `CitySafety.report` computes them, without its `Tb2l`. -/
def posFt (s : JsbExact.State Float) : Float × Float × Float :=
  let ce := JsbExact.S.cosS s.epa
  let se := JsbExact.S.sinS s.epa
  let ti2ec : JsbExact.M33 Float := JsbExact.M33.mk' ce se 0 (-se) ce 0 0 0 1
  let loc := ti2ec.mulV s.ri
  let l := JsbExact.locDerive loc
  (loc.y, loc.z, l.radius - JsbExact.seaLevelRadius l)

theorem posFt_report (s : JsbExact.State Float) :
    posFt s = ((CitySafety.report s).loc.y, (CitySafety.report s).loc.z, (CitySafety.report s).hsl) := rfl

/-- `clearAt` in integers: the position's mantissas and exponents (`decB`) scaled exactly to units (`comb`, `fcDy`),
and integer loops. -/
def clearAtFast (extra : Float) (p : Plane) : Bool :=
  let (ly, lz, hs) := posFt p.st
  match decB p.ox.toBits, decB ly.toBits, decB p.oy.toBits, decB lz.toBits, decB hs.toBits with
  | some (a, ea), some (m, em), some (b, eb), some (n, en), some (h, eh) =>
    let x := comb a ea m em
    let y := comb b eb n en
    let (xf, xc) := fcDy x.1 x.2 1250
    let (yf, yc) := fcDy y.1 y.2 1250
    let (zf, zc) := fcDy (6096 * h) eh 1250
    let k : Int := keepBase + extraUnits extra
    terrainClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) &&
      boxesClearI (xf - k) (xc + k) (yf - k) (yc + k) (zf - k) (zc + k)
  | _, _, _, _, _ => false

@[csimp] theorem clearAt_eq_fast : @clearAt = @clearAtFast := by
  funext e p
  simp only [clearAt, clearAtFast, exactPos, posFt_report, ratOf_eq, ratOfBits_dec, boxesClearI_eq, terrainClearI_eq]
  cases decB p.ox.toBits <;> cases decB (CitySafety.report p.st).loc.y.toBits <;>
    cases decB p.oy.toBits <;> cases decB (CitySafety.report p.st).loc.z.toBits <;>
    cases decB (CitySafety.report p.st).hsl.toBits <;> try rfl
  rename_i h n b m a
  obtain ⟨a, ea⟩ := a; obtain ⟨m, em⟩ := m; obtain ⟨b, eb⟩ := b; obtain ⟨n, en⟩ := n; obtain ⟨h, eh⟩ := h
  have d : 0 < 1250 := by decide
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    fcDy_eq _ _ d, ← comb_eq, ← comb_z]
#guard [0.0, -0.0, 1.0, -1.0, 0.03125, 0.1, -0.1, 2999.97, -1234.5678, 5e-324, 1e300, -1e300].all fun f =>
  (decB f.toBits).map (fun me => dyadic me.1 me.2) == CitySafety.ratOf f
#guard decB (1.0 / 0.0 : Float).toBits == none && decB (0.0 / 0.0 : Float).toBits == none
#guard (comb 0 (-1074) 5 (-3)).2 == -3 && fcDy 7 (-1) 2 == (1, 2) && fcDy (-7) 1 3 == (-5, -4)

end CityGate
