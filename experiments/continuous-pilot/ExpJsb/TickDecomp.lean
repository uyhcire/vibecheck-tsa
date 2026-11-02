import ExpJsb.EscapeRegionChecks

/-! One-tick vz/vx increments decomposed into the eight substeps' derivative evaluations, and a counterexample
showing the interval route's full region (`Tools/BoxProbe.lean`) contains states violating the one-tick property.

Part A. Over one tick `s_0 = c.s`, `s_{k+1} = step 7 true u s_k` with `u = Escape.input c`. The AB2 update of
substep `k` adds `(3 a_k - a_{k-1} + 128) >>> 8` to vz, where `a_k = (s_k).au` and `a_{k-1} = (s_k).au1`, which is
`(s_{k-1}).au` (`c.s.au1` for `k = 0`) because `evaluate` leaves `au1` alone. Summing the eight substeps gives
`2 a_0 - a_{-1} + 2 (a_1 + ... + a_6) + 3 a_7` up to the eight roundings, each in `[-127, 128]` after scaling by 256.

The multiplication `3 * x` on `Fx` is exact only while `x.raw` fits in an `Int64` (`fmul` converts through `Int64`);
the theorems carry that as an explicit hypothesis `Fits`. -/

namespace ExpJsb
open ExpVibecheck

/-- `x.raw` is representable in an `Int64`, so `Fx` arithmetic that goes through `Int64` does not wrap. -/
def Fits (x : Fx) : Prop := -2 ^ 63 ≤ x.raw ∧ x.raw < 2 ^ 63

/-- Multiplying by the constant 3 is exact (`3 = lit 196608`; `fmul` is exact in both of its branches). -/
theorem three_mul_raw (x : Fx) (h : Fits x) : ((3 : Fx) * x).raw = 3 * x.raw := by
  obtain ⟨h1, h2⟩ := h
  show (fmul ⟨196608⟩ x).raw = _
  unfold fmul
  simp only []
  split
  · rename_i h
    obtain ⟨a, b, c, d⟩ := h
    have hb : x.raw.bmod Int64.size = x.raw :=
      Int.bmod_eq_of_le (by unfold Int64.size; omega) (by unfold Int64.size; omega)
    simp [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, Int64.toInt_ofInt, hb] at a b c d
    simp only [Int64.toInt, Int64.toBitVec_shiftRight, Int64.toBitVec_mul, Int64.toBitVec_ofInt]
    simp [hb]
    have h3 : (196608 * x.raw).bmod 18446744073709551616 = 196608 * x.raw :=
      Int.bmod_eq_of_le (by omega) (by omega)
    rw [h3]
    rw [Int.shiftRight_eq_div_pow]; omega
  · simp; omega

/-- The rounded shift `Scalar.shr x 8` as floor division. -/
theorem shr8_raw (x : Fx) : (Scalar.shr x 8).raw = (x.raw + 128) / 256 := by
  show (x.raw + (1 <<< (8 - 1 : Nat))) >>> 8 = _
  rw [Int.shiftRight_eq_div_pow]; rfl

/-- `evaluate` leaves the AB2 history `au1` alone, so after a step it holds the previous `au`. -/
theorem step_au1 (u : InputOf Fx) (s : StateOf Fx) : (step 7 true u s).au1 = s.au := by kernel_rfl
theorem step_ah1 (u : InputOf Fx) (s : StateOf Fx) : (step 7 true u s).ah1 = s.ah := by kernel_rfl

/-- Raw vz increment of one substep, as floor division. -/
theorem step_vz_raw (u : InputOf Fx) (s : StateOf Fx) (h : Fits s.au) :
    (step 7 true u s).vz.raw = s.vz.raw + (3 * s.au.raw - s.au1.raw + 128) / 256 := by
  rw [step_vz]
  show s.vz.raw + (Scalar.shr (3 * s.au - s.au1) 8).raw = _
  rw [shr8_raw]
  show _ + ((3 * s.au).raw - s.au1.raw + 128) / 256 = _
  rw [three_mul_raw _ h]

theorem step_vx_raw (u : InputOf Fx) (s : StateOf Fx) (h : Fits s.ah) :
    (step 7 true u s).vx.raw = s.vx.raw + (3 * s.ah.raw - s.ah1.raw + 128) / 256 := by
  rw [step_vx]
  show s.vx.raw + (Scalar.shr (3 * s.ah - s.ah1) 8).raw = _
  rw [shr8_raw]
  show _ + ((3 * s.ah).raw - s.ah1.raw + 128) / 256 = _
  rw [three_mul_raw _ h]

theorem iter_succ' {β : Type} (f : β → β) : ∀ (n : Nat) (s : β), iter (n + 1) f s = f (iter n f s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih => intro s; show iter (n + 1) f (f s) = _; rw [ih]; rfl

/-- Abstract eight-substep sum, for a velocity field `V` driven by a derivative field `F` with history `G`:
`256 * Δ V` is `2 a_0 - a_{-1} + 2 (a_1 + ... + a_6) + 3 a_7` up to the eight roundings
(`-127` and `+128` each), where `a_k = F (s_k)`. -/
theorem iter8_sum (V F G : StateOf Fx → Fx) (u : InputOf Fx) (s : StateOf Fx)
    (hv : ∀ t, Fits (F t) → (V (step 7 true u t)).raw = (V t).raw + (3 * (F t).raw - (G t).raw + 128) / 256)
    (hg : ∀ t, G (step 7 true u t) = F t)
    (hF : ∀ k, k ≤ 7 → Fits (F (iter k (step 7 true u) s))) :
    let a := fun k => (F (iter k (step 7 true u) s)).raw
    let S := 2 * (F s).raw - (G s).raw + 2 * (a 1 + a 2 + a 3 + a 4 + a 5 + a 6) + 3 * a 7
    S - 1016 ≤ 256 * ((V (iter 8 (step 7 true u) s)).raw - (V s).raw) ∧
    256 * ((V (iter 8 (step 7 true u) s)).raw - (V s).raw) ≤ S + 1024 := by
  intro a S
  have key : ∀ k m, k ≤ 7 → m = k + 1 → (V (iter m (step 7 true u) s)).raw =
      (V (iter k (step 7 true u) s)).raw +
        (3 * (F (iter k (step 7 true u) s)).raw - (G (iter k (step 7 true u) s)).raw + 128) / 256 :=
    fun k m hk hm => by subst hm; rw [iter_succ']; exact hv _ (hF k hk)
  have gk : ∀ k m, m = k + 1 → (G (iter m (step 7 true u) s)).raw = (F (iter k (step 7 true u) s)).raw :=
    fun k m hm => by subst hm; rw [iter_succ', hg]
  have k0 := key 0 1 (by omega) rfl; have k1 := key 1 2 (by omega) rfl; have k2 := key 2 3 (by omega) rfl
  have k3 := key 3 4 (by omega) rfl; have k4 := key 4 5 (by omega) rfl; have k5 := key 5 6 (by omega) rfl
  have k6 := key 6 7 (by omega) rfl; have k7 := key 7 8 (by omega) rfl
  have g0 := gk 0 1 rfl; have g1 := gk 1 2 rfl; have g2 := gk 2 3 rfl; have g3 := gk 3 4 rfl
  have g4 := gk 4 5 rfl; have g5 := gk 5 6 rfl; have g6 := gk 6 7 rfl
  have e0 : iter 0 (step 7 true u) s = s := rfl
  rw [e0] at k0 g0
  simp only [S, a]
  omega

/-- Lower bound on the vz increment of one escape tick from the derivative `au` at the start and at each of
the first seven substeps' ends: `A ≤ au_k` for `k = 1..7` where `au_k = (iter k (step 7 true u) c.s).au`.
`Fits` side conditions: `3 * au_k` goes through `Int64` in `fmul`. The constant 1016 is `8 * 127`. -/
theorem tick_dvz_lower (c : CLOf Fx) (A : Int)
    (hF : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).au)
    (hA : ∀ k, 1 ≤ k → k ≤ 7 → A ≤ (iter k (step 7 true (Escape.input c)) c.s).au.raw) :
    2 * c.s.au.raw - c.s.au1.raw + 15 * A - 1016 ≤ 256 * ((Escape.tick c).s.vz.raw - c.s.vz.raw) := by
  have h := (iter8_sum (·.vz) (·.au) (·.au1) (Escape.input c) c.s
    (fun t ht => step_vz_raw _ t ht) (fun t => step_au1 _ t) hF).1
  have : (Escape.tick c).s = iter 8 (step 7 true (Escape.input c)) c.s := rfl
  rw [this]
  simp only at h
  have := hA 1 (by omega) (by omega); have := hA 2 (by omega) (by omega); have := hA 3 (by omega) (by omega)
  have := hA 4 (by omega) (by omega); have := hA 5 (by omega) (by omega); have := hA 6 (by omega) (by omega)
  have := hA 7 (by omega) (by omega)
  omega

/-- Upper bound counterpart: `au_k ≤ B` for `k = 1..7`; the constant 1024 is `8 * 128`. -/
theorem tick_dvz_upper (c : CLOf Fx) (B : Int)
    (hF : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).au)
    (hB : ∀ k, 1 ≤ k → k ≤ 7 → (iter k (step 7 true (Escape.input c)) c.s).au.raw ≤ B) :
    256 * ((Escape.tick c).s.vz.raw - c.s.vz.raw) ≤ 2 * c.s.au.raw - c.s.au1.raw + 15 * B + 1024 := by
  have h := (iter8_sum (·.vz) (·.au) (·.au1) (Escape.input c) c.s
    (fun t ht => step_vz_raw _ t ht) (fun t => step_au1 _ t) hF).2
  have : (Escape.tick c).s = iter 8 (step 7 true (Escape.input c)) c.s := rfl
  rw [this]
  simp only at h
  have := hB 1 (by omega) (by omega); have := hB 2 (by omega) (by omega); have := hB 3 (by omega) (by omega)
  have := hB 4 (by omega) (by omega); have := hB 5 (by omega) (by omega); have := hB 6 (by omega) (by omega)
  have := hB 7 (by omega) (by omega)
  omega

/-- The horizontal counterpart of `tick_dvz_lower`, for `ah`. -/
theorem tick_dvx_lower (c : CLOf Fx) (A : Int)
    (hF : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).ah)
    (hA : ∀ k, 1 ≤ k → k ≤ 7 → A ≤ (iter k (step 7 true (Escape.input c)) c.s).ah.raw) :
    2 * c.s.ah.raw - c.s.ah1.raw + 15 * A - 1016 ≤ 256 * ((Escape.tick c).s.vx.raw - c.s.vx.raw) := by
  have h := (iter8_sum (·.vx) (·.ah) (·.ah1) (Escape.input c) c.s
    (fun t ht => step_vx_raw _ t ht) (fun t => step_ah1 _ t) hF).1
  have : (Escape.tick c).s = iter 8 (step 7 true (Escape.input c)) c.s := rfl
  rw [this]
  simp only at h
  have := hA 1 (by omega) (by omega); have := hA 2 (by omega) (by omega); have := hA 3 (by omega) (by omega)
  have := hA 4 (by omega) (by omega); have := hA 5 (by omega) (by omega); have := hA 6 (by omega) (by omega)
  have := hA 7 (by omega) (by omega)
  omega

theorem tick_dvx_upper (c : CLOf Fx) (B : Int)
    (hF : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).ah)
    (hB : ∀ k, 1 ≤ k → k ≤ 7 → (iter k (step 7 true (Escape.input c)) c.s).ah.raw ≤ B) :
    256 * ((Escape.tick c).s.vx.raw - c.s.vx.raw) ≤ 2 * c.s.ah.raw - c.s.ah1.raw + 15 * B + 1024 := by
  have h := (iter8_sum (·.vx) (·.ah) (·.ah1) (Escape.input c) c.s
    (fun t ht => step_vx_raw _ t ht) (fun t => step_ah1 _ t) hF).2
  have : (Escape.tick c).s = iter 8 (step 7 true (Escape.input c)) c.s := rfl
  rw [this]
  simp only at h
  have := hB 1 (by omega) (by omega); have := hB 2 (by omega) (by omega); have := hB 3 (by omega) (by omega)
  have := hB 4 (by omega) (by omega); have := hB 5 (by omega) (by omega); have := hB 6 (by omega) (by omega)
  have := hB 7 (by omega) (by omega)
  omega

/-- The `IncrProp` conjuncts from per-substep lower bounds `Az`, `Ax` on `au_k`, `ah_k` (`k = 1..7`) and the
start-of-tick values: `256 * dvzMin + 1016 ≤ 2 au_0 - au_{-1} + 15 Az`, likewise for vx. -/
theorem incr_of_substeps (c : CLOf Fx) (Az Ax : Int)
    (hFz : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).au)
    (hFx : ∀ k, k ≤ 7 → Fits (iter k (step 7 true (Escape.input c)) c.s).ah)
    (hz : ∀ k, 1 ≤ k → k ≤ 7 → Az ≤ (iter k (step 7 true (Escape.input c)) c.s).au.raw)
    (hx : ∀ k, 1 ≤ k → k ≤ 7 → Ax ≤ (iter k (step 7 true (Escape.input c)) c.s).ah.raw)
    (hz0 : 256 * EscapeRegion.dvzMin + 1016 ≤ 2 * c.s.au.raw - c.s.au1.raw + 15 * Az)
    (hx0 : 256 * EscapeRegion.dvxMin + 1016 ≤ 2 * c.s.ah.raw - c.s.ah1.raw + 15 * Ax) :
    IncrProp EscapeRegion.dvzMin EscapeRegion.dvxMin c := by
  have h1 := tick_dvz_lower c Az hFz hz
  have h2 := tick_dvx_lower c Ax hFx hx
  unfold IncrProp
  omega


namespace EscapeRegion
open ExpVibecheck

/-- The full region of `Tools/BoxProbe.lean` at scale 1.0 (output of `boxprobe emit 1000`): 35-45 m/s, flight
path -0.1..0.05, alpha 0.10..0.16, altitude 600-1250 m, and the derivative fields `ah`, `au`, `ah1`, `au1` free
over [-2.4, 2.1] and [1.1, 13.4] m/s^2, subject to `cons`. -/
def fullBox : CLOf Iv := CLOf.ofList [.box (0) (0), .box (39321600) (81920000), .box (2293760) (2949120),
  .box (-262144) (147456), .box (64291) (65510), .box (1966) (12452), .box (1966) (13763),
  .box (101580800) (184156160), .box (3997696) (5963776), .box (-111411) (124518), .box (-419430) (6554),
  .box (0) (0), .box (-157286) (137626), .box (78643) (871629), .box (-19661) (30802), .box (-157286) (137626),
  .box (72090) (878182), .box (-268698) (144179), .box (-275251) (144179), .box (4391) (22610)]

/-- A corner of the full region: h 1250, vx 35, vz 1.75, dz 0.14375, dx = sqrt(1 - dz^2) (raw 64855), q 0.03,
rpm 1550, tmap 91, udot 1.9, wdot -6.4, ah -2.4, au 1.2, qd -0.3, ah1 -2.4, au1 1.2, pvz = pvz2 = 1.75,
elevator 0.345 (raw = round(value * 65536); no value needed nudging). -/
def cBad : CLOf Fx := ⟨⟨⟨0⟩, ⟨81920000⟩, ⟨2293760⟩, ⟨114688⟩, ⟨64855⟩, ⟨9421⟩, ⟨1966⟩, ⟨101580800⟩, ⟨5963776⟩,
  ⟨124518⟩, ⟨-419430⟩, ⟨0⟩, ⟨-157286⟩, ⟨78643⟩, ⟨-19661⟩, ⟨-157286⟩, ⟨78643⟩, ⟨114688⟩, ⟨114688⟩⟩, ⟨22610⟩⟩

/-- The one-tick property is FALSE on the interval route's full region: `cBad` lies in `fullBox` and satisfies
every linear constraint in `cons`, yet its vz increment over the tick is below `dvzMin` (about -0.024 m/s
against the required +0.031 m/s). The derivative fields (`au`, `ah`, ...) are free coordinates of the region,
so the box contains `au = 1.2` m/s^2 next to a physical state (low alpha, low speed, high altitude) whose
evaluated vertical acceleration is about -1 m/s^2; the interval route cannot prove the property there because
it does not hold there. -/
theorem full_region_counterexample : fullBox.Mem cBad ∧ (∀ l ∈ cons, l.Holds cBad) ∧
    ¬ IncrProp dvzMin dvxMin cBad := by decide +kernel

end EscapeRegion

#print axioms three_mul_raw
#print axioms iter8_sum
#print axioms tick_dvz_lower
#print axioms tick_dvz_upper
#print axioms tick_dvx_lower
#print axioms tick_dvx_upper
#print axioms incr_of_substeps
#print axioms EscapeRegion.full_region_counterexample

end ExpJsb
