import CityGate.SpecBridge

/-! `airframeNearGate`: `AirframeNearGate 7` from two facts about the plant's reported pose. -/

namespace CityGate.SpecBridge
open JsbExact
open CitySafety (ratOf mapPoint report mulRows)

def Bd (x b : Rat) : Prop := -b ≤ x ∧ x ≤ b

theorem Bd_mul {t o a b : Rat} (ht : Bd t a) (ho : Bd o b) : Bd (t * o) (a * b) := by
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨h3, h4⟩ := ho
  have p1 := Rat.mul_nonneg (show 0 ≤ a - t by grind) (show 0 ≤ b + o by grind)
  have p2 := Rat.mul_nonneg (show 0 ≤ a + t by grind) (show 0 ≤ b - o by grind)
  have p3 := Rat.mul_nonneg (show 0 ≤ a + t by grind) (show 0 ≤ b + o by grind)
  have p4 := Rat.mul_nonneg (show 0 ≤ a - t by grind) (show 0 ≤ b - o by grind)
  constructor <;> grind

theorem Bd_add {x y a b : Rat} (hx : Bd x a) (hy : Bd y b) : Bd (x + y) (a + b) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  constructor <;> grind

def absR (x : Rat) : Rat := if x < 0 then -x else x

theorem Bd_absR (x : Rat) : Bd x (absR x) := by
  unfold Bd absR; split <;> constructor <;> grind

def spread (a lo hi : Rat) : Rat := max (absR (a - lo)) (absR (a - hi))

theorem Bd_spread {a c lo hi : Rat} (h1 : lo ≤ c) (h2 : c ≤ hi) : Bd (a - c) (spread a lo hi) := by
  have l1 := Bd_absR (a - lo)
  have l2 := Bd_absR (a - hi)
  have m1 : absR (a - lo) ≤ spread a lo hi := by unfold spread; grind
  have m2 : absR (a - hi) ≤ spread a lo hi := by unfold spread; grind
  unfold Bd at *
  constructor <;> grind

theorem mulRows_bd (m : List Rat) (v : Rat × Rat × Rat) (A : Nat → Rat) {B0 B1 B2 : Rat}
    (hm : ∀ i < 9, Bd (m.getD i 0) (A i)) (h0 : Bd v.1 B0) (h1 : Bd v.2.1 B1) (h2 : Bd v.2.2 B2) :
    Bd (mulRows m v).1 (A 0 * B0 + A 1 * B1 + A 2 * B2) ∧ Bd (mulRows m v).2.1 (A 3 * B0 + A 4 * B1 + A 5 * B2) ∧
      Bd (mulRows m v).2.2 (A 6 * B0 + A 7 * B1 + A 8 * B2) := by
  simp only [mulRows]
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Bd_add (Bd_add (Bd_mul (hm _ (by decide)) h0) (Bd_mul (hm _ (by decide)) h1)) (Bd_mul (hm _ (by decide)) h2)

def tb2lEntries (s : State Float) : List Float :=
  [(report s).tb2l.a11, (report s).tb2l.a12, (report s).tb2l.a13, (report s).tb2l.a21, (report s).tb2l.a22,
    (report s).tb2l.a23, (report s).tb2l.a31, (report s).tb2l.a32, (report s).tb2l.a33]

/-- CG box (in): the template's CG (42.12, -1.34, 37.74) moved under 0.05 in over 156 s at full throttle. -/
def cgLo : Rat × Rat × Rat := (40, -3 / 2, 36)
def cgHi : Rat × Rat × Rat := (43, -6 / 5, 38)

def tbBound : Rat := 1 + 1 / 1000

/-- **Assumption:** after the first frame, the reported `Tb2l`'s entries are finite and at most `1 + 1/1000` in size
(it is a rotation), and the CG is finite and in `[cgLo, cgHi]`. -/
def PoseBounded : Prop :=
  ∀ s ob mc, CitySafety.Reach specFilter (s, some (ob, mc)) →
    (∃ T, (tb2lEntries s).mapM ratOf = some T ∧ ∀ i < 9, Bd (T.getD i 0) tbBound) ∧
    ∃ cx cy cz, ratOf s.cg.x = some cx ∧ ratOf s.cg.y = some cy ∧ ratOf s.cg.z = some cz ∧
      cgLo.1 ≤ cx ∧ cx ≤ cgHi.1 ∧ cgLo.2.1 ≤ cy ∧ cy ≤ cgHi.2.1 ∧ cgLo.2.2 ≤ cz ∧ cz ≤ cgHi.2.2

/-- The CG under fuel freeze: the mass balance of the template's tanks, which never drain. -/
def frozenCg : V3 Float := (massBalance CityJsb.template.cg CityJsb.template.tank0 CityJsb.template.tank1).cg

/-- Tanks never drain, so after the first frame the CG is `frozenCg`. -/
theorem reach_cg : ∀ p, CitySafety.Reach specFilter p → p.1.tank0 = CityJsb.template.tank0 ∧
    p.1.tank1 = CityJsb.template.tank1 ∧ (p.2.isSome → p.1.cg = frozenCg) := by
  intro p hp
  induction hp with
  | init h =>
    obtain ⟨c, _, rfl⟩ := h
    exact ⟨rfl, rfl, by simp [specFilter]⟩
  | @step p u _ _ ih =>
    obtain ⟨h0, h1, _⟩ := ih
    have e0 : (specFilter.frame p u).1.tank0 = p.1.tank0 := rfl
    have e1 : (specFilter.frame p u).1.tank1 = p.1.tank1 := rfl
    have ec : (specFilter.frame p u).1.cg = (massBalance CityJsb.template.cg p.1.tank0 p.1.tank1).cg := rfl
    refine ⟨e0.trans h0, e1.trans h1, fun _ => ?_⟩
    rw [ec, h0, h1]; rfl

/-- `frozenCg` is finite and in the CG box. -/
def cgFits : Bool :=
  match ratOf frozenCg.x, ratOf frozenCg.y, ratOf frozenCg.z with
  | some x, some y, some z => decide (cgLo.1 ≤ x ∧ x ≤ cgHi.1 ∧ cgLo.2.1 ≤ y ∧ y ≤ cgHi.2.1 ∧ cgLo.2.2 ≤ z ∧ z ≤ cgHi.2.2)
  | _, _, _ => false

theorem cgFits_true : cgFits = true := by decide +kernel

/-- **Assumption:** after the first frame, the reported `Tb2l`'s entries are finite and at most `1 + 1/1000` in size
(it is a rotation matrix computed in `Float`). -/
def TbBounded : Prop :=
  ∀ s ob mc, CitySafety.Reach specFilter (s, some (ob, mc)) →
    ∃ T, (tb2lEntries s).mapM ratOf = some T ∧ ∀ i < 9, Bd (T.getD i 0) tbBound

/-- Under fuel freeze, `PoseBounded`'s CG part is a theorem. -/
theorem poseBounded_of (hTb : TbBounded) : PoseBounded := by
  intro s ob mc hp
  refine ⟨hTb s ob mc hp, ?_⟩
  have hcg : s.cg = frozenCg := (reach_cg _ hp).2.2 (by simp)
  have hf := cgFits_true
  unfold cgFits at hf
  rw [hcg]
  generalize ratOf frozenCg.x = ox at hf ⊢
  generalize ratOf frozenCg.y = oy at hf ⊢
  generalize ratOf frozenCg.z = oz at hf ⊢
  cases ox <;> cases oy <;> cases oz <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  exact ⟨_, _, _, rfl, rfl, rfl, h1, h2, h3, h4, h5, h6⟩

def obsGap : Rat := 1 / 100

/-- After the first frame, `report`'s CG is within 1 cm per axis of the gate's `exactPos` (a theorem with gap 0,
`reportMatchesObs`, since `exactPos` reads `report`). -/
def ReportMatchesObs : Prop :=
  ∀ s ob mc, CitySafety.Reach specFilter (s, some (ob, mc)) → ∀ c, exactPos (planeOf s ob) = some c →
    ∃ ly lz hs, ratOf (report s).loc.y = some ly ∧ ratOf (report s).loc.z = some lz ∧ ratOf (report s).hsl = some hs ∧
      Bd (ly * CitySafety.ft - c.1) obsGap ∧ Bd (lz * CitySafety.ft - c.2.1) obsGap ∧
      Bd (hs * CitySafety.ft - c.2.2) obsGap

/-- Bound (ft) on each local component of point `r`'s offset from the CG, before the rotation's `1 + ε`. -/
def offBound (r : V3 Float) : Option Rat := do
  let ts ← Gen.Ts2b.toList.mapM ratOf
  let rx ← ratOf r.x
  let ry ← ratOf r.y
  let rz ← ratOf r.z
  let A := fun i => absR (ts.getD i 0)
  let (M0, M1, M2) := (spread rx cgLo.1 cgHi.1, spread ry cgLo.2.1 cgHi.2.1, spread rz cgLo.2.2 cgHi.2.2)
  return (A 0 * M0 + A 1 * M1 + A 2 * M2) + (A 3 * M0 + A 4 * M1 + A 5 * M2) + (A 6 * M0 + A 7 * M1 + A 8 * M2)

def pointsFit : Bool :=
  (CitySafety.contactPoints ++ CitySafety.flightGearPoints).all fun r =>
    match offBound r with
    | some L => decide (tbBound * L * CitySafety.ft + obsGap ≤ 7)
    | none => false

theorem pointsFit_true : pointsFit = true := by decide +kernel

theorem point_near {s : State Float} {c : Rat × Rat × Rat} {T : List Rat} {cx cy cz ly lz hs L : Rat}
    (r : V3 Float) (hT : (tb2lEntries s).mapM ratOf = some T) (hTb : ∀ i < 9, Bd (T.getD i 0) tbBound)
    (hcx : ratOf s.cg.x = some cx) (hcy : ratOf s.cg.y = some cy) (hcz : ratOf s.cg.z = some cz)
    (bx1 : cgLo.1 ≤ cx) (bx2 : cx ≤ cgHi.1) (by1 : cgLo.2.1 ≤ cy) (by2 : cy ≤ cgHi.2.1) (bz1 : cgLo.2.2 ≤ cz)
    (bz2 : cz ≤ cgHi.2.2) (hly : ratOf (report s).loc.y = some ly) (hlz : ratOf (report s).loc.z = some lz)
    (hhs : ratOf (report s).hsl = some hs) (gx : Bd (ly * CitySafety.ft - c.1) obsGap)
    (gy : Bd (lz * CitySafety.ft - c.2.1) obsGap) (gz : Bd (hs * CitySafety.ft - c.2.2) obsGap)
    (hL : offBound r = some L) (hfit : tbBound * L * CitySafety.ft + obsGap ≤ 7) :
    ∃ q, mapPoint s r = some q ∧ Near 7 c q := by
  simp only [offBound, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hL
  obtain ⟨ts, hts, rx, hrx, ry, hry, rz, hrz, hL⟩ := hL
  simp only [tb2lEntries] at hT
  simp only [mapPoint, hts, hT, hrx, hry, hrz, hcx, hcy, hcz, hly, hlz, hhs, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  refine ⟨_, rfl, ?_⟩
  have o0 := Bd_spread (a := rx) bx1 bx2
  have o1 := Bd_spread (a := ry) by1 by2
  have o2 := Bd_spread (a := rz) bz1 bz2
  obtain ⟨w0, w1, w2⟩ := mulRows_bd ts (rx - cx, ry - cy, rz - cz) (fun i => absR (ts.getD i 0))
    (fun i _ => Bd_absR _) o0 o1 o2
  obtain ⟨vn, ve, vd⟩ := mulRows_bd T _ (fun _ => tbBound) hTb w0 w1 w2
  generalize mulRows T (mulRows ts (rx - cx, ry - cy, rz - cz)) = v at vn ve vd ⊢
  obtain ⟨n, e, d⟩ := v
  have hft : Bd CitySafety.ft CitySafety.ft := by unfold Bd CitySafety.ft; constructor <;> decide +kernel
  have eq : ∀ x : Rat, Bd x (tbBound * (absR (ts.getD 0 0) * spread rx cgLo.fst cgHi.fst +
      absR (ts.getD 1 0) * spread ry cgLo.snd.fst cgHi.snd.fst + absR (ts.getD 2 0) * spread rz cgLo.snd.snd cgHi.snd.snd) +
      tbBound * (absR (ts.getD 3 0) * spread rx cgLo.fst cgHi.fst + absR (ts.getD 4 0) * spread ry cgLo.snd.fst cgHi.snd.fst +
        absR (ts.getD 5 0) * spread rz cgLo.snd.snd cgHi.snd.snd) +
      tbBound * (absR (ts.getD 6 0) * spread rx cgLo.fst cgHi.fst + absR (ts.getD 7 0) * spread ry cgLo.snd.fst cgHi.snd.fst +
        absR (ts.getD 8 0) * spread rz cgLo.snd.snd cgHi.snd.snd)) → Bd (x * CitySafety.ft) (tbBound * L * CitySafety.ft) := by
    intro x hx
    have := Bd_mul hx hft
    rw [← hL]
    unfold Bd at this ⊢
    constructor <;> grind
  have bn := eq n vn
  have be := eq e ve
  have bd := eq d vd
  unfold Bd at gx gy gz bn be bd
  simp only [Near]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem mapM_all {α β : Type} (f : α → Option β) (P : β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b ∧ P b) → ∃ bs, l.mapM f = some bs ∧ ∀ b ∈ bs, P b
  | [], _ => ⟨[], rfl, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb, hP⟩ := h a (by simp)
    obtain ⟨bs, hbs, hall⟩ := mapM_all f P l (fun x hx => h x (by simp [hx]))
    refine ⟨b :: bs, by simp [List.mapM_cons, hb, hbs], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hP
    · exact hall y hy

theorem airframeNearGate (hP : PoseBounded) (hR : ReportMatchesObs) : AirframeNearGate 7 := by
  intro s ob mc hp c hc
  obtain ⟨⟨T, hT, hTb⟩, cx, cy, cz, hcx, hcy, hcz, bx1, bx2, by1, by2, bz1, bz2⟩ := hP s ob mc hp
  obtain ⟨ly, lz, hs, hly, hlz, hhs, gx, gy, gz⟩ := hR s ob mc hp c hc
  have fit := pointsFit_true
  simp only [pointsFit, List.all_eq_true] at fit
  refine mapM_all _ _ _ fun r hr => ?_
  have hf := fit r hr
  cases hL : offBound r with
  | none => simp [hL] at hf
  | some L =>
    simp only [hL, decide_eq_true_eq] at hf
    exact point_near r hT hTb hcx hcy hcz bx1 bx2 by1 by2 bz1 bz2 hly hlz hhs gx gy gz hL hf

end CityGate.SpecBridge
