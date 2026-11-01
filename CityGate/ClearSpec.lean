import CityGate.SpecMap
import Spec.CitySafetyChecks

/-! `clear_spec_sound`: the gate's clearance test (`clearAt`) is sound for the spec's `Crash` on the demo map
(`CityGate.cityMap`). If it passes, every airframe point lies in a box that meets nothing solid, so neither the
body hull nor any wheel touches anything. -/

namespace CityGate
open CitySafety JsbExact

/-! ### The demo map in the spec's terms -/

theorem max_floor_node (a b : Nat) : max Landing.rwyZ (node a b) = node a b := by
  unfold node; grind

theorem cityMap_terrain (x y : Rat) : cityMap.terrain x y = terrainAt x y := by
  have hx : clampR 0 ((gridN - 1 : Nat) : Rat) ((x + 3000) / 20) = gridCoord gridX0 x := by
    simp only [clampR, gridCoord, gridX0, gridStep]
    congr 2; grind
  have hy : clampR 0 ((gridN - 1 : Nat) : Rat) ((y + 3000) / 20) = gridCoord gridY0 y := by
    simp only [clampR, gridCoord, gridY0, gridStep]
    congr 2; grind
  simp only [CityMap.terrain, cityMap, terrainAt, hx, hy, square, max_floor_node]
  rfl

/-- A point solid in the spec's sense is solid in the gate's sense. -/
theorem spec_solid (q : CitySafety.Pt) (h : CitySafety.Solid cityMap q) : Solid q.x q.y q.z := by
  rcases h with ht | ⟨b, hb, hc⟩
  · exact Or.inr (by rw [← cityMap_terrain]; exact ht)
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact Or.inl ⟨b', Array.mem_toList_iff.mp hb', hc⟩

/-! ### Bounds -/

theorem mul_bound (a w v : Rat) (h1 : -v ≤ w) (h2 : w ≤ v) : a * w ≤ rabs a * v ∧ -(rabs a * v) ≤ a * w := by
  unfold rabs
  by_cases ha : 0 ≤ a
  · have e : max a (-a) = a := by grind
    rw [e]
    have p1 := Rat.mul_le_mul_of_nonneg_left h2 ha
    have p2 := Rat.mul_le_mul_of_nonneg_left h1 ha
    constructor <;> grind
  · have ha' : 0 ≤ -a := by grind
    have e : max a (-a) = -a := by grind
    rw [e]
    have p1 := Rat.mul_le_mul_of_nonneg_left (show -w ≤ v by grind) ha'
    have p2 := Rat.mul_le_mul_of_nonneg_left h2 ha'
    constructor <;> grind

theorem getD_map_rabs (m : List Rat) (i : Nat) : (m.map rabs).getD i 0 = rabs (m.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> simp [rabs] <;> grind

/-- `w` lies within `±v` componentwise. -/
def Within (v w : Rat × Rat × Rat) : Prop :=
  -v.1 ≤ w.1 ∧ w.1 ≤ v.1 ∧ -v.2.1 ≤ w.2.1 ∧ w.2.1 ≤ v.2.1 ∧ -v.2.2 ≤ w.2.2 ∧ w.2.2 ≤ v.2.2

theorem mulRows_within (m : List Rat) {v w : Rat × Rat × Rat} (h : Within v w) :
    Within (absRows m v) (mulRows m w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [Within, absRows, mulRows, getD_map_rabs]
  have a0 := mul_bound (m.getD 0 0) _ _ h1 h2
  have a1 := mul_bound (m.getD 1 0) _ _ h3 h4
  have a2 := mul_bound (m.getD 2 0) _ _ h5 h6
  have a3 := mul_bound (m.getD 3 0) _ _ h1 h2
  have a4 := mul_bound (m.getD 4 0) _ _ h3 h4
  have a5 := mul_bound (m.getD 5 0) _ _ h5 h6
  have a6 := mul_bound (m.getD 6 0) _ _ h1 h2
  have a7 := mul_bound (m.getD 7 0) _ _ h3 h4
  have a8 := mul_bound (m.getD 8 0) _ _ h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- A map point in the box `[xlo, xhi] × [ylo, yhi] × [zlo, zhi]`. -/
def InBox (xlo xhi ylo yhi zlo zhi : Rat) (q : CitySafety.Pt) : Prop :=
  xlo ≤ q.x ∧ q.x ≤ xhi ∧ ylo ≤ q.y ∧ q.y ≤ yhi ∧ zlo ≤ q.z ∧ q.z ≤ zhi

theorem hull_box {xlo xhi ylo yhi zlo zhi : Rat} {ps : List CitySafety.Pt}
    (hp : ∀ p ∈ ps, InBox xlo xhi ylo yhi zlo zhi p) {q : CitySafety.Pt} (hq : InHull ps q) :
    InBox xlo xhi ylo yhi zlo zhi q := by
  have b1 := hull_lin_ge 1 0 0 xlo (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  have b2 := hull_lin_ge (-1) 0 0 (-xhi) (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  have b3 := hull_lin_ge 0 1 0 ylo (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  have b4 := hull_lin_ge 0 (-1) 0 (-yhi) (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  have b5 := hull_lin_ge 0 0 1 zlo (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  have b6 := hull_lin_ge 0 0 (-1) (-zhi) (fun p h => by have := hp p h; simp only [InBox] at this; grind) hq
  simp only [InBox]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem win_lo (a x : Rat) (k : Int) (hk : 0 ≤ k) (h : a ≤ x) : (((a * S).floor - k : Int) : Rat) ≤ x * S := by
  have h1 := Rat.floor_le (a * S)
  have h2 := Rat.mul_le_mul_of_nonneg_right h (show (0 : Rat) ≤ S by unfold S; decide)
  have h3 : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast hk
  simp only [Rat.intCast_sub]
  grind

theorem win_hi (a x : Rat) (k : Int) (hk : 0 ≤ k) (h : x ≤ a) : x * S ≤ (((a * S).ceil + k : Int) : Rat) := by
  have h1 : a * S ≤ ((a * S).ceil : Rat) := Rat.le_ceil
  have h2 := Rat.mul_le_mul_of_nonneg_right h (show (0 : Rat) ≤ S by unfold S; decide)
  have h3 : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast hk
  simp only [Rat.intCast_add]
  grind

/-- Nothing in a box that passes `boxClear` is solid. -/
theorem not_solid_of_box {k : Int} (hk : 0 ≤ k) {xlo xhi ylo yhi zlo zhi : Rat}
    (hc : boxClear k xlo xhi ylo yhi zlo zhi = true) {q : CitySafety.Pt} (hq : InBox xlo xhi ylo yhi zlo zhi q) :
    ¬ CitySafety.Solid cityMap q := by
  intro hs
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  simp only [boxClear, Bool.and_eq_true] at hc
  obtain ⟨ht, hb⟩ := hc
  rcases spec_solid q hs with ⟨b, hbm, b1, b2, b3, b4, b5, b6⟩ | hter
  · exact box_case hb (win_lo _ _ k hk q1) (win_hi _ _ k hk q2) (win_lo _ _ k hk q3) (win_hi _ _ k hk q4)
      (win_lo _ _ k hk q5) (win_hi _ _ k hk q6) hbm b1 b2 b3 b4 b5 b6
  · exact terrain_case ht (win_lo _ _ k hk q1) (win_hi _ _ k hk q2) (win_lo _ _ k hk q3) (win_hi _ _ k hk q4)
      (win_lo _ _ k hk q5) hter

theorem mapM_some {α β : Type} (f : α → Option β) (P : β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b ∧ P b) → ∃ bs, l.mapM f = some bs ∧ ∀ b ∈ bs, P b
  | [], _ => ⟨[], rfl, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb, hP⟩ := h a (by simp)
    obtain ⟨bs, hbs, hPs⟩ := mapM_some f P l (fun a' ha' => h a' (by simp [ha']))
    refine ⟨b :: bs, ?_, ?_⟩
    · simp [List.mapM_cons, hb, hbs]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hP
      · exact hPs x hx

/-! ### Soundness -/

theorem mapPoint_eq {s : State Float} {r : V3 Float} {ts tb : List Rat} {rx ry rz cx cy cz ly lz h : Rat}
    (hts : Gen.Ts2b.toList.mapM ratOf = some ts)
    (htb : [(report s).tb2l.a11, (report s).tb2l.a12, (report s).tb2l.a13, (report s).tb2l.a21,
      (report s).tb2l.a22, (report s).tb2l.a23, (report s).tb2l.a31, (report s).tb2l.a32,
      (report s).tb2l.a33].mapM ratOf = some tb)
    (hrx : ratOf r.x = some rx) (hry : ratOf r.y = some ry) (hrz : ratOf r.z = some rz)
    (hcx : ratOf s.cg.x = some cx) (hcy : ratOf s.cg.y = some cy) (hcz : ratOf s.cg.z = some cz)
    (hly : ratOf (report s).loc.y = some ly) (hlz : ratOf (report s).loc.z = some lz)
    (hh : ratOf (report s).hsl = some h) :
    mapPoint cityMap s r = some ⟨(ly + (mulRows tb (mulRows ts (rx - cx, ry - cy, rz - cz))).2.1) * ft,
      (lz + (mulRows tb (mulRows ts (rx - cx, ry - cy, rz - cz))).1) * ft,
      (h - (mulRows tb (mulRows ts (rx - cx, ry - cy, rz - cz))).2.2) * ft + cityMap.datum⟩ := by
  simp only [mapPoint, hts, htb, hrx, hry, hrz, hcx, hcy, hcz, hly, hlz, hh, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- **The clearance test is sound for the spec**: if it passes, the aircraft does not crash in the spec's sense. -/
theorem clear_spec_sound (e : Float) (p : Plane) : clearAt e p = true → ¬ CitySafety.Crash cityMap p.st := by
  intro hc
  unfold clearAt clearSpec at hc
  dsimp only at hc
  generalize hs : p.st = s at hc ⊢
  cases hts : ts2bL with
  | none => simp [hts] at hc
  | some ts =>
  cases htb : [(report s).tb2l.a11, (report s).tb2l.a12, (report s).tb2l.a13, (report s).tb2l.a21,
      (report s).tb2l.a22, (report s).tb2l.a23, (report s).tb2l.a31, (report s).tb2l.a32,
      (report s).tb2l.a33].mapM ratOf with
  | none => simp [hts, htb] at hc
  | some tb =>
  cases hcx : ratOf s.cg.x with
  | none => simp [hts, htb, hcx] at hc
  | some cx =>
  cases hcy : ratOf s.cg.y with
  | none => simp [hts, htb, hcx, hcy] at hc
  | some cy =>
  cases hcz : ratOf s.cg.z with
  | none => simp [hts, htb, hcx, hcy, hcz] at hc
  | some cz =>
  cases hly : ratOf (report s).loc.y with
  | none => simp [hts, htb, hcx, hcy, hcz, hly] at hc
  | some ly =>
  cases hlz : ratOf (report s).loc.z with
  | none => simp [hts, htb, hcx, hcy, hcz, hly, hlz] at hc
  | some lz =>
  cases hh : ratOf (report s).hsl with
  | none => simp [hts, htb, hcx, hcy, hcz, hly, hlz, hh] at hc
  | some h =>
  cases hv : sinkRate s with
  | none => simp [hts, htb, hcx, hcy, hcz, hly, hlz, hh, hv] at hc
  | some v =>
  simp only [hts, htb, hcx, hcy, hcz, hly, hlz, hh, hv, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.getD_some, Bool.and_eq_true] at hc
  obtain ⟨hpts, hbox⟩ := hc
  -- the box every airframe point lies in
  generalize hm : (max (ptMaxX - cx) (cx - ptMinX), max (ptMaxY - cy) (cy - ptMinY),
    max (ptMaxZ - cz) (cz - ptMinZ)) = m at hbox
  generalize hdd : absRows tb (absRows ts m) = dd at hbox
  have hk : (0 : Int) ≤ ((keepSpec + extraUnits e : Nat) : Int) := by omega
  have hft : (0 : Rat) ≤ ft := by unfold ft; grind
  have hpt : ∀ r ∈ contactPoints ++ flightGearPoints, ∃ q, mapPoint cityMap s r = some q ∧
      InBox ((ly - dd.2.1) * ft) ((ly + dd.2.1) * ft) ((lz - dd.1) * ft) ((lz + dd.1) * ft)
        ((h - dd.2.2) * ft + 9) ((h + dd.2.2) * ft + 9) q := by
    intro r hr
    simp only [ptsOK, List.all_eq_true] at hpts
    have hr' := hpts r hr
    cases hrx : ratOf r.x with
    | none => simp [hrx] at hr'
    | some rx =>
    cases hry : ratOf r.y with
    | none => simp [hrx, hry] at hr'
    | some ry =>
    cases hrz : ratOf r.z with
    | none => simp [hrx, hry, hrz] at hr'
    | some rz =>
    simp only [hrx, hry, hrz, decide_eq_true_eq] at hr'
    obtain ⟨x1, x2, y1, y2, z1, z2⟩ := hr'
    have hoff : Within m (rx - cx, ry - cy, rz - cz) := by
      subst hm; simp only [Within]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
    have hw := mulRows_within tb (mulRows_within ts hoff)
    rw [hdd] at hw
    refine ⟨_, mapPoint_eq (by unfold ts2bL at hts; exact hts) htb hrx hry hrz hcx hcy hcz hly hlz hh, ?_⟩
    generalize mulRows tb (mulRows ts (rx - cx, ry - cy, rz - cz)) = w at hw
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
    have d9 : cityMap.datum = 9 := rfl
    simp only [InBox, d9]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Rat.mul_le_mul_of_nonneg_right (by grind) hft
    · exact Rat.mul_le_mul_of_nonneg_right (by grind) hft
    · exact Rat.mul_le_mul_of_nonneg_right (by grind) hft
    · exact Rat.mul_le_mul_of_nonneg_right (by grind) hft
    · have := Rat.mul_le_mul_of_nonneg_right (show h - dd.2.2 ≤ h - w.2.2 by grind) hft; grind
    · have := Rat.mul_le_mul_of_nonneg_right (show h - w.2.2 ≤ h + dd.2.2 by grind) hft; grind
  have hsub : ∀ l, l ⊆ contactPoints ++ flightGearPoints → ∃ qs, l.mapM (mapPoint cityMap s) = some qs ∧
      ∀ q ∈ qs, InBox ((ly - dd.2.1) * ft) ((ly + dd.2.1) * ft) ((lz - dd.1) * ft) ((lz + dd.1) * ft)
        ((h - dd.2.2) * ft + 9) ((h + dd.2.2) * ft + 9) q :=
    fun l hl => mapM_some _ _ l (fun r hr => hpt r (hl hr))
  obtain ⟨bs, hbs, hbin⟩ := hsub bodyPoints (by
    intro r hr
    simp only [bodyPoints, List.mem_append] at hr ⊢
    rcases hr with hr | hr
    · exact Or.inl (List.mem_of_mem_drop hr)
    · exact Or.inr (List.mem_of_mem_drop hr))
  obtain ⟨ws, hws, hwin⟩ := hsub wheelPoints (by
    intro r hr
    simp only [wheelPoints, List.mem_append] at hr ⊢
    rcases hr with hr | hr
    · exact Or.inl (List.mem_of_mem_take hr)
    · exact Or.inr (List.mem_of_mem_take hr))
  intro hcr
  simp only [CitySafety.Crash, hbs, hws, hv] at hcr
  rcases hcr with ⟨q, hq, hsq⟩ | ⟨w, hw, hsw, _⟩
  · exact not_solid_of_box hk hbox (hull_box hbin hq) hsq
  · exact not_solid_of_box hk hbox (hwin w hw) hsw

end CityGate
