import CityGate.Safety
import GateSafety.ProofsR
import Spec.CitySafetyChecks

/-! # The city gate against the reviewed spec: `cityGate_spec_safe` proves `CitySafety.Safe cityMap specFilter`
from three named assumptions (`TermSoundR`, `InitChecked`, `AirframeNear`). -/

namespace CityGate.SpecBridge
open GateSafety

/-! ## The map -/

/-- An exported building box as a spec box (same six numbers, reordered). -/
def toBox (b : Box Rat) : CitySafety.Box := ⟨b.xmin, b.xmax, b.ymin, b.ymax, b.zmin, b.zmax⟩

/-- The exported city map (`CityGate.Map`) as a spec map: the same exact rational heights and boxes, no rounding. -/
def cityMap : CitySafety.CityMap where
  half := 3000
  spacing := 20
  n := gridN
  height := node
  boxes := boxes.toList.map toBox

theorem cityMap_terrain (x y : Rat) : cityMap.terrain x y = terrainAt x y := by
  have hx : CitySafety.clampR 0 ((gridN - 1 : Nat) : Rat) ((x + 3000) / 20) = gridCoord gridX0 x := by
    simp only [CitySafety.clampR, gridCoord, gridX0, gridStep]
    congr 2; grind
  have hy : CitySafety.clampR 0 ((gridN - 1 : Nat) : Rat) ((y + 3000) / 20) = gridCoord gridY0 y := by
    simp only [CitySafety.clampR, gridCoord, gridY0, gridStep]
    congr 2; grind
  simp only [CitySafety.CityMap.terrain, cityMap, terrainAt, hx, hy, square]
  rfl

/-- A point solid in the spec's sense is solid in the gate's sense. -/
theorem solid_of_spec (q : CitySafety.Pt) (h : CitySafety.Solid cityMap q) : Solid q.x q.y q.z := by
  rcases h with ht | ⟨b, hb, hc⟩
  · exact Or.inr (by rw [← cityMap_terrain]; exact ht)
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    exact Or.inl ⟨b', Array.mem_toList_iff.mp hb', hc⟩

/-! ## The filter -/

/-- The aircraft the gate sees for plant state `s` and last observation `ob`, placed at the map origin. -/
def planeOf (s : JsbExact.State Float) (ob : FloatArray) : Plane := ⟨s, ob, 0, 0⟩

def toSurf (u : CitySafety.Surfaces) : Surf := ⟨u.elev, u.ail, u.rud, u.thr⟩
def ofSurf (a : Surf) : CitySafety.Surfaces := ⟨a.elev, a.ail, a.rud, a.thr⟩

/-- The controls of the first frame, flown before the gate starts (it needs one frame's observation): centred,
throttle idle. -/
def firstSurf : Surf := ⟨0, 0, 0, 0⟩

/-- The aircraft after the first frame from plant state `s`: where the gate starts. -/
def firstPlane (s : JsbExact.State Float) : Plane := (planeOf s FloatArray.empty).step firstSurf

/-- The filter's memory: `none` before the first frame; then the last observation, the gate's memory and the
controller it holds. -/
abbrev Mem' := Option (FloatArray × Mem × Ctl)

/-- One frame of the gate as a filter. The first frame flies `firstSurf` and starts the gate on the result; after
that, the controls are those the gate's frame applies (`Gate.frame`: the first checked candidate, else the held
controller), and the memory is the gate's after that frame. -/
def specAct : Mem' → JsbExact.State Float → CitySafety.Surfaces → CitySafety.Surfaces × Mem'
  | none, s, _ =>
    let pl := firstPlane s
    (ofSurf firstSurf, some (pl.ob, cityGate.m₀, cityGate.start pl))
  | some (ob, m, c), s, u =>
    let pl := planeOf s ob
    let w := (cityGate.choose pl m c (toSurf u)).getD c
    let g := cityGate.frame (pl, (m, c)) (toSurf u)
    (ofSurf (cityGate.ctl w pl).1, some (g.1.ob, g.2))

/-- **The city gate as a spec filter.** -/
def specFilter : CitySafety.Filter := ⟨Mem', fun _ => none, specAct⟩

/-- The gate's starts: the aircraft after the first frame from one of the spec's starts. -/
def GInit (pl : Plane) : Prop := ∃ s, CitySafety.Init s ∧ pl = firstPlane s

/-- The gate state a closed-loop state of `specFilter` stands for: before the first frame, the gate's start after
it; afterwards, the gate's current state. -/
def gateState : JsbExact.State Float × Mem' → Plane × (Mem × Ctl)
  | (s, none) => (firstPlane s, (cityGate.m₀, cityGate.start (firstPlane s)))
  | (s, some (ob, mc)) => (planeOf s ob, mc)

/-- The aircraft whose reported position (`exactPos`) the gate's checks bound in a closed-loop state of
`specFilter`: its own before the first frame's end, else the gate's start after it (0.39 m along). -/
def refPlane (p : JsbExact.State Float × Mem') : Plane := (gateState p).1

/-! ## The crash cube, any size -/

/-- `Crash` with the cube's half-size `h` (m) as a parameter: `CrashH envHalf` is `Crash` (`crashH_envHalf`). -/
def CrashH (h : Rat) (p : Plane) : Prop :=
  match exactPos p with
  | some (x, y, z) => ∃ dx dy dz : Rat, -h ≤ dx ∧ dx ≤ h ∧ -h ≤ dy ∧ dy ≤ h ∧ -h ≤ dz ∧ dz ≤ h ∧
      Solid (x + dx) (y + dy) (z + dz)
  | none => True

theorem crashH_envHalf : CrashH envHalf = Crash := rfl

/-- `clear_sound` for any cube up to the 8.5 m keep-out. -/
theorem windowH (q d h : Rat) (k : Int) (hd1 : -h ≤ d) (hd2 : d ≤ h) (hk : h * S ≤ k) :
    (((q * S).floor - k : Int) : Rat) ≤ (q + d) * S ∧ (q + d) * S ≤ (((q * S).ceil + k : Int) : Rat) := by
  have h1 := Rat.floor_le (q * S)
  have h2 : q * S ≤ ((q * S).ceil : Rat) := Rat.le_ceil
  simp only [S, Rat.intCast_sub, Rat.intCast_add] at *
  constructor <;> grind

theorem clear_soundH {h : Rat} (hh : h ≤ 17 / 2) (e : Float) (p : Plane) : clearAt e p = true → ¬ CrashH h p := by
  intro hc hcr
  unfold clearAt at hc
  unfold CrashH at hcr
  cases hp : exactPos p with
  | none => simp [hp] at hc
  | some pos =>
    obtain ⟨x, y, z⟩ := pos
    simp only [hp, Bool.and_eq_true] at hc hcr
    obtain ⟨ht, hb⟩ := hc
    obtain ⟨dx, dy, dz, h1, h2, h3, h4, h5, h6, hs⟩ := hcr
    have hk : h * S ≤ (((keepBase + extraUnits e : Nat) : Int) : Rat) := by
      have : (136 : Int) ≤ ((keepBase + extraUnits e : Nat) : Int) := by simp [keepBase]; omega
      have := Rat.intCast_le_intCast.mpr this
      simp only [S] at *
      grind
    obtain ⟨wx1, wx2⟩ := windowH x dx h _ h1 h2 hk
    obtain ⟨wy1, wy2⟩ := windowH y dy h _ h3 h4 hk
    obtain ⟨wz1, wz2⟩ := windowH z dz h _ h5 h6 hk
    rcases hs with ⟨b, hbm, b1, b2, b3, b4, b5, b6⟩ | hter
    · exact box_case hb wx1 wx2 wy1 wy2 wz1 wz2 hbm b1 b2 b3 b4 b5 b6
    · exact terrain_case ht wx1 wx2 wy1 wy2 wz1 hter

/-! ## The assumptions -/

/-- Every control the gate applies is finite and in range, so the spec's clamp changes nothing (`outputsInRange`). -/
def OutputsInRange : Prop :=
  ∀ p u, CitySafety.Reach specFilter p → u.Valid →
    (specFilter.act p.2 p.1 u).1.clamp = (specFilter.act p.2 p.1 u).1

theorem clampTo_idem {lo hi : Float} (h1 : lo ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ hi) (x : Float) :
    CitySafety.clampTo lo hi (CitySafety.clampTo lo hi x) = CitySafety.clampTo lo hi x := by
  unfold CitySafety.clampTo
  by_cases a : lo ≤ x <;> by_cases b : x ≤ hi <;> simp [a, b, h1, h2, h3]

theorem ofSurf_clamp (u : Surf) : (ofSurf u.clamp).clamp = ofSurf u.clamp := by
  have m1 : ((-1 : Float) ≤ -1) := by decide +kernel
  have m2 : ((-1 : Float) ≤ 1) := by decide +kernel
  have p1 : ((1 : Float) ≤ 1) := by decide +kernel
  have z0 : ((0 : Float) ≤ 0) := by decide +kernel
  have z1 : ((0 : Float) ≤ 1) := by decide +kernel
  simp only [CitySafety.Surfaces.clamp, ofSurf, Surf.clamp]
  have e : clampIn = CitySafety.clampTo := rfl
  rw [e, clampTo_idem m1 m2 p1, clampTo_idem m1 m2 p1, clampTo_idem m1 m2 p1, clampTo_idem z0 z1 p1]

theorem firstSurf_clamp : (ofSurf firstSurf).clamp = ofSurf firstSurf := by
  have m1 : ((-1 : Float) ≤ 0) := by decide +kernel
  have z0 : ((0 : Float) ≤ 0) := by decide +kernel
  have z1 : ((0 : Float) ≤ 1) := by decide +kernel
  simp [CitySafety.Surfaces.clamp, ofSurf, firstSurf, CitySafety.clampTo, m1, z0, z1]

theorem ctl_clamp (c : Ctl) (pl : Plane) : ∃ v : Surf, (cityGate.ctl c pl).1 = v.clamp := by
  show ∃ v : Surf, (Ctl.ctl c pl).1 = v.clamp
  unfold Ctl.ctl
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **`OutputsInRange` holds**: every control the gate applies has been through `Surf.clamp`. -/
theorem outputsInRange : OutputsInRange := by
  intro p u _ _
  obtain ⟨s, m⟩ := p
  cases m with
  | none => exact firstSurf_clamp
  | some v =>
    obtain ⟨ob, m, c⟩ := v
    obtain ⟨w, hw⟩ := ctl_clamp ((cityGate.choose (planeOf s ob) m c (toSurf u)).getD c) (planeOf s ob)
    show (ofSurf (cityGate.ctl _ (planeOf s ob)).1).clamp = ofSurf (cityGate.ctl _ (planeOf s ob)).1
    rw [hw]; exact ofSurf_clamp w

/-- `q` lies in the cube of half-size `h` around `c`, per axis, boundary included. -/
def Near (h : Rat) (c : Rat × Rat × Rat) (q : CitySafety.Pt) : Prop :=
  c.1 - h ≤ q.x ∧ q.x ≤ c.1 + h ∧ c.2.1 - h ≤ q.y ∧ q.y ≤ c.2.1 + h ∧ c.2.2 - h ≤ q.z ∧ q.z ≤ c.2.2 + h

/-- The airframe points of plant state `s` are defined and lie within `h` m per axis of `pl`'s reported position. -/
def AirframeNearAt (h : Rat) (s : JsbExact.State Float) (pl : Plane) : Prop :=
  ∀ c, exactPos pl = some c → ∃ ps, CitySafety.airframe s = some ps ∧ ∀ q ∈ ps, Near h c q

/-- In every reachable state, the airframe points lie within `h` m of the gate's reported position (`refPlane`). -/
def AirframeNear (h : Rat) : Prop :=
  ∀ p, CitySafety.Reach specFilter p → AirframeNearAt h p.1 (refPlane p)

/-- **Assumption:** after the first frame, every reachable state's airframe points lie within `h` m per axis of
the position the plant reported for that same state. The c172p's points lie about 5.9 m from its CG at most;
this could be proved from bounds on the reported rotation matrix's entries and agreement of `Diag.loc` with
`report`. Checked along flights by `specbridgeinit`. -/
def AirframeNearGate (h : Rat) : Prop :=
  ∀ s ob mc, CitySafety.Reach specFilter (s, some (ob, mc)) → AirframeNearAt h s (planeOf s ob)

/-- The 4 starts' airframe points lie within `h` m of the gate's start, one frame on (decidable; see
`SpecBridgeNative`). -/
def AirframeNearInit (h : Rat) : Prop := ∀ s, CitySafety.Init s → AirframeNearAt h s (firstPlane s)

/-! ## Correspondence: every spec state is a gate state -/

/-- What a reachable state of `specFilter` is: a spec start before the first frame, afterwards a reachable state of
the gate with the same plant state. -/
def Corr (p : JsbExact.State Float × Mem') : Prop :=
  match p.2 with
  | none => CitySafety.Init p.1
  | some (ob, mc) => GateSafety.Reach cityGate GInit (planeOf p.1 ob, mc)

theorem plane_step_st (s : JsbExact.State Float) (ob : FloatArray) (a : Surf) :
    ((planeOf s ob).step a).st = (CitySafety.specStep s (ofSurf a).toInput).1 := rfl

/-- A gate frame from a plane at the map origin stays at the map origin. -/
theorem planeOf_eta (s : JsbExact.State Float) (ob : FloatArray) {a : Surf} {g : Plane}
    (hg : g = (planeOf s ob).step a) : planeOf g.st g.ob = g := by
  subst hg; rfl

/-- The plant step of the spec frame, once the clamp is known to change nothing. -/
theorem frame_fst (p : JsbExact.State Float × Mem') (u : CitySafety.Surfaces)
    (hc : (specFilter.act p.2 p.1 u).1.clamp = (specFilter.act p.2 p.1 u).1) :
    (specFilter.frame p u).1 = (CitySafety.specStep p.1 (specFilter.act p.2 p.1 u).1.toInput).1 := by
  simp only [CitySafety.Filter.frame]
  rw [hc]

theorem reach_corr (hOut : OutputsInRange) : ∀ p, CitySafety.Reach specFilter p → Corr p := by
  intro p hp
  induction hp with
  | init h => exact h
  | @step p u hu hp ih =>
    have hs := frame_fst p u (hOut p u hp hu)
    obtain ⟨s, m⟩ := p
    cases m with
    | none =>
      have e : specFilter.frame (s, none) u =
          ((firstPlane s).st, some ((firstPlane s).ob, cityGate.m₀, cityGate.start (firstPlane s))) := by
        exact Prod.ext hs rfl
      rw [e]
      exact GateSafety.Reach.init ⟨s, ih, rfl⟩
    | some v =>
      obtain ⟨ob, m, c⟩ := v
      have hg := GateSafety.Reach.step (toSurf u) ih
      generalize hw : (cityGate.choose (planeOf s ob) m c (toSurf u)).getD c = w at hs
      have hg1 : (cityGate.frame (planeOf s ob, (m, c)) (toSurf u)).1 =
          (planeOf s ob).step (cityGate.ctl w (planeOf s ob)).1 := by
        rw [← hw]; rfl
      have hst := plane_step_st s ob (cityGate.ctl w (planeOf s ob)).1
      have h2 : (specFilter.frame (s, some (ob, m, c)) u).2 =
          some ((cityGate.frame (planeOf s ob, (m, c)) (toSurf u)).1.ob,
            (cityGate.frame (planeOf s ob, (m, c)) (toSurf u)).2) := rfl
      have ha : (specFilter.act (some (ob, m, c)) s u).1 = ofSurf (cityGate.ctl w (planeOf s ob)).1 := by
        rw [← hw]; rfl
      have h1 : (specFilter.frame (s, some (ob, m, c)) u).1 = (cityGate.frame (planeOf s ob, (m, c)) (toSurf u)).1.st := by
        dsimp only at hs
        rw [ha] at hs
        rw [hg1, hst]; exact hs
      unfold Corr
      rw [h2]
      dsimp only
      rw [h1, planeOf_eta s ob hg1]
      exact hg

theorem reach_gate (p : JsbExact.State Float × Mem') (hp : CitySafety.Reach specFilter p) :
    GateSafety.Reach cityGate GInit (gateState p) := by
  have hc := reach_corr outputsInRange p hp
  obtain ⟨s, m⟩ := p
  cases m with
  | none => exact GateSafety.Reach.init ⟨s, hc, rfl⟩
  | some v => obtain ⟨ob, mc⟩ := v; exact hc

theorem airframeNear_of {h : Rat} (hi : AirframeNearInit h) (hg : AirframeNearGate h) : AirframeNear h := by
  intro p hp
  obtain ⟨s, m⟩ := p
  cases m with
  | none => exact hi s (reach_corr outputsInRange _ hp)
  | some v => obtain ⟨ob, mc⟩ := v; exact hg s ob mc hp

/-- `Near`, decided. -/
def nearB (h : Rat) (c : Rat × Rat × Rat) (q : CitySafety.Pt) : Bool :=
  decide (c.1 - h ≤ q.x ∧ q.x ≤ c.1 + h ∧ c.2.1 - h ≤ q.y ∧ q.y ≤ c.2.1 + h ∧ c.2.2 - h ≤ q.z ∧ q.z ≤ c.2.2 + h)

/-- `AirframeNearAt`, decided. -/
def nearAtB (h : Rat) (s : JsbExact.State Float) (pl : Plane) : Bool :=
  match exactPos pl with
  | none => true
  | some c => match CitySafety.airframe s with
    | none => false
    | some ps => ps.all (nearB h c)

theorem nearAt_of_B {h : Rat} {s : JsbExact.State Float} {pl : Plane} (hb : nearAtB h s pl = true) :
    AirframeNearAt h s pl := by
  intro c hc
  simp only [nearAtB, hc] at hb
  cases ha : CitySafety.airframe s with
  | none => simp [ha] at hb
  | some ps =>
    simp only [ha, List.all_eq_true, nearB, decide_eq_true_eq] at hb
    exact ⟨ps, rfl, fun q hq => hb q hq⟩

/-! ## Geometry -/

/-- The cube is convex: a hull of points in it stays in it. -/
theorem near_hull {h : Rat} {c : Rat × Rat × Rat} {ps : List CitySafety.Pt} (hp : ∀ q ∈ ps, Near h c q)
    {q : CitySafety.Pt} (hq : CitySafety.InHull ps q) : Near h c q := by
  have g := fun cx cy cz k (f : ∀ r ∈ ps, k ≤ cx * r.x + cy * r.y + cz * r.z) => CitySafety.hull_lin_ge cx cy cz k f hq
  have l1 := g 1 0 0 (c.1 - h) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  have l2 := g (-1) 0 0 (-(c.1 + h)) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  have l3 := g 0 1 0 (c.2.1 - h) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  have l4 := g 0 (-1) 0 (-(c.2.1 + h)) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  have l5 := g 0 0 1 (c.2.2 - h) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  have l6 := g 0 0 (-1) (-(c.2.2 + h)) (fun r hr => by have := hp r hr; simp only [Near] at this; grind)
  simp only [Near]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- A solid point near the aircraft's position is a crash of the cube. -/
theorem crashH_of_near {h : Rat} {pl : Plane} {c : Rat × Rat × Rat} (hc : exactPos pl = some c)
    {q : CitySafety.Pt} (hn : Near h c q) (hs : Solid q.x q.y q.z) : CrashH h pl := by
  obtain ⟨x, y, z⟩ := c
  simp only [Near] at hn
  simp only [CrashH, hc]
  refine ⟨q.x - x, q.y - y, q.z - z, by grind, by grind, by grind, by grind, by grind, by grind, ?_⟩
  have e1 : x + (q.x - x) = q.x := by grind
  have e2 : y + (q.y - y) = q.y := by grind
  have e3 : z + (q.z - z) = q.z := by grind
  rw [e1, e2, e3]; exact hs

/-! ## The theorem -/

/-- The spec's safety from the gate's own: no reachable gate state is a crash of the `h` m cube. -/
theorem spec_safe_of_gate_safe {h : Rat} (gsafe : GateSafety.Safe cityGate (CrashH h) GInit)
    (hNear : AirframeNear h) : CitySafety.Safe cityMap specFilter := by
  intro p hp hcr
  have hnc := gsafe _ (reach_gate p hp)
  change ¬ CrashH h (refPlane p) at hnc
  cases hc : exactPos (refPlane p) with
  | none => exact hnc (by simp only [CrashH, hc])
  | some c =>
    obtain ⟨ps, h1, hall⟩ := hNear p hp c hc
    simp only [CitySafety.Crash, h1] at hcr
    obtain ⟨q, hq, hs⟩ := hcr
    exact hnc (crashH_of_near hc (near_hull hall hq) (solid_of_spec q hs))

theorem clearSoundH {h : Rat} (hh : h ≤ 17 / 2) : ClearSound cityGate (CrashH h) :=
  fun x hx => (cityGate_clear x hx).elim fun e he => clear_soundH hh e x.2 he

/-- **The city gate is safe against the spec**, given three assumptions: `hT`, the end-of-escape test means safe
forever for the `h` m cube (known false for the current helix end test, see tracker #30); `hInit`, the 4 starts pass
the gate's initial check (`specbridgeinit` reports true); `hNear`, see `AirframeNear`. -/
theorem cityGate_spec_safe {h : Rat} (hh : h ≤ 17 / 2) (hT : TermSound cityGate (CrashH h))
    (hInit : InitChecked cityGate GInit) (hNear : AirframeNear h) : CitySafety.Safe cityMap specFilter :=
  spec_safe_of_gate_safe (GateSafety.safe cityGate (CrashH h) GInit (clearSoundH hh) hT hInit) hNear

/-- **`cityGate_spec_safe` with the end-of-escape assumption on the gate's own rollouts only** (`TermSoundR`: the
rollouts of its start controller, or of a candidate it proposes at a reachable state, which `TermSound` implies).
`TermSoundR` is currently known false for the helix end test (counterexamples in tracker #30), and false as stated
while `JsbExact` burns fuel; the theorem is conditional on a redesigned certifying end test. -/
theorem cityGate_spec_safe_R {h : Rat} (hh : h ≤ 17 / 2) (hT : TermSoundR cityGate (CrashH h) GInit)
    (hInit : InitChecked cityGate GInit) (hNear : AirframeNear h) : CitySafety.Safe cityMap specFilter :=
  spec_safe_of_gate_safe (GateSafety.safeR cityGate (CrashH h) GInit (clearSoundH hh) hT hInit) hNear

end CityGate.SpecBridge
