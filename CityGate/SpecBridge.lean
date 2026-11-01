import CityGate.Safety
import CityGate.SpecMap
import GateSafety.ProofsU
import Spec.CitySafetyChecks

/-! # The city gate against the reviewed spec

`cityGate_spec_safe_funnel_of` proves `CitySafety.Safe cityMap specFilter`. The gate's crash is the spec's crash
(`GCrash`, which allows a landing), so gate safety gives spec safety directly. The theorem's hypotheses are:
- the clearance test is sound against it;
- the funnel assumption (`FunnelSoundR`);
- checked starts;
- crash-free starts (`startClearB`, decided).

`SpecBridgeNative` discharges the last two by running the plant. -/

namespace CityGate.SpecBridge
open GateSafety

/-! ## The map -/

theorem max_max_self (a x : Rat) : max a (max a x) = max a x := by
  by_cases h : a ≤ x
  · have e : max a x = x := by rw [Rat.max_def]; simp [h]
    rw [e, e]
  · have e : max a x = a := by rw [Rat.max_def]; simp [h]
    rw [e, Rat.max_def]; simp

theorem node_floor (a b : Nat) : max cityMap.floor (node a b) = node a b := by
  simp only [cityMap, node]
  exact max_max_self _ _

theorem cityMap_terrain (x y : Rat) : cityMap.terrain x y = terrainAt x y := by
  have hx : CitySafety.clampR 0 ((gridN - 1 : Nat) : Rat) ((x + 3000) / 20) = gridCoord gridX0 x := by
    simp only [CitySafety.clampR, gridCoord, gridX0, gridStep]
    congr 2; grind
  have hy : CitySafety.clampR 0 ((gridN - 1 : Nat) : Rat) ((y + 3000) / 20) = gridCoord gridY0 y := by
    simp only [CitySafety.clampR, gridCoord, gridY0, gridStep]
    congr 2; grind
  have hf : ∀ a b, max cityMap.floor (cityMap.height a b) = node a b := fun a b => node_floor a b
  simp only [CitySafety.CityMap.terrain, hf]
  simp only [cityMap, terrainAt, hx, hy, square]
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

def toSurf (u : CitySafety.Surfaces) : Surf := ⟨u.elev, u.ail, u.rud, u.thr, u.brake⟩
def ofSurf (a : Surf) : CitySafety.Surfaces := ⟨a.elev, a.ail, a.rud, a.thr, a.brk⟩

/-- The controls of the first frame, flown before the gate starts (it needs one frame's observation): centred,
throttle idle, brakes released. -/
def firstSurf : Surf := ⟨0, 0, 0, 0, 0⟩

/-- The aircraft after the first frame from plant state `s`: where the gate starts. -/
def firstPlane (s : JsbExact.State Float) : Plane := (planeOf s FloatArray.empty).step firstSurf

/-- The filter's memory: `none` before the first frame; then the last observation, the gate's memory and the
controller it holds. -/
abbrev Mem' := Option (FloatArray × Mem × Ctl)

/-- One frame of the gate as a filter. The first frame flies `firstSurf` and starts the gate on the result. After
that, the controls are those the gate's frame applies: the first checked candidate, else the held controller
(`Gate.frame`). The memory is the gate's after that frame. -/
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

/-! ## The gate's crash is the spec's -/

/-- The gate's crash: the spec's crash of the aircraft's plant state. It allows a landing (wheels on the runway). -/
def GCrash (pl : Plane) : Prop := CitySafety.Crash cityMap pl.st

/-- The gate's landed: the spec's `Landed` of the aircraft's plant state. The closed loop ends there, as the spec's
`Reach` does. -/
def GLanded (pl : Plane) : Prop := CitySafety.Landed cityMap pl.st

/-- **The funnel assumption.** The end-of-escape test is `inFunnel`, so this says: from the landing funnel, the
autoland's flight does not crash until it has landed (up to and including the frame it lands on), under the spec's
crash rule, which allows a landing. Only for the rollouts the gate flies (`TermSoundRU`). -/
def FunnelSoundR : Prop := TermSoundRU cityGate GCrash GLanded GInit

theorem clearSound_of (hc : ∀ e pl, clearAt e pl = true → ¬ GCrash pl) : ClearSound cityGate GCrash :=
  fun x hx => (cityGate_clear x hx).elim fun e he => hc e x.2 he

/-! ## Controls in range -/

/-- Every control the gate applies is finite and in range, so the spec's clamp changes nothing (`outputsInRange`). -/
def OutputsInRange : Prop :=
  ∀ p u, CitySafety.Reach cityMap specFilter p → u.Valid →
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
  rw [e, clampTo_idem m1 m2 p1, clampTo_idem m1 m2 p1, clampTo_idem m1 m2 p1, clampTo_idem z0 z1 p1,
    clampTo_idem z0 z1 p1]

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

/-! ## Correspondence: every spec state is a gate state -/

/-- What a reachable state of `specFilter` is: a spec start before the first frame, afterwards a reachable state of
the gate with the same plant state. -/
def Corr (p : JsbExact.State Float × Mem') : Prop :=
  match p.2 with
  | none => CitySafety.Init p.1
  | some (ob, mc) => GateSafety.ReachU cityGate GLanded GInit (planeOf p.1 ob, mc)

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

theorem reach_corr (hOut : OutputsInRange) : ∀ p, CitySafety.Reach cityMap specFilter p → Corr p := by
  intro p hp
  induction hp with
  | init h => exact h
  | @step p u hu hnl hp ih =>
    have hs := frame_fst p u (hOut p u hp hu)
    obtain ⟨s, m⟩ := p
    cases m with
    | none =>
      have e : specFilter.frame (s, none) u =
          ((firstPlane s).st, some ((firstPlane s).ob, cityGate.m₀, cityGate.start (firstPlane s))) := by
        exact Prod.ext hs rfl
      rw [e]
      exact GateSafety.ReachU.init ⟨s, ih, rfl⟩
    | some v =>
      obtain ⟨ob, m, c⟩ := v
      have hg := GateSafety.ReachU.step (toSurf u) hnl ih
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
      have h1 : (specFilter.frame (s, some (ob, m, c)) u).1 =
          (cityGate.frame (planeOf s ob, (m, c)) (toSurf u)).1.st := by
        dsimp only at hs
        rw [ha] at hs
        rw [hg1, hst]; exact hs
      unfold Corr
      rw [h2]
      dsimp only
      rw [h1, planeOf_eta s ob hg1]
      exact hg

theorem reach_gate (p : JsbExact.State Float × Mem') (hp : CitySafety.Reach cityMap specFilter p) :
    GateSafety.ReachU cityGate GLanded GInit (gateState p) := by
  have hc := reach_corr outputsInRange p hp
  obtain ⟨s, m⟩ := p
  cases m with
  | none => exact GateSafety.ReachU.init ⟨s, hc, rfl⟩
  | some v => obtain ⟨ob, mc⟩ := v; exact hc

/-! ## Crash-free starts, decided -/

theorem min_le_l (a b : Rat) : min a b ≤ a := by rw [Rat.min_def]; split <;> grind
theorem min_le_r (a b : Rat) : min a b ≤ b := by rw [Rat.min_def]; split <;> grind
theorem le_max_l (a b : Rat) : a ≤ max a b := by rw [Rat.max_def]; split <;> grind
theorem le_max_r (a b : Rat) : b ≤ max a b := by rw [Rat.max_def]; split <;> grind

/-- The least and greatest of `f` over `ps` (`d` if empty). -/
def minOf (f : CitySafety.Pt → Rat) (ps : List CitySafety.Pt) (d : Rat) : Rat := ps.foldr (fun q m => min (f q) m) d
def maxOf (f : CitySafety.Pt → Rat) (ps : List CitySafety.Pt) (d : Rat) : Rat := ps.foldr (fun q m => max (f q) m) d

theorem minOf_le (f : CitySafety.Pt → Rat) (d : Rat) :
    ∀ (ps : List CitySafety.Pt) (q : CitySafety.Pt), q ∈ ps → minOf f ps d ≤ f q
  | [], _, h => by cases h
  | a :: ps, q, h => by
    simp only [minOf, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_l _ _
    · exact Rat.le_trans (min_le_r _ _) (minOf_le f d ps q h)

theorem le_maxOf (f : CitySafety.Pt → Rat) (d : Rat) :
    ∀ (ps : List CitySafety.Pt) (q : CitySafety.Pt), q ∈ ps → f q ≤ maxOf f ps d
  | [], _, h => by cases h
  | a :: ps, q, h => by
    simp only [maxOf, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_l _ _
    · exact Rat.le_trans (le_maxOf f d ps q h) (le_max_r _ _)

/-- A coordinate between `a` and `b`, scaled to units, lies in the window `[⌊aS⌋, ⌈bS⌉]`. -/
theorem win {a q b : Rat} (h1 : a ≤ q) (h2 : q ≤ b) :
    (((a * S).floor : Int) : Rat) ≤ q * S ∧ q * S ≤ (((b * S).ceil : Int) : Rat) := by
  have f1 := Rat.floor_le (a * S)
  have c1 : b * S ≤ ((b * S).ceil : Rat) := Rat.le_ceil
  have m1 : a * S ≤ q * S := Rat.mul_le_mul_of_nonneg_right h1 (by simp only [S]; decide)
  have m2 : q * S ≤ b * S := Rat.mul_le_mul_of_nonneg_right h2 (by simp only [S]; decide)
  exact ⟨Rat.le_trans f1 m1, Rat.le_trans m2 c1⟩

/-- The fold's starting point: the first point of `ps` (so the span is exactly `ps`'s). -/
def d0 (ps : List CitySafety.Pt) : CitySafety.Pt := ps.headD ⟨0, 0, 0⟩

/-- `q` lies in the box spanned by `ps`'s coordinates. -/
def InSpan (ps : List CitySafety.Pt) (q : CitySafety.Pt) : Prop :=
  minOf (·.x) ps (d0 ps).x ≤ q.x ∧ q.x ≤ maxOf (·.x) ps (d0 ps).x ∧ minOf (·.y) ps (d0 ps).y ≤ q.y ∧
    q.y ≤ maxOf (·.y) ps (d0 ps).y ∧ minOf (·.z) ps (d0 ps).z ≤ q.z ∧ q.z ≤ maxOf (·.z) ps (d0 ps).z

theorem inSpan_of_mem {ps : List CitySafety.Pt} {q : CitySafety.Pt} (h : q ∈ ps) : InSpan ps q :=
  ⟨minOf_le _ _ _ _ h, le_maxOf _ _ _ _ h, minOf_le _ _ _ _ h, le_maxOf _ _ _ _ h, minOf_le _ _ _ _ h,
    le_maxOf _ _ _ _ h⟩

/-- The hull of part of `ps` stays in `ps`'s span (the span is a box, which is convex). -/
theorem inSpan_hull {ps bs : List CitySafety.Pt} (hsub : ∀ p ∈ bs, p ∈ ps) {q : CitySafety.Pt}
    (hq : CitySafety.InHull bs q) : InSpan ps q := by
  have g := fun cx cy cz k (f : ∀ r ∈ bs, k ≤ cx * r.x + cy * r.y + cz * r.z) => CitySafety.hull_lin_ge cx cy cz k f hq
  have hp := fun r (hr : r ∈ bs) => inSpan_of_mem (hsub r hr)
  have l1 := g 1 0 0 (minOf (·.x) ps (d0 ps).x) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  have l2 := g (-1) 0 0 (-maxOf (·.x) ps (d0 ps).x) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  have l3 := g 0 1 0 (minOf (·.y) ps (d0 ps).y) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  have l4 := g 0 (-1) 0 (-maxOf (·.y) ps (d0 ps).y) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  have l5 := g 0 0 1 (minOf (·.z) ps (d0 ps).z) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  have l6 := g 0 0 (-1) (-maxOf (·.z) ps (d0 ps).z) (fun r hr => by have := hp r hr; simp only [InSpan] at this; grind)
  simp only [InSpan]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The span of `ps`, rounded out to units, is clear of buildings and above the terrain. -/
def spanClear (ps : List CitySafety.Pt) : Bool :=
  let xl := (minOf (·.x) ps (d0 ps).x * S).floor
  let xh := (maxOf (·.x) ps (d0 ps).x * S).ceil
  let yl := (minOf (·.y) ps (d0 ps).y * S).floor
  let yh := (maxOf (·.y) ps (d0 ps).y * S).ceil
  let zl := (minOf (·.z) ps (d0 ps).z * S).floor
  let zh := (maxOf (·.z) ps (d0 ps).z * S).ceil
  boxesClear xl xh yl yh zl zh && terrainClear xl xh yl yh zl

theorem not_solid_of_spanClear {ps : List CitySafety.Pt} (hc : spanClear ps = true) {q : CitySafety.Pt}
    (hq : InSpan ps q) : ¬ CitySafety.Solid cityMap q := by
  intro hs
  simp only [spanClear, Bool.and_eq_true] at hc
  obtain ⟨hb, ht⟩ := hc
  obtain ⟨x1, x2, y1, y2, z1, z2⟩ := hq
  obtain ⟨wx1, wx2⟩ := win x1 x2
  obtain ⟨wy1, wy2⟩ := win y1 y2
  obtain ⟨wz1, wz2⟩ := win z1 z2
  rcases solid_of_spec q hs with ⟨b, hbm, b1, b2, b3, b4, b5, b6⟩ | hter
  · exact box_case hb wx1 wx2 wy1 wy2 wz1 wz2 hbm b1 b2 b3 b4 b5 b6
  · exact terrain_case ht wx1 wx2 wy1 wy2 wz1 hter

/-- A start state is crash-free if its airframe points and sink rate are defined and the span of the points is
clear (decidable: `SpecBridgeNative` runs it on the 4 starts). -/
def startClearB (s : JsbExact.State Float) : Bool :=
  match CitySafety.bodyPoints.mapM (CitySafety.mapPoint cityMap s),
    CitySafety.wheelPoints.mapM (CitySafety.mapPoint cityMap s), CitySafety.sinkRate s with
  | some bs, some ws, some _ => spanClear (bs ++ ws)
  | _, _, _ => false

theorem not_crash_of_startClearB {s : JsbExact.State Float} (h : startClearB s = true) :
    ¬ CitySafety.Crash cityMap s := by
  unfold startClearB at h
  unfold CitySafety.Crash
  cases h1 : CitySafety.bodyPoints.mapM (CitySafety.mapPoint cityMap s) <;>
    cases h2 : CitySafety.wheelPoints.mapM (CitySafety.mapPoint cityMap s) <;>
    cases h3 : CitySafety.sinkRate s <;> simp only [h1, h2, h3] at h ⊢ <;> try simp at h
  rename_i bs ws v
  rintro (⟨q, hq, hs⟩ | ⟨w, hw, hs, _⟩)
  · exact not_solid_of_spanClear h (inSpan_hull (fun p hp => List.mem_append_left _ hp) hq) hs
  · exact not_solid_of_spanClear h (inSpan_of_mem (List.mem_append_right _ hw)) hs

/-! ## The theorem -/

/-- **The city gate is safe against the spec.** It takes four hypotheses:
- `hc`: the clearance test is sound against the spec's crash;
- `hF`: from the landing funnel, the autoland does not crash until it has landed (`FunnelSoundR`);
- `hInit`: the starts pass the gate's initial check;
- `hStart`: the starts are crash-free.

`SpecBridgeNative` discharges `hInit` and `hStart` by running the plant. -/
theorem cityGate_spec_safe_funnel_of (hc : ∀ e pl, clearAt e pl = true → ¬ GCrash pl) (hF : FunnelSoundR)
    (hInit : InitChecked cityGate GInit) (hStart : ∀ s, CitySafety.Init s → ¬ CitySafety.Crash cityMap s) :
    CitySafety.Safe cityMap specFilter := by
  have gsafe := GateSafety.safeU cityGate GCrash GLanded GInit (clearSound_of hc) hF hInit
  intro p hp
  obtain ⟨s, m⟩ := p
  cases m with
  | none => exact hStart s (reach_corr outputsInRange _ hp)
  | some v =>
    obtain ⟨ob, mc⟩ := v
    have h := gsafe (gateState (s, some (ob, mc))) (reach_gate (s, some (ob, mc)) hp)
    exact h

end CityGate.SpecBridge
