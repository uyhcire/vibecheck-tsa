import CityGate.Safety
import Spec.CitySafetyChecks

/-! # The city gate against the reviewed spec: `cityGate_spec_safe` proves `CitySafety.Safe cityMap specFilter`
from four named assumptions (`TermSound`, `InitChecked`, `OutputsInRange`, `SweepNear`). -/

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
  sorry

/-- A point solid in the spec's sense is solid in the gate's sense. -/
theorem solid_of_spec (q : CitySafety.Pt) (h : CitySafety.Solid cityMap q) : Solid q.x q.y q.z := by
  sorry

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

/-- The last observation held in the filter's memory (empty before the first frame). -/
def obOf : Mem' → FloatArray
  | none => FloatArray.empty
  | some (ob, _) => ob

/-- The aircraft the gate sees in a closed-loop state of `specFilter`. -/
def specPlane (p : JsbExact.State Float × Mem') : Plane := planeOf p.1 (obOf p.2)

/-! ## The crash cube, any size -/

/-- `Crash` with the cube's half-size `h` (m) as a parameter: `CrashH envHalf` is `Crash` (`crashH_envHalf`). -/
def CrashH (h : Rat) (p : Plane) : Prop :=
  match exactPos p with
  | some (x, y, z) => ∃ dx dy dz : Rat, -h ≤ dx ∧ dx ≤ h ∧ -h ≤ dy ∧ dy ≤ h ∧ -h ≤ dz ∧ dz ≤ h ∧
      Solid (x + dx) (y + dy) (z + dz)
  | none => True

theorem crashH_envHalf : CrashH envHalf = Crash := rfl

/-- `clear_sound` for any cube up to the 8.5 m keep-out. -/
theorem clear_soundH {h : Rat} (hh : h ≤ 17 / 2) (e : Float) (p : Plane) : clearAt e p = true → ¬ CrashH h p := by
  sorry

/-! ## The assumptions -/

/-- **Assumption:** every control the gate applies is finite and in range, so the spec's clamp changes nothing.
True for the pilot's valid controls by IEEE 754; for the escape law (which clamps) it means it never outputs NaN. -/
def OutputsInRange : Prop :=
  ∀ p u, CitySafety.Reach specFilter p → u.Valid →
    (specFilter.act p.2 p.1 u).1.clamp = (specFilter.act p.2 p.1 u).1

/-- `q` lies in the cube of half-size `h` around `c`, per axis, boundary included. -/
def Near (h : Rat) (c : Rat × Rat × Rat) (q : CitySafety.Pt) : Prop :=
  c.1 - h ≤ q.x ∧ q.x ≤ c.1 + h ∧ c.2.1 - h ≤ q.y ∧ q.y ≤ c.2.1 + h ∧ c.2.2 - h ≤ q.z ∧ q.z ≤ c.2.2 + h

/-- **Assumption:** each frame's airframe points (both ends) lie within `h` m per axis of the end position `c`.
Follows from points within `r` of the CG plus at most `d` m of travel per frame with `r + d ≤ h`; check numerically. -/
def SweepNear (h : Rat) : Prop :=
  ∀ p u, CitySafety.Reach specFilter p → u.Valid → ∀ c, exactPos (specPlane (specFilter.frame p u)) = some c →
    ∃ ps ps', CitySafety.airframe p.1 = some ps ∧ CitySafety.airframe (specFilter.frame p u).1 = some ps' ∧
      ∀ q ∈ ps ++ ps', Near h c q

/-! ## Correspondence: every spec state is a gate state -/

/-- What a reachable state of `specFilter` is: a spec start before the first frame, afterwards a reachable state of
the gate with the same plant state. -/
def Corr (p : JsbExact.State Float × Mem') : Prop :=
  match p.2 with
  | none => CitySafety.Init p.1
  | some (ob, mc) => GateSafety.Reach cityGate GInit (planeOf p.1 ob, mc)

theorem frame_some (p : JsbExact.State Float × Mem') (u : CitySafety.Surfaces) :
    ∃ ob mc, (specFilter.frame p u).2 = some (ob, mc) := by
  sorry

theorem reach_corr (hOut : OutputsInRange) : ∀ p, CitySafety.Reach specFilter p → Corr p := by
  sorry

/-! ## Geometry -/

/-- The cube is convex: a hull of points in it stays in it. -/
theorem near_hull {h : Rat} {c : Rat × Rat × Rat} {ps : List CitySafety.Pt} (hp : ∀ q ∈ ps, Near h c q)
    {q : CitySafety.Pt} (hq : CitySafety.InHull ps q) : Near h c q := by
  sorry

/-- A solid point near the aircraft's position is a crash of the cube. -/
theorem crashH_of_near {h : Rat} {pl : Plane} {c : Rat × Rat × Rat} (hc : exactPos pl = some c)
    {q : CitySafety.Pt} (hn : Near h c q) (hs : Solid q.x q.y q.z) : CrashH h pl := by
  sorry

/-! ## The theorem -/

/-- **The city gate is safe against the spec**, given the four assumptions. -/
theorem cityGate_spec_safe {h : Rat} (hh : h ≤ 17 / 2) (hT : TermSound cityGate (CrashH h))
    (hInit : InitChecked cityGate GInit) (hOut : OutputsInRange) (hNear : SweepNear h) :
    CitySafety.Safe cityMap specFilter := by
  intro p u hp hu hsw
  have gsafe := GateSafety.safe cityGate (CrashH h) GInit
    (fun x hx => (cityGate_clear x hx).elim fun e he => clear_soundH hh e x.2 he) hT hInit
  have hp' : CitySafety.Reach specFilter (specFilter.frame p u) := .step u hu hp
  obtain ⟨ob, mc, hsome⟩ := frame_some p u
  have hcorr := reach_corr hOut _ hp'
  simp only [Corr, hsome] at hcorr
  have hnc := gsafe _ hcorr
  have hpl : specPlane (specFilter.frame p u) = planeOf (specFilter.frame p u).1 ob := by
    simp only [specPlane, hsome, obOf]
  cases hc : exactPos (specPlane (specFilter.frame p u)) with
  | none => exact hnc (by rw [← hpl]; simp only [CrashH, hc])
  | some c =>
    obtain ⟨ps, ps', h1, h2, hall⟩ := hNear p u hp hu c hc
    simp only [CitySafety.SweptCrash, h1, h2] at hsw
    obtain ⟨q, hq, hs⟩ := hsw
    exact hnc (hpl ▸ crashH_of_near hc (near_hull hall hq) (solid_of_spec q hs))

end CityGate.SpecBridge
