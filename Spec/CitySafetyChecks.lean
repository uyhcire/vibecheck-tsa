import Spec.CitySafety
import Spec.Audit

namespace CitySafety
open JsbExact

/-! ## The decoder is exact -/

example : ratOf (Float.ofBits 0x3ff8000000000000) = some (3 / 2) := by decide +kernel
example : ratOf (Float.ofBits 0xc059000000000000) = some (-100) := by decide +kernel
example : ratOf (Float.ofBits 0x3fb999999999999a) = some (3602879701896397 / 36028797018963968) := by decide +kernel
example : ratOf (Float.ofBits 0x0000000000000001) = some ((1 : Rat) / 2 ^ 1074) := by decide +kernel
example : ratOf (Float.ofBits 0x7ff0000000000000) = none := by decide +kernel
example : ratOf (Float.ofBits 0x7ff8000000000000) = none := by decide +kernel

/-! ## `Init` is satisfiable -/

def north : StartCond := ⟨0, 0, 1500, 50, 0, 0.0223, 8⟩

example : Init north.state := ⟨north, List.mem_cons_self .., rfl⟩

/-! ## Hulls -/

theorem sum_replicate_zero (n : Nat) : (List.replicate n (0 : Rat)).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, ih, Rat.add_zero]

theorem combo_zeros (ps : List Pt) : combo (List.replicate ps.length 0) ps = ⟨0, 0, 0⟩ := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.replicate, combo, ih, Rat.add_zero, Rat.zero_mul]

theorem inHull_of_mem {ps : List Pt} {p : Pt} (h : p ∈ ps) : InHull ps p := by
  induction ps with
  | nil => cases h
  | cons a ps ih =>
    rcases List.mem_cons.mp h with rfl | h
    · refine ⟨1 :: List.replicate ps.length 0, by simp, ?_, by simp [sum_replicate_zero, Rat.add_zero], ?_⟩
      · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
        · decide
        · rw [List.eq_of_mem_replicate hw]; exact Rat.le_refl
      · simp [combo, combo_zeros, Rat.one_mul, Rat.add_zero]
    · obtain ⟨ws, hl, hn, hs, hc⟩ := ih h
      refine ⟨0 :: ws, by simp [hl], ?_, by simp [hs, Rat.zero_add],
        by simp [combo, hc, Rat.zero_mul, Rat.zero_add]⟩
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact Rat.le_refl
      · exact hn w hw

theorem hull_lin_ge (cx cy cz k : Rat) {ps : List Pt} (hp : ∀ p ∈ ps, k ≤ cx * p.x + cy * p.y + cz * p.z)
    {q : Pt} (hq : InHull ps q) : k ≤ cx * q.x + cy * q.y + cz * q.z := by
  obtain ⟨ws, hl, hn, hs, rfl⟩ := hq
  have key : ∀ (ps : List Pt) (ws : List Rat), ws.length = ps.length → (∀ w ∈ ws, 0 ≤ w) →
      (∀ p ∈ ps, k ≤ cx * p.x + cy * p.y + cz * p.z) →
      k * ws.sum ≤ cx * (combo ws ps).x + cy * (combo ws ps).y + cz * (combo ws ps).z := by
    intro ps
    induction ps with
    | nil => intro ws hl _ _; cases ws <;> simp_all [combo] <;> decide +kernel
    | cons p ps ih =>
      intro ws hl hn hp
      cases ws with
      | nil => simp at hl
      | cons w ws =>
        have h1 := ih ws (by simpa using hl) (fun v hv => hn v (by simp [hv])) (fun r hr => hp r (by simp [hr]))
        have h2 := Rat.mul_le_mul_of_nonneg_left (hp p (by simp)) (hn w (by simp))
        simp only [combo, List.sum_cons]
        grind
  have := key ps ws hl hn hp
  rw [hs] at this
  simpa using this

def idle : Surfaces := ⟨0, 0, 0, 0, 0⟩

theorem idle_valid : idle.Valid :=
  ⟨⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

/-! ## A hand-made map -/

def tower : Box := ⟨-50, 50, 150, 200, -3 / 2, 2000⟩

def pole : Box := ⟨3, 16 / 5, -1 / 2, 1 / 2, -3 / 2, 30⟩

theorem max00 : max (0 : Rat) 0 = 0 := by decide +kernel

def tiny : CityMap := ⟨3000, 20, 301, fun _ _ => 0, [tower, pole], 1000, 1100, 1000, 1040, 0, 0, 0⟩

theorem tiny_terrain (x y : Rat) : tiny.terrain x y = 0 := by
  simp [CityMap.terrain, tiny, Rat.sub_self, Rat.mul_zero, Rat.add_zero, max00]

-- `contactPoints ++ flightGearPoints` (CG at structural (42, 0, 38) in) of a level aircraft heading north, to the cm
def level (x y z : Rat) : List Pt :=
  [⟨x, y + 124 / 100, z - 146 / 100⟩, ⟨x - 109 / 100, y - 41 / 100, z - 136 / 100⟩,
   ⟨x + 109 / 100, y - 41 / 100, z - 136 / 100⟩, ⟨x, y + 202 / 100, z - 29 / 100⟩,
   ⟨x, y - 371 / 100, z - 76 / 100⟩,
   ⟨x - 546 / 100, y - 3 / 100, z + 54 / 100⟩, ⟨x + 546 / 100, y - 3 / 100, z + 54 / 100⟩,
   ⟨x, y + 123 / 100, z - 148 / 100⟩, ⟨x - 109 / 100, y - 41 / 100, z - 135 / 100⟩,
   ⟨x + 109 / 100, y - 41 / 100, z - 135 / 100⟩, ⟨x, y - 471 / 100, z - 53 / 100⟩,
   ⟨x - 589 / 100, y + 54 / 100, z + 31 / 100⟩, ⟨x + 589 / 100, y + 54 / 100, z + 31 / 100⟩,
   ⟨x, y + 122 / 100, z - 96 / 100⟩, ⟨x - 122 / 100, y - 43 / 100, z - 96 / 100⟩,
   ⟨x + 122 / 100, y - 43 / 100, z - 96 / 100⟩, ⟨x, y + 407 / 100, z - 7 / 100⟩,
   ⟨x, y + 407 / 100, z - 76 / 100⟩,
   ⟨x, y + 117 / 100, z + 56 / 100⟩, ⟨x, y - 539 / 100, z + 132 / 100⟩]

deriving instance DecidableEq for Pt

instance (b : Box) (q : Pt) : Decidable (b.Contains q) := by unfold Box.Contains; infer_instance

-- 50 m up, west of the pole and south of the tower: nothing is touched
example : ¬ HullHits tiny (level (-10) 0 50) := by
  rintro ⟨q, hq, hs⟩
  have hz := hull_lin_ge 0 0 1 48 (by decide +kernel) hq
  have hy := hull_lin_ge 0 (-1) 0 (-5) (by decide +kernel) hq
  rcases hs with h | ⟨b, hb, hc⟩
  · rw [tiny_terrain] at h; grind
  · simp [tiny] at hb; rcases hb with rfl | rfl <;> (simp [Box.Contains, tower, pole] at hc; grind)

-- sitting 1 m up, the nose gear is 0.46 m below the ground
example : Crash tiny (north.state) ∨ HullHits tiny (level 0 0 1) :=
  .inr ⟨_, inHull_of_mem (List.mem_cons_self ..), Or.inl (by rw [tiny_terrain]; decide +kernel)⟩

-- 20 m up next to the pole: no airframe point is in the pole, but the right wing between them is
example : (∀ p ∈ level 0 0 20, ¬ pole.Contains p) ∧ HullHits tiny (level 0 0 20) := by
  refine ⟨by decide +kernel, ⟨30576 / 10000, -3 / 100, 2054 / 100⟩, ?_,
    Or.inr ⟨pole, by simp [tiny], by decide +kernel⟩⟩
  exact ⟨[0, 0, 0, 0, 0, 22 / 100, 78 / 100] ++ List.replicate 13 0, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- A 2 cm ledge just inside the right wingtip (FlightGear's RIGHT_TIP), 20.10 to 20.12 m up. -/
def ledge : Box := ⟨588 / 100, 589 / 100, 1 / 2, 6 / 10, 2010 / 100, 2012 / 100⟩

def ledgeMap : CityMap := ⟨3000, 20, 301, fun _ _ => 0, [ledge], 1000, 1100, 1000, 1040, 0, 0, 0⟩

theorem ledgeMap_terrain (x y : Rat) : ledgeMap.terrain x y = 0 := by
  simp [CityMap.terrain, ledgeMap, Rat.sub_self, Rat.mul_zero, Rat.add_zero, max00]

-- sinking 0.25 m in one frame (32 m/s) past the ledge: neither frame touches it. Contact strictly between frames is
-- not counted (decision 5 in `Spec/CitySafety.lean`).
example : ¬ HullHits ledgeMap (level 0 0 20) ∧ ¬ HullHits ledgeMap (level 0 0 (20 - 1 / 4)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨q, hq, hs⟩
    have hz := hull_lin_ge 0 0 1 18 (by decide +kernel) hq
    have hl := hull_lin_ge (-1 / 2) 0 1 (3473 / 200) (by decide +kernel) hq
    rcases hs with h | ⟨b, hb, hc⟩
    · rw [ledgeMap_terrain] at h; grind
    · simp [ledgeMap] at hb; subst hb; simp [Box.Contains, ledge] at hc; grind
  · rintro ⟨q, hq, hs⟩
    have hz := hull_lin_ge 0 0 1 18 (by decide +kernel) hq
    have hl := hull_lin_ge (-3 / 4) 0 (-1) (-9791 / 400) (by decide +kernel) hq
    rcases hs with h | ⟨b, hb, hc⟩
    · rw [ledgeMap_terrain] at h; grind
    · simp [ledgeMap] at hb; subst hb; simp [Box.Contains, ledge] at hc; grind

/-- A runway under a level aircraft heading north at the origin; flat ground at 0, no buildings. -/
def rwyMap : CityMap := ⟨3000, 20, 301, fun _ _ => 0, [], -50, 50, -100, 100, 0, 0, 0⟩

theorem rwyMap_terrain (x y : Rat) : rwyMap.terrain x y = 0 := by
  simp [CityMap.terrain, rwyMap, Rat.sub_self, Rat.mul_zero, Rat.add_zero, max00]

instance (M : CityMap) (q : Pt) : Decidable (M.InRunwayLayer q) := by unfold CityMap.InRunwayLayer; infer_instance

-- resting on the runway (nose wheel at its surface, CG 1.46 m up): the body hull clears it and every wheel is in the
-- runway layer, so this contact is allowed (`Crash` with a gentle sink rate)
example : ¬ HullHits rwyMap (((level 0 0 (146 / 100)).drop 3).take 4 ++ (level 0 0 (146 / 100)).drop 10) ∧
    ∀ w ∈ (level 0 0 (146 / 100)).take 3 ++ ((level 0 0 (146 / 100)).drop 7).take 3, rwyMap.InRunwayLayer w := by
  refine ⟨?_, by decide +kernel⟩
  rintro ⟨q, hq, hs⟩
  have hz := hull_lin_ge 0 0 1 (1 / 2) (by decide +kernel) hq
  rcases hs with h | ⟨b, hb, _⟩
  · rw [rwyMap_terrain] at h; grind
  · simp [rwyMap] at hb

/-! ## The spec rejects a filter that does nothing -/

def passThrough : Filter := ⟨Unit, fun _ => (), fun _ _ u => (u, ())⟩

theorem reach_foldl {M : CityMap} {F : Filter} {p : State Float × F.σ} (hp : Reach M F p) :
    ∀ us : List Surfaces, (∀ u ∈ us, u.Valid) →
      (∀ k < us.length, ¬ Landed M ((us.take k).foldl F.frame p).1) → Reach M F (us.foldl F.frame p) := by
  intro us
  induction us generalizing p with
  | nil => intro _ _; exact hp
  | cons u us ih =>
    intro hu hl
    exact ih (.step u (hu u (by simp)) (hl 0 (by simp)) hp) (fun v hv => hu v (by simp [hv]))
      (fun k hk => hl (k + 1) (by simp; omega))

theorem not_safe_of_trace {M : CityMap} {F : Filter} {s : State Float} (hs : Init s) (us : List Surfaces)
    (hu : ∀ u ∈ us, u.Valid) (hl : ∀ k < us.length, ¬ Landed M ((us.take k).foldl F.frame (s, F.start s)).1)
    (hc : Crash M (us.foldl F.frame (s, F.start s)).1) : ¬ Safe M F :=
  fun h => h _ (reach_foldl (.init hs) us hu hl) hc

instance (M : CityMap) (q : Pt) : Decidable (Solid M q) := by unfold Solid; infer_instance

/-- Sufficient for `Crash`, not equivalent: an undefined pose, a body point in something solid, or a wheel in
something solid that is not a gentle runway contact. -/
def vertexCrash (M : CityMap) (s : State Float) : Bool :=
  match bodyPoints.mapM (mapPoint M s), wheelPoints.mapM (mapPoint M s), sinkRate s with
  | some bs, some ws, some v => bs.any (fun p => decide (Solid M p)) ||
      ws.any (fun w => decide (Solid M w ∧ ¬ (M.InRunwayLayer w ∧ v ≤ tdSinkMax)))
  | _, _, _ => true

set_option linter.unusedSimpArgs false in
theorem crash_of_vertex {M : CityMap} {s : State Float} (h : vertexCrash M s = true) : Crash M s := by
  unfold vertexCrash at h; unfold Crash
  cases h1 : bodyPoints.mapM (mapPoint M s) <;> cases h2 : wheelPoints.mapM (mapPoint M s) <;>
    cases h3 : sinkRate s <;> simp only [h1, h2, h3] at h ⊢ <;> try trivial
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨p, hp, hs⟩ | h
  · exact .inl ⟨p, inHull_of_mem hp, hs⟩
  · exact .inr h

def cruise : Surfaces := ⟨-0.0625, 0, 0, 0.75, 0⟩

theorem cruise_valid : cruise.Valid :=
  ⟨⟨-1 / 16, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨3 / 4, by decide +kernel, by decide +kernel, by decide +kernel⟩,
   ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

/-- The state after `n` frames of `cruise` from `north` under `passThrough`. -/
def cruiseAt (n : Nat) : State Float × Unit := (List.replicate n cruise).foldl passThrough.frame (north.state, ())

-- `Tools/CitySafetyDemo.lean` evaluates `h` by running the plant; `Lean.ofReduceBool` would be needed to use that here
theorem passThrough_unsafe_of_cruise (n : Nat) (hl : ∀ k < n, ¬ Landed tiny (cruiseAt k).1)
    (h : vertexCrash tiny (cruiseAt n).1 = true) : ¬ Safe tiny passThrough :=
  not_safe_of_trace ⟨north, List.mem_cons_self .., rfl⟩ _
    (fun u hu => by rw [List.eq_of_mem_replicate hu]; exact cruise_valid)
    (fun k hk => by
      rw [List.length_replicate] at hk
      rw [List.take_replicate, Nat.min_eq_left (Nat.le_of_lt hk)]
      exact hl k hk)
    (crash_of_vertex h)

/-! ## Audit -/

#spec_surface Safe in Spec
#audit_axioms inHull_of_mem
#audit_axioms hull_lin_ge
#audit_axioms crash_of_vertex
#audit_axioms passThrough_unsafe_of_cruise

end CitySafety
