import Spec.EndSetsCheck

/-! # End sets on a hand-made map: decided examples, randomised checks of the clearance lemmas, and the audit. -/

namespace CitySafety.EndSets
open CitySafety

/-! ## The map -/

/-- A tower at the centre, 500 m tall. -/
def tower : Box := ⟨-10, 10, -10, 10, 0, 500⟩

/-- A wall 70 to 80 m east of the centre, 100 m tall. -/
def wall : Box := ⟨70, 80, -10, 10, 0, 100⟩

/-- A 4 × 4 grid of 100 m squares over `[-150, 150]²`: flat at 10 m, with a 300 m peak at the north-east corner. -/
def hill : CityMap := ⟨150, 100, 4, fun i j => if i = 3 ∧ j = 3 then 300 else 10, [tower, wall]⟩

/-! ## Helices: one clear, one blocked -/

/-- Circling the tower at 40 ± 5 m, from 60 m up. -/
def helixClear : Helix := ⟨0, 0, 40, 5, 0, 60, 600⟩

/-- Circling at 80 ± 5 m, through the wall and over the peak's square. -/
def helixBlocked : Helix := ⟨0, 0, 80, 5, 0, 60, 600⟩

example : helixClear.geoB hill 6 9 500 = true := by decide +kernel
example : helixBlocked.geoB hill 6 9 500 = false := by decide +kernel

/-- `helixClear` as a funnel widening 1 m per 100 m climbed: still clear. -/
def funnelClear : Helix := { helixClear with s := 1 / 100 }

/-- Widening 1 m per 20 m climbed: the funnel reaches the tower before the tower's top. -/
def funnelBlocked : Helix := { helixClear with s := 1 / 20 }

example : funnelClear.geoB hill 6 9 500 = true := by decide +kernel
example : funnelBlocked.geoB hill 6 9 500 = false := by decide +kernel

theorem helixClear_geo : helixClear.Geo hill 6 9 := Helix.geo_of_geoB (top := 500) (by decide +kernel)

/-! ## Rays: one clear, one blocked -/

/-- East from 100 m south of the tower, 5 m wide, climbing 1 in 2 from 60 m. -/
def rayClear : Ray := ⟨0, -100, 1, 0, 5, 0, 60, 1 / 2, 600⟩

/-- North from the same point, straight into the tower. -/
def rayBlocked : Ray := ⟨0, -100, 0, 1, 5, 0, 60, 1 / 2, 600⟩

example : TopOK hill 500 = true := by decide +kernel
example : rayClear.geoB hill 6 500 = true := by decide +kernel
example : rayBlocked.geoB hill 6 500 = false := by decide +kernel

theorem rayClear_geo : rayClear.Geo hill 6 := Ray.geo_of_geoB (top := 500) (by decide +kernel)

/-! ## The hypotheses are satisfiable -/

example : helixClear.Conf ⟨40, 0, 60⟩ := by
  simp only [Helix.Conf, Helix.slack, InAnnulus, dist2, helixClear]; decide +kernel

example : rayClear.Conf ⟨100, -100, 110⟩ := by
  simp only [Ray.Conf, Ray.halfWidth, Ray.lateral, Ray.along, rayClear]; decide +kernel

example : ∀ q, InBox 6 ⟨40, 0, 60⟩ q → ¬ Solid hill q :=
  Helix.clear (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simp only [Helix.Conf, Helix.slack, InAnnulus, dist2, helixClear]; decide +kernel) helixClear_geo

example : ∀ q, InBox 6 ⟨100, -100, 110⟩ q → ¬ Solid hill q :=
  Ray.clear (by decide +kernel) (by decide +kernel)
    (by simp only [Ray.Conf, Ray.halfWidth, Ray.lateral, Ray.along, rayClear]; decide +kernel) rayClear_geo

/-! ## Randomised checks of the clearance lemmas; the blocked tubes show the sampling can find solid points -/

/-- The next state of a 64-bit linear congruential generator. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A rational in `[lo, hi]` from generator state `s`, on a grid of 1/1000 of the range. -/
def uniform (s : Nat) (lo hi : Rat) : Rat := lo + (hi - lo) * ((s / 2 ^ 32 % 1001 : Nat) : Rat) / 1000

/-- `Helix.Conf`, decided. -/
def helixConfB (H : Helix) (p : Pt) : Bool :=
  let w := H.slack p.z
  decide (H.zTop ≤ p.z ∨ (H.z0 ≤ p.z ∧ (H.r - w ≤ 0 ∨ (H.r - w) * (H.r - w) ≤ dist2 H.cx H.cy p) ∧
    dist2 H.cx H.cy p ≤ (H.r + w) * (H.r + w)))

/-- `Ray.Conf`, decided. -/
def rayConfB (R : Ray) (p : Pt) : Bool :=
  decide (R.zTop ≤ p.z ∨ (-R.halfWidth p.z ≤ R.lateral p ∧ R.lateral p ≤ R.halfWidth p.z ∧ 0 ≤ R.along p ∧
    R.z0 + R.g * R.along p ≤ p.z))

/-- (positions kept by `conf`, solid points found in their boxes of half-size `e`) over `n` samples. -/
def sampleHits (M : CityMap) (conf : Pt → Bool) (x0 x1 y0 y1 z0 z1 e : Rat) (n : Nat) : Nat × Nat := Id.run do
  let mut s := 12345
  let mut kept := 0
  let mut hits := 0
  for _ in [0:n] do
    s := lcg s; let px := uniform s x0 x1
    s := lcg s; let py := uniform s y0 y1
    s := lcg s; let pz := uniform s z0 z1
    let p : Pt := ⟨px, py, pz⟩
    if conf p then
      kept := kept + 1
      s := lcg s; let qx := uniform s (px - e) (px + e)
      s := lcg s; let qy := uniform s (py - e) (py + e)
      s := lcg s; let qz := uniform s (pz - e) (pz + e)
      if decide (Solid M ⟨qx, qy, qz⟩) then hits := hits + 1
  return (kept, hits)

#guard (sampleHits hill (helixConfB helixClear) (-45) 45 (-45) 45 60 70 6 3000).2 == 0
#guard (sampleHits hill (helixConfB helixClear) (-45) 45 (-45) 45 60 70 6 3000).1 > 500
#guard (sampleHits hill (helixConfB helixBlocked) (-85) 85 (-85) 85 60 70 6 3000).2 > 0
#guard (sampleHits hill (helixConfB funnelClear) (-50) 50 (-50) 50 60 600 6 3000).2 == 0
#guard (sampleHits hill (helixConfB funnelBlocked) (-30) 30 (-30) 30 400 510 6 6000).2 > 0
#guard (sampleHits hill (rayConfB rayClear) 0 2000 (-105) (-95) 60 1100 6 3000).2 == 0
#guard (sampleHits hill (rayConfB rayClear) 0 2000 (-105) (-95) 60 1100 6 3000).1 > 500
#guard (sampleHits hill (rayConfB rayBlocked) (-5) 5 (-100) 300 60 300 6 3000).2 > 0

/-! ## The spec rejects bad outputs -/

/-- A position below the tube's entry altitude is not in the helix tube. -/
example : ¬ helixClear.Conf ⟨40, 0, 59⟩ := by
  simp only [Helix.Conf, Helix.slack, InAnnulus, dist2, helixClear]; decide +kernel

/-- A position off the corridor is not in the ray tube. -/
example : ¬ rayClear.Conf ⟨100, -90, 200⟩ := by
  simp only [Ray.Conf, Ray.halfWidth, Ray.lateral, Ray.along, rayClear]; decide +kernel

/-- The blocked helix's `Geo` is false: a wall point in its annulus is above `z0 - e`. -/
example : ¬ helixBlocked.Geo hill 6 9 := fun h => by
  have := (h ⟨75, 0, 99⟩ (Or.inr ⟨wall, by simp [hill], by decide +kernel⟩)).2
    (by simp only [Helix.slack, InAnnulus, dist2, helixBlocked]; decide +kernel)
  revert this; decide +kernel

/-- The blocked ray's `Geo` is false: a tower point on its line is above the floor. -/
example : ¬ rayBlocked.Geo hill 6 := fun h => by
  have := (h ⟨0, 0, 400⟩ (Or.inr ⟨tower, by simp [hill], by decide +kernel⟩)).2
    (by simp only [Ray.halfWidth, Ray.lateral, Ray.reach, absR, rayBlocked]; decide +kernel)
    (by simp only [Ray.halfWidth, Ray.lateral, Ray.reach, absR, rayBlocked]; decide +kernel)
    (by simp only [Ray.along, Ray.reach, absR, rayBlocked]; decide +kernel)
  revert this; simp only [Ray.floorAt, Ray.along, Ray.reach, absR, rayBlocked]; decide +kernel

/-! ## Audit -/

#audit_axioms Helix.clear
#audit_axioms Ray.clear
#audit_axioms Helix.not_crash
#audit_axioms Ray.not_crash
#audit_axioms Helix.geo_of_geoB
#audit_axioms Ray.geo_of_geoB
#audit_axioms helixClear_geo
#audit_axioms rayClear_geo
#spec_surface Helix.not_crash in Spec
#spec_surface Ray.not_crash in Spec

end CitySafety.EndSets
