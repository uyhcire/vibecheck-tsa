import CityGate.TermSkeleton
import Spec.EndSetsCheck

/-! Non-emptiness check (a run, not a proof) of the skeleton's certified sets on real rollouts: from each spec start,
fly the gate's start escape until `cityGate.term` passes, build a funnel around the settled state, and test the
`Geo` and `Conf` halves of `C_k` (`Helix.geoB`/`Ray.geoB`, sound by `Helix.geo_of_geoB`/`Ray.geo_of_geoB`). The
`DynA` half is the informal proof's set, still `opaque`. `lake build termskelcheck && .lake/build/bin/termskelcheck`. -/

open CityGate CityGate.SpecBridge CityGate.EndSets CitySafety CitySafety.EndSets

def ratD (f : Float) : Rat := (CitySafety.ratOf f).getD 0

def fl (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

def rayConfB (R : Ray) (p : Pt) : Bool :=
  decide (R.zTop ≤ p.z) || (decide (-R.halfWidth p.z ≤ R.lateral p) && decide (R.lateral p ≤ R.halfWidth p.z) &&
    decide (0 ≤ R.along p) && decide (R.z0 + R.g * R.along p ≤ p.z))

def helixConfB (H : Helix) (p : Pt) : Bool :=
  let lo := H.r - H.slack p.z
  let hi := H.r + H.slack p.z
  decide (H.zTop ≤ p.z) || (decide (H.z0 ≤ p.z) && (decide (lo ≤ 0) || decide (lo * lo ≤ dist2 H.cx H.cy p)) &&
    decide (dist2 H.cx H.cy p ≤ hi * hi))

theorem rayConfB_sound {R : Ray} {p : Pt} (h : rayConfB R p = true) : R.Conf p := by
  simp only [rayConfB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Ray.Conf; grind

theorem helixConfB_sound {H : Helix} {p : Pt} (h : helixConfB H p = true) : H.Conf p := by
  simp only [helixConfB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Helix.Conf InAnnulus; grind

/-- A bound above every solid (m) for the `geoB` checks: the map's highest terrain or roof, plus 1. -/
def solidTop : Rat := ratD Esc.top + 1

def main : IO Unit := do
  for c in startConds do
    let pl := firstPlane c.state
    let mut x : Ctl × Plane := (cityGate.start pl, pl)
    let mut n := 0
    while !cityGate.term x && n < cityGate.horizon do
      x := cityGate.fly x
      n := n + 1
    match exactPos x.2 with
    | none => IO.println s!"start {c.psi}: position not finite"
    | some (px, py, pz) =>
      let p : Pt := ⟨px, py, pz⟩
      let dir := x.1.law.dir
      if dir == 0 then
        let psi := Float.atan2 (Esc.obN x.2.ob) (Esc.obE x.2.ob)
        let R : Ray := ⟨px, py, ratD psi.cos, ratD psi.sin, 10, 1 / 50, pz - 1, 1 / 20, 1200⟩
        let conf := rayConfB R p
        let geo := R.geoB cityMap 7 solidTop
        IO.println s!"start {c.psi}: term at frame {n}, ray at ({fl px}, {fl py}, z {fl pz}): Conf {conf}, Geo {geo}"
      else
        let s := Esc.seg ((x.1.record x.2).hist.extract ((x.1.record x.2).hist.size - Esc.HALF - 1)
          (x.1.record x.2).hist.size)
        let rr := s.vh / s.omega
        let cx := s.e.x - rr * s.e.psi.sin
        let cy := s.e.y + rr * s.e.psi.cos
        let H : Helix := ⟨ratD cx, ratD cy, ratD rr.abs, 10, 1 / 20, pz - 1, 1200⟩
        let conf := helixConfB H p
        let geo := H.geoB cityMap 7 10 solidTop
        IO.println s!"start {c.psi}: term at frame {n}, helix r {rr.abs} at z {fl pz}: Conf {conf}, Geo {geo}"
