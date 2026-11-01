import CityGate.SpecBridgeNear

/-! `ReportMatchesObs` reduced to `NoWowReach`, `ReportBounded` and the pure `Float` fact `FtConvClose`. -/

namespace CityGate.SpecBridge
open JsbExact

/-- `JsbExact.step`'s `wow0`: under it, `step` shifts `ri` and `Diag.loc` by two different `Float` expressions. -/
def wow0 (s : State Float) : Bool := s.gears.toList.zipIdx.any fun (g, i) => g.wow && Gen.gears[i]![0]! == 0.0

theorem report_step (s : State Float) (u : Input Float) (h : wow0 s = false) :
    (CitySafety.report (step s u true).1).loc = (step s u true).2.loc ∧
      (CitySafety.report (step s u true).1).hsl = (step s u true).2.hsl := by
  unfold wow0 at h
  unfold step
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, rfl⟩

theorem reach_step : ∀ p, CitySafety.Reach specFilter p → ∀ ob mc, p.2 = some (ob, mc) →
    ∃ p0 i, CitySafety.Reach specFilter p0 ∧ p.1 = (step p0.1 i true).1 ∧
      ob = CityJsb.obs (step p0.1 i true).1 (step p0.1 i true).2 := by
  intro p hp
  induction hp with
  | init h => intro ob mc he; simp [specFilter] at he
  | @step p u hu hp _ =>
    intro ob mc he
    have hs := frame_fst p u (outputsInRange p u hp hu)
    obtain ⟨s, m⟩ := p
    cases m with
    | none =>
      refine ⟨(s, none), (ofSurf firstSurf).toInput, hp, hs, ?_⟩
      simp only [CitySafety.Filter.frame, specFilter, specAct, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.1]; rfl
    | some v =>
      obtain ⟨ob0, m, c⟩ := v
      refine ⟨(s, some (ob0, m, c)), (specFilter.act (some (ob0, m, c)) s u).1.toInput, hp, hs, ?_⟩
      simp only [CitySafety.Filter.frame, specFilter, specAct, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.1]; rfl

def NoWowReach : Prop := ∀ p, CitySafety.Reach specFilter p → wow0 p.1 = false

/-- Units: feet. -/
def ReportBounded (B : Rat) : Prop :=
  ∀ s ob mc, CitySafety.Reach specFilter (s, some (ob, mc)) →
    ∀ x ∈ [(CitySafety.report s).loc.y, (CitySafety.report s).loc.z, (CitySafety.report s).hsl],
      ∀ r, CitySafety.ratOf x = some r → Bd r B

/-- About `Float` alone (one rounded product, error about `3.4e-17 |x|` m, so true for `B = 10^14`); unproved. -/
def FtConvClose (B : Rat) : Prop :=
  ∀ x c, (VcFilter.ratOfFloat (0 + x * CityJsb.ft) = some c ∨ VcFilter.ratOfFloat (x * CityJsb.ft) = some c) →
    ∃ r, CitySafety.ratOf x = some r ∧ (Bd r B → Bd (r * CitySafety.ft - c) obsGap)

theorem reportMatchesObs_of {B : Rat} (hW : NoWowReach) (hB : ReportBounded B) (hF : FtConvClose B) :
    ReportMatchesObs := by
  intro s ob mc hp c hc
  obtain ⟨p0, i, hp0, hs, hob⟩ := reach_step _ hp ob mc rfl
  obtain ⟨hl, hh⟩ := report_step p0.1 i (hW p0 hp0)
  have hb := hB s ob mc hp
  simp only at hs
  subst hs hob
  generalize step p0.1 i true = r at hl hh hb hc
  obtain ⟨s, d⟩ := r
  simp only at hl hh hb hc
  have e1 : (CityJsb.obs s d)[1]! = d.loc.y * CityJsb.ft := rfl
  have e0 : (CityJsb.obs s d)[0]! = d.loc.z * CityJsb.ft := rfl
  have e2 : (CityJsb.obs s d)[2]! = d.hsl * CityJsb.ft := rfl
  simp only [exactPos, Plane.pos, planeOf, e0, e1, e2, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hc
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hc
  obtain ⟨rx, hrx, bx⟩ := hF _ _ (Or.inl hx)
  obtain ⟨ry, hry, bY⟩ := hF _ _ (Or.inl hy)
  obtain ⟨rz, hrz, bz⟩ := hF _ _ (Or.inr hz)
  rw [hl, hh]
  refine ⟨rx, ry, rz, hrx, hry, hrz, bx ?_, bY ?_, bz ?_⟩
  · exact hb _ (by simp [hl]) _ hrx
  · exact hb _ (by simp [hl]) _ hry
  · exact hb _ (by simp [hh]) _ hrz

end CityGate.SpecBridge
