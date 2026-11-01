import CityGate.SpecBridge
import GateSafety.EndSets
import Spec.EndSetsCheck

/-! # City gate end sets for `CrashH`. -/

namespace CityGate.EndSets
open GateSafety CitySafety.EndSets CityGate.SpecBridge

/-- A gate position `(east, north, altitude)` (m) as a spec point. -/
def toPt (c : Rat × Rat × Rat) : CitySafety.Pt := ⟨c.1, c.2.1, c.2.2⟩

theorem near_iff_inBox {h : Rat} {c : Rat × Rat × Rat} {q : CitySafety.Pt} : Near h c q ↔ InBox h (toPt c) q :=
  Iff.rfl

theorem airframeNearAt_iff {h : Rat} {s : JsbExact.State Float} {pl : Plane} :
    AirframeNearAt h s pl ↔ ∀ c, exactPos pl = some c → AirframeWithinOf h s (toPt c) :=
  Iff.rfl

theorem spec_solid_of_solid {x y z : Rat} (h : Solid x y z) : CitySafety.Solid cityMap ⟨x, y, z⟩ := by
  rcases h with ⟨b, hb, hc⟩ | ht
  · exact Or.inr ⟨toBox b, List.mem_map.mpr ⟨b, Array.mem_toList_iff.mpr hb, rfl⟩, hc⟩
  · exact Or.inl (by rw [cityMap_terrain]; exact ht)

theorem not_crashH_of_clear {h : Rat} {pl : Plane} {c : Rat × Rat × Rat} (hc : exactPos pl = some c)
    (hclr : ∀ q, InBox h (toPt c) q → ¬ CitySafety.Solid cityMap q) : ¬ CrashH h pl := by
  obtain ⟨x, y, z⟩ := c
  simp only [CrashH, hc]
  rintro ⟨dx, dy, dz, h1, h2, h3, h4, h5, h6, hs⟩
  exact hclr ⟨x + dx, y + dy, z + dz⟩ (by simp only [InBox, toPt]; grind) (spec_solid_of_solid hs)

theorem Helix.not_crashH {H : Helix} {h e' : Rat} (hr : 0 ≤ H.r + H.δ) (he' : 0 ≤ e') (he : 2 * h * h ≤ e' * e')
    {pl : Plane} {c : Rat × Rat × Rat} (hc : exactPos pl = some c) (hconf : H.Conf (toPt c))
    (hg : H.Geo cityMap h e') : ¬ CrashH h pl :=
  not_crashH_of_clear hc (H.clear hr he' he hconf hg)

theorem Ray.not_crashH {R : Ray} {h : Rat} (hg0 : 0 ≤ R.g) {pl : Plane} {c : Rat × Rat × Rat}
    (hc : exactPos pl = some c) (hconf : R.Conf (toPt c)) (hg : R.Geo cityMap h) : ¬ CrashH h pl :=
  not_crashH_of_clear hc (R.clear hg0 hconf hg)

/-- The helix tubes as city-gate end sets; `Dyn` and its invariance are supplied by the model. -/
def helixEndSet (h e' : Rat) (he' : 0 ≤ e') (he : 2 * h * h ≤ e' * e') (Dyn : Helix → Ctl × Plane → Prop)
    (hconf : ∀ H x, Dyn H x → ∃ c, exactPos x.2 = some c ∧ H.Conf (toPt c))
    (hinv : ∀ H x, Dyn H x → Dyn H (cityGate.fly x)) : EndSet cityGate (CrashH h) Helix where
  Dyn := Dyn
  Geo H _ := 0 ≤ H.r + H.δ ∧ H.Geo cityMap h e'
  dyn_inv := hinv
  geo_inv _ _ _ g := g
  clear H x hd hg := by
    obtain ⟨c, hc, hcf⟩ := hconf H x hd
    exact Helix.not_crashH hg.1 he' he hc hcf hg.2

/-- The ray tubes as city-gate end sets; `Dyn` and its invariance are supplied by the model. -/
def rayEndSet (h : Rat) (Dyn : Ray → Ctl × Plane → Prop)
    (hconf : ∀ R x, Dyn R x → ∃ c, exactPos x.2 = some c ∧ R.Conf (toPt c))
    (hinv : ∀ R x, Dyn R x → Dyn R (cityGate.fly x)) : EndSet cityGate (CrashH h) Ray where
  Dyn := Dyn
  Geo R _ := 0 ≤ R.g ∧ R.Geo cityMap h
  dyn_inv := hinv
  geo_inv _ _ _ g := g
  clear R x hd hg := by
    obtain ⟨c, hc, hcf⟩ := hconf R x hd
    exact Ray.not_crashH hg.1 hc hcf hg.2

theorem cityGate_spec_safe_of_endSet {h : Rat} (hh : h ≤ 17 / 2) {Θ : Type} (E : EndSet cityGate (CrashH h) Θ)
    (hterm : ∀ x, Origin cityGate GInit x → ∀ n, cityGate.term (cityGate.flyN n x) = true → E.Mem (cityGate.flyN n x))
    (hInit : InitChecked cityGate GInit) (hNear : AirframeNear h) : CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_R hh (E.termSoundR hterm) hInit hNear

/-- `e' = 10` covers the half-diagonal of the bridge's 7 m cube. -/
theorem cityGate_spec_safe_of_tubes (DynH : Helix → Ctl × Plane → Prop) (DynR : Ray → Ctl × Plane → Prop)
    (hconfH : ∀ H x, DynH H x → ∃ c, exactPos x.2 = some c ∧ H.Conf (toPt c))
    (hinvH : ∀ H x, DynH H x → DynH H (cityGate.fly x))
    (hconfR : ∀ R x, DynR R x → ∃ c, exactPos x.2 = some c ∧ R.Conf (toPt c))
    (hinvR : ∀ R x, DynR R x → DynR R (cityGate.fly x))
    (hterm : ∀ x, Origin cityGate GInit x → ∀ n, cityGate.term (cityGate.flyN n x) = true →
      ((helixEndSet 7 10 (by decide +kernel) (by decide +kernel) DynH hconfH hinvH).sum (rayEndSet 7 DynR hconfR hinvR)).Mem
        (cityGate.flyN n x))
    (hInit : InitChecked cityGate GInit) (hNear : AirframeNear 7) : CitySafety.Safe cityMap specFilter :=
  cityGate_spec_safe_of_endSet (by decide +kernel) _ hterm hInit hNear

#audit_axioms Helix.not_crashH
#audit_axioms Ray.not_crashH
#audit_axioms cityGate_spec_safe_of_endSet
#audit_axioms cityGate_spec_safe_of_tubes

end CityGate.EndSets
