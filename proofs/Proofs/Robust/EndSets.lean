import Proofs.Robust.Invariance
import CityGate.EndSets

/-! `Tube.Residual` is the one hypothesis not over ℝ: the `Float` gate frame read through `π`, against `Φ`. -/

namespace Proofs.Robust
open GateSafety CityGate CityGate.SpecBridge CityGate.EndSets CitySafety.EndSets

variable {n m : Type*} [Fintype n] [Fintype m] {S Θ : Type*}

structure Tube (S Θ : Type*) (n : Type*) [Fintype n] where
  π : Θ → S → n → ℝ
  Q : Θ → Matrix n n ℝ
  r : Θ → ℝ
  Φ : Θ → (n → ℝ) → (n → ℝ)
  lam : Θ → ℝ
  δ : Θ → ℝ
  A : Θ → S → Prop

def Tube.Dyn (T : Tube S Θ n) (θ : Θ) (x : S) : Prop := qn (T.Q θ) (T.π θ x) ≤ T.r θ ∧ T.A θ x

structure Tube.Valid (T : Tube S Θ n) : Prop where
  sym : ∀ θ, Sym (T.Q θ)
  lam_nonneg : ∀ θ, 0 ≤ T.lam θ
  contract : ∀ θ ξ, qn (T.Q θ) ξ ≤ T.r θ → qn (T.Q θ) (T.Φ θ ξ) ≤ T.lam θ * qn (T.Q θ) ξ
  budget : ∀ θ, T.δ θ ≤ (1 - T.lam θ) * T.r θ

def Tube.Residual (T : Tube S Θ n) (fly : S → S) : Prop :=
  ∀ θ x, T.Dyn θ x → qn (T.Q θ) (T.π θ (fly x) - T.Φ θ (T.π θ x)) ≤ T.δ θ

def Tube.SideInv (T : Tube S Θ n) (fly : S → S) : Prop := ∀ θ x, T.Dyn θ x → T.A θ (fly x)

theorem Tube.dyn_inv {T : Tube S Θ n} {fly : S → S} (hV : T.Valid) (hres : T.Residual fly) (hA : T.SideInv fly) :
    ∀ θ x, T.Dyn θ x → T.Dyn θ (fly x) :=
  fun θ x hx => ⟨robust_step (hV.sym θ) (hV.lam_nonneg θ) (hV.contract θ) (hV.budget θ) hx.1 (hres θ x hx),
    hA θ x hx⟩

def InTubes (TH : Tube (Ctl × Plane) Helix n) (TR : Tube (Ctl × Plane) Ray m) (y : Ctl × Plane) : Prop :=
  (∃ H, TH.Dyn H y ∧ 0 ≤ H.r + H.δ ∧ 0 ≤ H.s ∧ H.Geo cityMap 7 10) ∨
    (∃ R, TR.Dyn R y ∧ 0 ≤ R.g ∧ 0 ≤ R.s ∧ R.Geo cityMap 7)

theorem cityGate_spec_safe_of_sublevels (TH : Tube (Ctl × Plane) Helix n) (TR : Tube (Ctl × Plane) Ray m)
    (hVH : TH.Valid) (hresH : TH.Residual cityGate.fly) (hAH : TH.SideInv cityGate.fly)
    (hVR : TR.Valid) (hresR : TR.Residual cityGate.fly) (hAR : TR.SideInv cityGate.fly)
    (hconfH : ∀ H x, TH.Dyn H x → ∃ c, exactPos x.2 = some c ∧ H.Conf (toPt c))
    (hconfR : ∀ R x, TR.Dyn R x → ∃ c, exactPos x.2 = some c ∧ R.Conf (toPt c))
    (hterm : ∀ x, Origin cityGate GInit x → ∀ k, cityGate.term (cityGate.flyN k x) = true →
      InTubes TH TR (cityGate.flyN k x))
    (hInit : InitChecked cityGate GInit) (hNear : AirframeNear 7) : CitySafety.Safe cityMap specFilter := by
  refine cityGate_spec_safe_of_tubes TH.Dyn TR.Dyn hconfH (Tube.dyn_inv hVH hresH hAH) hconfR
    (Tube.dyn_inv hVR hresR hAR) (fun x hx k ht => ?_) hInit hNear
  rcases hterm x hx k ht with ⟨H, hd, hg⟩ | ⟨R, hd, hg⟩
  · exact ⟨.inl H, hd, hg⟩
  · exact ⟨.inr R, hd, hg⟩

end Proofs.Robust
