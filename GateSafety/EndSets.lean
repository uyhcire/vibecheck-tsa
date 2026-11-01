import GateSafety.ProofsR

/-! # End sets split into dynamics and geometry, and how `TermSound`/`TermSoundR` follow from membership. -/

namespace GateSafety
variable {S I L M : Type} (G : Gate S I L M) (Crash : S → Prop)

/-- End sets `C θ = {x | Dyn θ x ∧ Geo θ x}`, with `Dyn` the model-specific part and `Geo` the map clearance. -/
structure EndSet (Θ : Type) where
  Dyn : Θ → L × S → Prop
  Geo : Θ → L × S → Prop
  dyn_inv : ∀ θ x, Dyn θ x → Dyn θ (G.fly x)
  geo_inv : ∀ θ x, Dyn θ x → Geo θ x → Geo θ (G.fly x)
  clear : ∀ θ x, Dyn θ x → Geo θ x → ¬ Crash x.2

variable {G Crash}

/-- `x` is in one of the family's end sets. -/
def EndSet.Mem {Θ : Type} (E : EndSet G Crash Θ) (x : L × S) : Prop := ∃ θ, E.Dyn θ x ∧ E.Geo θ x

theorem EndSet.mem_flyN {Θ : Type} (E : EndSet G Crash Θ) {θ : Θ} :
    ∀ k x, E.Dyn θ x → E.Geo θ x → E.Dyn θ (G.flyN k x) ∧ E.Geo θ (G.flyN k x)
  | 0, _, hd, hg => ⟨hd, hg⟩
  | k + 1, x, hd, hg => E.mem_flyN k (G.fly x) (E.dyn_inv θ x hd) (E.geo_inv θ x hd hg)

theorem EndSet.safeForever {Θ : Type} (E : EndSet G Crash Θ) {x : L × S} (h : E.Mem x) : SafeForever G Crash x := by
  obtain ⟨θ, hd, hg⟩ := h
  intro k
  obtain ⟨hd', hg'⟩ := E.mem_flyN k x hd hg
  exact E.clear θ _ hd' hg'

theorem EndSet.termSound {Θ : Type} (E : EndSet G Crash Θ) (h : ∀ x, G.term x = true → E.Mem x) :
    TermSound G Crash :=
  fun x hx => E.safeForever (h x hx)

theorem EndSet.termSoundR {Θ : Type} (E : EndSet G Crash Θ) {Init : S → Prop}
    (h : ∀ x, Origin G Init x → ∀ n, G.term (G.flyN n x) = true → E.Mem (G.flyN n x)) : TermSoundR G Crash Init :=
  fun x hx n ht => E.safeForever (h x hx n ht)

/-- The union of two end-set families. -/
def EndSet.sum {Θ₁ Θ₂ : Type} (E₁ : EndSet G Crash Θ₁) (E₂ : EndSet G Crash Θ₂) : EndSet G Crash (Θ₁ ⊕ Θ₂) where
  Dyn | .inl θ => E₁.Dyn θ | .inr θ => E₂.Dyn θ
  Geo | .inl θ => E₁.Geo θ | .inr θ => E₂.Geo θ
  dyn_inv | .inl θ => E₁.dyn_inv θ | .inr θ => E₂.dyn_inv θ
  geo_inv | .inl θ => E₁.geo_inv θ | .inr θ => E₂.geo_inv θ
  clear | .inl θ => E₁.clear θ | .inr θ => E₂.clear θ

theorem EndSet.mem_sum_left {Θ₁ Θ₂ : Type} {E₁ : EndSet G Crash Θ₁} (E₂ : EndSet G Crash Θ₂) {x : L × S}
    (h : E₁.Mem x) : (E₁.sum E₂).Mem x :=
  let ⟨θ, hd, hg⟩ := h; ⟨.inl θ, hd, hg⟩

theorem EndSet.mem_sum_right {Θ₁ Θ₂ : Type} (E₁ : EndSet G Crash Θ₁) {E₂ : EndSet G Crash Θ₂} {x : L × S}
    (h : E₂.Mem x) : (E₁.sum E₂).Mem x :=
  let ⟨θ, hd, hg⟩ := h; ⟨.inr θ, hd, hg⟩

end GateSafety
