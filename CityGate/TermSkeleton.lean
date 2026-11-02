import CityGate.EndSets

/-! Skeleton of `TermSoundR cityGate (CrashH 7) GInit`: obligations as `Prop`s, composition proved (`termSoundR_of`). -/

namespace CityGate.TermSkeleton
open GateSafety CityGate.SpecBridge CityGate.EndSets CitySafety.EndSets

/-! ## The abstraction's interface -/

/-- One end kind's abstraction, over tube parameters `Θ` (the entry constants) and an abstract state `A`. -/
structure Abs (Θ A : Type) where
  /-- Reads the gate state into the model; `none` where a number involved is not finite. -/
  π : Ctl × Plane → Option A
  /-- One frame of the escape law in the model. -/
  F : Θ → A → A
  /-- `Near θ a a'`: `a'` is within the per-frame disturbance `δ` of `a` (`‖a' - a‖ ≤ δ` in the model's norm). -/
  Near : Θ → A → A → Prop
  /-- The model's invariant set (the informal proof's coarse invariant set). -/
  DynA : Θ → A → Prop
  /-- Boxes on the states the model leaves out (attitude, rates, α, engine). -/
  Fast : Θ → Ctl × Plane → Prop

variable {Θ A : Type}

/-- `Dyn_k θ`: the model state is in `DynA θ` and the left-out states are in their boxes. -/
def Abs.Dyn (E : Abs Θ A) (θ : Θ) (x : Ctl × Plane) : Prop :=
  (∃ a, E.π x = some a ∧ E.DynA θ a) ∧ E.Fast θ x

/-! ## The obligations -/

/-- **OPEN `dyn_abstract_inv`** (the informal proof): `DynA` is robustly invariant under the model step and `Near`. -/
def Abs.DynAbstractInv (E : Abs Θ A) : Prop :=
  ∀ θ a a', E.DynA θ a → E.Near θ (E.F θ a) a' → E.DynA θ a'

/-- **OPEN `residual_bound`** (measurement, then proof): one real gate frame, read through `π`, lands within `Near`
of the model step, from every state in `Dyn`. -/
def Abs.ResidualBound (E : Abs Θ A) : Prop :=
  ∀ θ x a, E.Dyn θ x → E.π x = some a → ∃ a', E.π (cityGate.fly x) = some a' ∧ E.Near θ (E.F θ a) a'

/-- **OPEN `fast_states_bounded`** (measurement, then proof): the left-out states stay in their boxes on `Dyn`. -/
def Abs.FastBounded (E : Abs Θ A) : Prop :=
  ∀ θ x, E.Dyn θ x → E.Fast θ (cityGate.fly x)

/-- **OPEN `dyn_conf`** (the informal proof's set): `Dyn` puts the exact position in the funnel `Conf` `Geo` uses. -/
def Abs.DynConf (E : Abs Θ A) (Conf : Θ → CitySafety.Pt → Prop) : Prop :=
  ∀ θ x, E.Dyn θ x → ∃ c, exactPos x.2 = some c ∧ Conf θ (toPt c)

theorem Abs.dyn_inv {E : Abs Θ A} (hI : E.DynAbstractInv) (hR : E.ResidualBound) (hF : E.FastBounded) :
    ∀ θ x, E.Dyn θ x → E.Dyn θ (cityGate.fly x) := by
  intro θ x hx
  obtain ⟨⟨a, ha, hd⟩, _⟩ := id hx
  obtain ⟨a', ha', hn⟩ := hR θ x a hx ha
  exact ⟨⟨a', ha', hI θ a a' hd hn⟩, hF θ x hx⟩

/-! ## The end kinds' `Geo` and the certified sets -/

/-- Helix `Geo` for the 7 m cube (`e' = 10` covers its half-diagonal). -/
def GeoH (H : Helix) : Prop := 0 ≤ H.r + H.δ ∧ 0 ≤ H.s ∧ H.Geo cityMap 7 10

/-- Ray `Geo` for the 7 m cube. -/
def GeoR (R : Ray) : Prop := 0 ≤ R.g ∧ 0 ≤ R.s ∧ R.Geo cityMap 7

/-- The three end kinds' abstractions: helix, straight ray, and the street escape, whose tube is a ray funnel
until its own `Geo` exists (placeholder). -/
structure Ends (A : Type) where
  helix : Abs Helix A
  ray : Abs Ray A
  street : Abs Ray A

/-- **`C_k`**: the state is in one end kind's certified set `Dyn_k θ ∧ Geo_k θ`. -/
def InTubes (E : Ends A) (x : Ctl × Plane) : Prop :=
  (∃ H, E.helix.Dyn H x ∧ GeoH H) ∨ (∃ R, E.ray.Dyn R x ∧ GeoR R) ∨ (∃ R, E.street.Dyn R x ∧ GeoR R)

/-- All four abstraction obligations for one end kind. -/
structure Abs.Sound (E : Abs Θ A) (Conf : Θ → CitySafety.Pt → Prop) : Prop where
  inv : E.DynAbstractInv
  residual : E.ResidualBound
  fast : E.FastBounded
  conf : E.DynConf Conf

def Ends.Sound (E : Ends A) : Prop :=
  E.helix.Sound Helix.Conf ∧ E.ray.Sound Ray.Conf ∧ E.street.Sound Ray.Conf

/-! ## The end test -/

/-- **OPEN `term_sound_mem`** (the end-test fix): on every rollout the gate starts (`Origin`), `T` passing at
frame `n` puts the state in some `C_k`. -/
def EndTestCertified (E : Ends A) (T : Ctl × Plane → Bool) : Prop :=
  ∀ x, Origin cityGate GInit x → ∀ n, T (cityGate.flyN n x) = true → InTubes E (cityGate.flyN n x)

/-- The gate's own end test passes only where `T` does (by definition once `T` is the fixed test itself). -/
def TermLink (T : Ctl × Plane → Bool) : Prop := ∀ x, cityGate.term x = true → T x = true

theorem term_sound_mem {E : Ends A} {T : Ctl × Plane → Bool} (hT : EndTestCertified E T) (hL : TermLink T) :
    ∀ x, Origin cityGate GInit x → ∀ n, cityGate.term (cityGate.flyN n x) = true → InTubes E (cityGate.flyN n x) :=
  fun x hx n ht => hT x hx n (hL _ ht)

/-! ## Geometry: `C_k → ¬ CrashH 7` -/

theorem geo_clear_helix {E : Abs Helix A} (hc : E.DynConf Helix.Conf) {H : Helix} {x : Ctl × Plane}
    (hd : E.Dyn H x) (hg : GeoH H) : ¬ CrashH 7 x.2 := by
  obtain ⟨c, hpos, hcf⟩ := hc H x hd
  exact Helix.not_crashH hg.1 hg.2.1 (by decide +kernel) (by decide +kernel) hpos hcf hg.2.2

theorem geo_clear_ray {E : Abs Ray A} (hc : E.DynConf Ray.Conf) {R : Ray} {x : Ctl × Plane}
    (hd : E.Dyn R x) (hg : GeoR R) : ¬ CrashH 7 x.2 := by
  obtain ⟨c, hpos, hcf⟩ := hc R x hd
  exact Ray.not_crashH hg.1 hg.2.1 hpos hcf hg.2.2

/-! ## The composition -/

/-- The certified sets as one `EndSet` family for `CrashH 7`. -/
def endSet (E : Ends A) (h : E.Sound) : EndSet cityGate (CrashH 7) (Helix ⊕ Ray ⊕ Ray) :=
  (helixEndSet 7 10 (by decide +kernel) (by decide +kernel) E.helix.Dyn h.1.conf
      (Abs.dyn_inv h.1.inv h.1.residual h.1.fast)).sum
    ((rayEndSet 7 E.ray.Dyn h.2.1.conf (Abs.dyn_inv h.2.1.inv h.2.1.residual h.2.1.fast)).sum
      (rayEndSet 7 E.street.Dyn h.2.2.conf (Abs.dyn_inv h.2.2.inv h.2.2.residual h.2.2.fast)))

theorem mem_endSet {E : Ends A} (h : E.Sound) {x : Ctl × Plane} (hx : InTubes E x) : (endSet E h).Mem x := by
  rcases hx with ⟨H, hd, hg⟩ | ⟨R, hd, hg⟩ | ⟨R, hd, hg⟩
  · exact ⟨.inl H, hd, hg⟩
  · exact ⟨.inr (.inl R), hd, hg⟩
  · exact ⟨.inr (.inr R), hd, hg⟩

/-- **`TermSoundR` from the obligations** (no `sorry`): the abstractions' four facts per end kind, the fixed end
test's certification, and the link from the gate's end test to it. -/
theorem termSoundR_of (E : Ends A) (hE : E.Sound) {T : Ctl × Plane → Bool} (hT : EndTestCertified E T)
    (hL : TermLink T) : TermSoundR cityGate (CrashH 7) GInit :=
  (endSet E hE).termSoundR fun x hx n ht => mem_endSet hE (term_sound_mem hT hL x hx n ht)

end CityGate.TermSkeleton

/-! ## A default reading for the abstraction -/

namespace CityGate.TermSkeleton.City
open GateSafety CityGate.SpecBridge CityGate.EndSets CitySafety.EndSets CityGate.TermSkeleton

/-- A point-mass reading of the gate state (m, m/s): position (`exactPos`), NED velocity and airspeed (`Plane.ob`). -/
structure AbsSt where
  x : Rat
  y : Rat
  z : Rat
  vN : Rat
  vE : Rat
  vD : Rat
  vt : Rat
  deriving Inhabited

def piPM (x : Ctl × Plane) : Option AbsSt := do
  let (px, py, pz) ← exactPos x.2
  let o := x.2.ob
  pure ⟨px, py, pz, ← CitySafety.ratOf (Esc.obN o), ← CitySafety.ratOf (Esc.obE o), ← CitySafety.ratOf (Esc.obD o),
    ← CitySafety.ratOf o[6]!⟩

end CityGate.TermSkeleton.City

/-! ## Non-vacuity of the obligations' shapes -/

namespace CityGate.TermSkeleton.Checks
open CityGate.TermSkeleton

/-- A one-state model: `DynA = [-1, 1]`, `F a = a / 2`, disturbance `δ`. -/
def toy (δ : Rat) : Abs Unit Rat where
  π _ := none
  F _ a := a / 2
  Near _ b a' := -δ ≤ a' - b ∧ a' - b ≤ δ
  DynA _ a := -1 ≤ a ∧ a ≤ 1
  Fast _ _ := True

/-- `dyn_abstract_inv` holds for the budget `δ = 1/2 = (1 - λ) r`. -/
example : (toy (1 / 2)).DynAbstractInv := by
  intro _ a a' h hn
  simp only [toy] at h hn ⊢
  grind

/-- It fails for `δ = 1`: the statement is not vacuous. -/
example : ¬ (toy 1).DynAbstractInv := by
  intro h
  have := h () 1 (3 / 2) (by simp only [toy]; decide +kernel) (by simp only [toy]; decide +kernel)
  simp only [toy] at this
  revert this; decide +kernel

/-- The link holds when the fixed end test is the gate's own. -/
example : TermLink cityGate.term := fun _ h => h

end CityGate.TermSkeleton.Checks
