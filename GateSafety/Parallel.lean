import GateSafety.Spec

/-! The gate's frame with the candidates' rollouts checked in parallel (`Task.spawn`), proven equal to `Gate.frame`,
and also returning what the frame applies. Not trusted surface: `frameP_fst` ties it to the spec. -/

namespace GateSafety
variable {α β : Type}

/-- `List.map` with each element computed in its own task. `Task.spawn` is pure, so this is `List.map`. -/
def pmap (f : α → β) (l : List α) : List β := (l.map fun a => Task.spawn fun _ => f a).map Task.get

theorem pmap_eq (f : α → β) : ∀ l : List α, pmap f l = l.map f
  | [] => rfl
  | a :: l => by
    have ih := pmap_eq f l
    simp only [pmap, List.map] at ih ⊢
    rw [ih]; rfl

theorem find_zip_map (f : α → Bool) : ∀ l : List α, ((l.zip (l.map f)).find? (·.2)).map (·.1) = l.find? f
  | [] => rfl
  | a :: l => by
    have ih := find_zip_map f l
    cases h : f a <;> simp [List.find?, h, ih]

variable {S I L M : Type} (G : Gate S I L M)

/-- `Gate.choose`, with every candidate's rollout in its own task. -/
def Gate.chooseP (s : S) (m : M) (w : L) (u : I) : Option L :=
  let cs := G.propose m s w u
  ((cs.zip (pmap (fun l => G.rolloutOK G.horizon (l, s)) cs)).find? (·.2)).map (·.1)

theorem chooseP_eq (s : S) (m : M) (w : L) (u : I) : G.chooseP s m w u = G.choose s m w u := by
  simp only [Gate.chooseP, Gate.choose, pmap_eq, find_zip_map]

/-- `Gate.frame` via `chooseP`, also returning the chosen candidate (if any) and the input applied this frame. -/
def Gate.frameP (p : S × (M × L)) (u : I) : (S × (M × L)) × Option L × I :=
  let c := G.chooseP p.1 p.2.1 p.2.2 u
  let l := c.getD p.2.2
  let x := G.fly (l, p.1)
  ((x.2, (G.update p.2.1 p.1 p.2.2 u c.isSome, x.1)), c, (G.ctl l p.1).1)

theorem frameP_fst (p : S × (M × L)) (u : I) : (G.frameP p u).1 = G.frame p u := by
  simp only [Gate.frameP, Gate.frame, chooseP_eq]

end GateSafety
