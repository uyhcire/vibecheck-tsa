import GateSafety.Spec

/-! The gate's frame with the candidates' rollouts checked in parallel (`Task.spawn`), proven equal to `Gate.frame`,
and also returning what the frame applies. `frameP` runs every candidate to its verdict; `chooseR` runs them in rounds
of a few frames and drops those behind one that verified. Not trusted surface: `frameP_fst` and `frameWith_fst` tie
them to the spec. -/

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

/-- `Gate.frame` with the choice `c` made elsewhere, also returning the choice and the input applied this frame. -/
def Gate.frameWith (c : Option L) (p : S × (M × L)) (u : I) : (S × (M × L)) × Option L × I :=
  let l := c.getD p.2.2
  let x := G.fly (l, p.1)
  ((x.2, (G.update p.2.1 p.1 p.2.2 u c.isSome, x.1)), c, (G.ctl l p.1).1)

theorem frameWith_fst (c : Option L) (p : S × (M × L)) (u : I) (h : c = G.choose p.1 p.2.1 p.2.2 u) :
    (G.frameWith c p u).1 = G.frame p u := by
  subst h; rfl

/-- A rollout check partly run: its verdict, or the frames left and the state it continues from. -/
abbrev Part (L S : Type) := Bool ⊕ (Nat × (L × S))

/-- Up to `K` frames of `rolloutOK n x`. -/
def Gate.runK : Nat → Nat → L × S → Part L S
  | 0, n, x => .inr (n, x)
  | _ + 1, 0, x => .inl (G.clear x && G.term x)
  | K + 1, n + 1, x => if G.clear x then (if G.term x then .inl true else Gate.runK K n (G.fly x)) else .inl false

/-- What a partly run rollout check concludes. -/
def Gate.verdict : Part L S → Bool
  | .inl b => b
  | .inr (n, x) => G.rolloutOK n x

theorem Gate.verdict_runK : ∀ K n x, G.verdict (G.runK K n x) = G.rolloutOK n x
  | 0, n, x => rfl
  | _ + 1, 0, x => rfl
  | K + 1, n + 1, x => by
    have ih := Gate.verdict_runK K n (G.fly x)
    simp only [Gate.runK, Gate.rolloutOK]
    cases G.clear x <;> cases G.term x <;> simp [Gate.verdict] at ih ⊢ <;> exact ih

/-- One round: `K` more frames, each in its own task, for the first `w` unresolved candidates before the first
verified one; the rest as they are. -/
def Gate.spawnRound (K : Nat) : Nat → List (L × Part L S) → List (Task (L × Part L S))
  | _, [] => []
  | _, (l, .inl true) :: r => .pure (l, .inl true) :: r.map Task.pure
  | w, (l, .inl false) :: r => .pure (l, .inl false) :: Gate.spawnRound K w r
  | 0, c :: r => .pure c :: Gate.spawnRound K 0 r
  | w + 1, (l, .inr (n, x)) :: r => Task.spawn (fun _ => (l, G.runK K n x)) :: Gate.spawnRound K w r

def Gate.round (K w : Nat) (cs : List (L × Part L S)) : List (L × Part L S) :=
  (G.spawnRound K w cs).map Task.get

/-- A candidate and its verdict. -/
def Gate.judged (c : L × Part L S) : L × Bool := (c.1, G.verdict c.2)

theorem Gate.round_judged (K : Nat) : ∀ w cs, (G.round K w cs).map G.judged = cs.map G.judged
  | _, [] => rfl
  | _, (l, .inl true) :: r => by simp [Gate.round, Gate.spawnRound]
  | w, (l, .inl false) :: r => by
    have ih := Gate.round_judged K w r
    simp only [Gate.round] at ih ⊢
    simp [Gate.spawnRound, ih]
  | 0, (l, .inr (n, x)) :: r => by
    have ih := Gate.round_judged K 0 r
    simp only [Gate.round] at ih ⊢
    simp [Gate.spawnRound, ih]
  | w + 1, (l, .inr (n, x)) :: r => by
    have ih := Gate.round_judged K w r
    simp only [Gate.round] at ih ⊢
    simp [Gate.spawnRound, ih, Gate.judged, Gate.verdict_runK, Task.spawn]
    rfl

/-- The choice, if the verdicts so far decide it: the first verified candidate, or none if all failed. -/
def decided : List (L × Part L S) → Option (Option L)
  | [] => some none
  | (l, .inl true) :: _ => some (some l)
  | (_, .inl false) :: r => decided r
  | (_, .inr _) :: _ => none

theorem decided_eq (G : Gate S I L M) : ∀ (cs : List (L × Part L S)) res, decided cs = some res →
    res = ((cs.map G.judged).find? (·.2)).map (·.1)
  | [], res, h => by simp [decided] at h; simp [← h]
  | (l, .inl true) :: _, res, h => by simp [decided] at h; simp [← h, Gate.judged, Gate.verdict]
  | (l, .inl false) :: r, res, h => by
    simp only [decided] at h
    simp [decided_eq G r res h, Gate.judged, Gate.verdict]
  | (_, .inr _) :: _, res, h => by simp [decided] at h

/-- Rounds until the choice is decided (`fuel` rounds, then sequentially). -/
def Gate.chooseLoop (K w : Nat) : Nat → List (L × Part L S) → Option L
  | 0, cs => ((cs.map G.judged).find? (·.2)).map (·.1)
  | fuel + 1, cs => match decided cs with
    | some res => res
    | none => Gate.chooseLoop K w fuel (G.round K w cs)

theorem Gate.chooseLoop_eq (K w : Nat) : ∀ fuel cs,
    G.chooseLoop K w fuel cs = ((cs.map G.judged).find? (·.2)).map (·.1)
  | 0, cs => rfl
  | fuel + 1, cs => by
    simp only [Gate.chooseLoop]
    split
    · rename_i res h; exact decided_eq G cs res h
    · rw [Gate.chooseLoop_eq K w fuel, G.round_judged]

/-- `Gate.choose` in rounds of `K` frames, running up to `w` candidates at once, and dropping every candidate
behind one that verified. -/
def Gate.chooseR (K w : Nat) (s : S) (m : M) (wl : L) (u : I) : Option L :=
  G.chooseLoop K w (G.horizon + 2) ((G.propose m s wl u).map fun l => (l, .inr (G.horizon, (l, s))))

theorem Gate.chooseR_eq (K w : Nat) (s : S) (m : M) (wl : L) (u : I) :
    G.chooseR K w s m wl u = G.choose s m wl u := by
  simp only [Gate.chooseR, Gate.chooseLoop_eq, Gate.choose, List.map_map, List.find?_map, Option.map_map]
  simp [Function.comp_def, Gate.judged, Gate.verdict]

end GateSafety
