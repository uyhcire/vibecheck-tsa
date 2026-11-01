/-! Safety of the exact-rollout gatekeeper (`flight/src/envfilter.rs`, `Gate`), one plant frame at a time, in
the shape of `docs/safety-objective.md`. Trusted surface: this file. -/

namespace GateSafety

/-- The gatekeeper over a deterministic plant.
- `S`: aircraft state; `I`: applied input (surfaces and throttle; also the pilot's input);
- `L`: a controller's state: an escape law (its clock, integrators, references), or a candidate such as "the
  pilot's surfaces for the rest of this tick, then escape law `l`";
- `M`: the proposal layer's memory (hold timer, last escape, ...). -/
structure Gate (S I L M : Type) where
  /-- One plant frame (`JsbExact.step`). -/
  step : S → I → S
  /-- A controller's input for this frame, and its next state (`Law::step`). -/
  ctl : L → S → I × L
  /-- Clearance test at one frame (`airframe_clearance > MARGIN`). -/
  clear : S → Bool
  /-- End-of-escape test: the rollout may stop here (`terminal`). -/
  term : L × S → Bool
  /-- Rollout length cap, in frames. -/
  horizon : Nat
  /-- Candidates to try this frame, best first, given the held controller and the pilot's input. -/
  propose : M → S → L → I → List L
  /-- Proposal memory after the frame, given whether a candidate was taken. -/
  update : M → S → L → I → Bool → M
  /-- The controller held at the start (the escape the initial search found), and the starting memory. -/
  start : S → L
  m₀ : M

variable {S I L M : Type} (G : Gate S I L M)

/-- One frame flown by controller `x.1` from aircraft state `x.2`. -/
def Gate.fly (x : L × S) : L × S := ((G.ctl x.1 x.2).2, G.step x.2 (G.ctl x.1 x.2).1)

/-- `n` frames flown by the controller. -/
def Gate.flyN : Nat → L × S → L × S
  | 0, x => x
  | n + 1, x => Gate.flyN n (G.fly x)

/-- Rollout check: clear at every frame until the end-of-escape test passes, within `n` more frames. -/
def Gate.rolloutOK : Nat → L × S → Bool
  | 0, x => G.clear x.2 && G.term x
  | n + 1, x => G.clear x.2 && (G.term x || Gate.rolloutOK n (G.fly x))

/-- The first proposed candidate whose rollout checks out from `s`. -/
def Gate.choose (s : S) (m : M) (w : L) (u : I) : Option L :=
  (G.propose m s w u).find? fun l => G.rolloutOK G.horizon (l, s)

/-- One frame of the closed loop from aircraft state `p.1`, memory `p.2.1` and held controller `p.2.2`, under
the pilot's input `u`: fly the chosen candidate if there is one, else the held controller; hold what flew. -/
def Gate.frame (p : S × (M × L)) (u : I) : S × (M × L) :=
  let c := G.choose p.1 p.2.1 p.2.2 u
  let x := G.fly (c.getD p.2.2, p.1)
  (x.2, (G.update p.2.1 p.1 p.2.2 u c.isSome, x.1))

/-- States the closed loop reaches from an allowed start, whatever input the pilot gives each frame. -/
inductive Reach (Init : S → Prop) : S × (M × L) → Prop
  | init {s : S} : Init s → Reach Init (s, (G.m₀, G.start s))
  | step {p : S × (M × L)} (u : I) : Reach Init p → Reach Init (G.frame p u)

/-- The objective: no reachable state is a crash. -/
def Safe (Crash : S → Prop) (Init : S → Prop) : Prop :=
  ∀ p, Reach G Init p → ¬ Crash p.1

/-! The three assumptions of `safe`. -/

/-- Flying controller `x.1` from `x.2` never crashes, at any frame. -/
def SafeForever (Crash : S → Prop) (x : L × S) : Prop :=
  ∀ k, ¬ Crash (G.flyN k x).2

/-- The clearance test means no contact. -/
def ClearSound (Crash : S → Prop) : Prop := ∀ s, G.clear s = true → ¬ Crash s

/-- The end-of-escape test means safe forever. -/
def TermSound (Crash : S → Prop) : Prop := ∀ x, G.term x = true → SafeForever G Crash x

/-- Every allowed start passes the initial check. -/
def InitChecked (Init : S → Prop) : Prop := ∀ s, Init s → G.rolloutOK G.horizon (G.start s, s) = true

end GateSafety
