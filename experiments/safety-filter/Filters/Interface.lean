/-! The common safety-filter interface (trusted surface: read this file to know what an instance's
`guarantee` says). Core Lean only. -/

namespace Filters

/-- Filter state carried into tick `n` of the closed loop: `init` at the start, then whatever `tick`
returned on the previous tick's observed state and pilot input. -/
def fstateAt {F S I C : Type} (init : F) (tick : F → S → I → F × C) (s : Nat → S)
    (pilot : Nat → I) : Nat → F
  | 0 => init
  | n + 1 => (tick (fstateAt init tick s pilot n) (s n) (pilot n)).1

/-- Command the filter applies during tick `n` of the closed loop. -/
def cmdAt {F S I C : Type} (init : F) (tick : F → S → I → F × C) (s : Nat → S) (pilot : Nat → I)
    (n : Nat) : C :=
  (tick (fstateAt init tick s pilot n) (s n) (pilot n)).2

/-- A verified, swappable safety filter: the code that runs (`init`, `tick`, `monitor`) together
with the plant model, the safety property and the theorem tying them together.

Each tick the host passes the plant state `s n` and the pilot input `pilot n`; `tick` returns the
next filter state and the command the host must apply. The plant model is a relation: `Allowed s c s'`
says the plant may move from `s` to `s'` in one tick under applied command `c` (a deterministic plant
is the special case `s' = step s c`). -/
structure SafetyFilter where
  /-- Plant state the guarantee is about (what the filter reads each tick). -/
  State : Type
  /-- Pilot input. -/
  Input : Type
  /-- Command the host applies to the plant. -/
  Command : Type
  /-- Filter state carried between ticks (committed plan, escape counter, ...). -/
  FState : Type
  /-- Filter state at the first tick. -/
  init : FState
  /-- One tick: (filter state, plant state, pilot input) ↦ (next filter state, applied command). -/
  tick : FState → State → Input → FState × Command
  /-- Plant model: the plant may move from `s` to `s'` in one tick under applied command `c`. -/
  Allowed : State → Command → State → Prop
  /-- Runtime check of one observed transition against `Allowed`. -/
  monitor : State → Command → State → Bool
  monitor_iff : ∀ s c s', monitor s c s' = true ↔ Allowed s c s'
  /-- Plant states the closed loop may start from. -/
  Init : State → Prop
  /-- Safety of one tick, from `s` to `s'` (a property of states `p` is the case `p s ∧ p s'`). -/
  Safe : State → State → Prop
  /-- The guarantee, up to the first tick the monitor rejects: for every pilot input sequence and
  every plant trajectory from an initial state, if the first `N` transitions obey `Allowed` under the
  commands the filter applied, those `N` ticks are safe. (`SafetyFilter.always_safe` is the form
  for an unbounded run.) -/
  guarantee : ∀ (pilot : Nat → Input) (s : Nat → State) (N : Nat), Init (s 0) →
    (∀ n < N, Allowed (s n) (cmdAt init tick s pilot n) (s (n + 1))) →
    ∀ n < N, Safe (s n) (s (n + 1))

/-- Optional strengthening for a plant that moves in discrete substeps within a tick: a host-side
`check` on the substep states of a tick that, together with that tick's `Safe`, makes each substep
`SafeSub`. -/
structure SubstepCheck (F : SafetyFilter) where
  /-- A substep state as the host reports it. -/
  Sub : Type
  /-- Host-side check of one tick's substeps. -/
  check : F.State → F.State → List Sub → Bool
  /-- Safety of a single substep state. -/
  SafeSub : Sub → Prop
  sound : ∀ s s' subs, F.Safe s s' → check s s' subs = true → ∀ p ∈ subs, SafeSub p

end Filters
