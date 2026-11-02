import Ci.proof.SafeCells
import Ci.Goals

/-! `TInvariant Ci.Proof.lawT` reduced to one open obligation, `TickInT`: the tick maps the terminal set into itself.
The other half of `TInvariant` (every substep safe and climbing) is `Ci.Proof.SafeIv.tick_safe_climb`, proved.

Evidence for `TickInT` (not a proof): exact-`inT` one-tick tests on 19447 near-boundary samples (fast coordinates at
their tolerance corners) and adversarial hill-climb searches per 50 m cell and per altitude band, no exit; worst
one-tick ratio found 0.993 (Lyapunov form or fast constraint, relative to its bound). In Mathlib,
`ExpProofs.CiProof.Skel.tInvariant_of_dynamics` reduces `TInvariant lawT` further, to the side conditions at the image
and an affine enclosure of the tick with a contraction certificate. See `docs/ci/log-proof.md`. -/

namespace Ci.Proof
open ExpVibecheck ExpJsb

/-- The open obligation: from every state in T, the tick lands in T. -/
def TickInT : Prop :=
  ∀ s m, lawT.inT (s, m) = true → lawT.inT ((Ci.tickT lawT s m).s, (Ci.tickT lawT s m).m) = true

theorem tInvariant_of_tickInT (h : TickInT) : Ci.Goals.TInvariant lawT := fun s m hT =>
  ⟨(SafeIv.tick_safe_climb s m hT).1, (SafeIv.tick_safe_climb s m hT).2, h s m hT⟩

theorem tSafe_of_tickInT (h : TickInT) : Ci.Goals.TSafe lawT :=
  Ci.Goals.tSafe_of_tInvariant lawT (tInvariant_of_tickInT h)

/-- A concrete state of the climb manifold at 1000 m (vx 31.96 m/s, vz 4.28 m/s) and its law memory. -/
def s1000 : State := ⟨⟨0⟩, ⟨65536000⟩, ⟨2094480⟩, ⟨280378⟩, ⟨63612⟩, ⟨15767⟩, ⟨-40⟩, ⟨172662207⟩, ⟨5656007⟩, ⟨292⟩, ⟨-1143⟩, ⟨0⟩, ⟨180⟩, ⟨-99⟩, ⟨31⟩, ⟨179⟩, ⟨-99⟩, ⟨280378⟩, ⟨280379⟩⟩
def m1000 : Ci.Lawfirst.Mem := ⟨-7788, 7232⟩

/-- T is not empty: the hypotheses of `tick_safe_climb` and `TickInT` are satisfiable. -/
theorem s1000_in : lawT.inT (s1000, m1000) = true := by decide +kernel

/-- T rejects a state 1 m/s faster than the manifold. -/
theorem s1000_fast_out : lawT.inT ({ s1000 with vx := ⟨2094480 + 65536⟩ }, m1000) = false := by decide +kernel

/-- The proved half applied to the concrete state. -/
example : (Ci.tickT lawT s1000 m1000).safe = true ∧ (Ci.tickT lawT s1000 m1000).climb = true :=
  SafeIv.tick_safe_climb _ _ s1000_in

end Ci.Proof
