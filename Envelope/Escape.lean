import Envelope.Relation

/-! Worst-case escape: per-tick lower bounds over the reachable interval, checked against terrain. -/

namespace Envelope
variable {ι : Type}

/-- A set of states: an along-track interval and lower bounds on altitude, vertical speed, airspeed. -/
structure Box where
  xlo : Rat
  xhi : Rat
  hLo : Rat
  vzLo : Rat
  VLo : Rat
  deriving Repr

namespace Box

/-- The box holding exactly `s` (in the bounded components). -/
def point (s : State) : Box := ⟨s.x, s.x, s.h, s.vz, s.V⟩

/-- `s` lies in `b`. -/
def Contains (b : Box) (s : State) : Prop :=
  b.xlo ≤ s.x ∧ s.x ≤ b.xhi ∧ b.hLo ≤ s.h ∧ b.vzLo ≤ s.vz ∧ b.VLo ≤ s.V

/-- `b` is inside `c`. -/
def Sub (b c : Box) : Prop :=
  c.xlo ≤ b.xlo ∧ b.xhi ≤ c.xhi ∧ c.hLo ≤ b.hLo ∧ c.vzLo ≤ b.vzLo ∧ c.VLo ≤ b.VLo

end Box

/-- Worst-case box one tick after `b`, given next tick's vertical-speed and airspeed floors. -/
def Box.adv (P : Params ι) (b : Box) (vz' V' : Rat) : Box :=
  { xlo := b.xlo + P.dt * P.vxMin
    xhi := b.xhi + P.dt * P.vxMax
    hLo := b.hLo + P.dt * min b.vzLo vz' - P.hSlack
    vzLo := vz'
    VLo := V' }

/-- Worst-case box one tick after `b` in mode `m` under input `u`. -/
def Box.next (P : Params ι) (m : Mode) (u : ι) (b : Box) : Box :=
  b.adv P (vzFloor P m u b.vzLo b.VLo) (VFloor P m u b.VLo)

/-- Worst-case box one escape tick (phase `k`) after `b`. -/
def Box.esc (P : Params ι) (k : Nat) (b : Box) : Box :=
  b.adv P (vzEsc P k b.vzLo b.VLo) (VEsc P b.VLo)

/-- Worst-case boxes along an escape at phase `k`: `escIter P k b j` is `j` ticks later. -/
def escIter (P : Params ι) : Nat → Box → Nat → Box
  | _, b, 0 => b
  | k, b, j + 1 => escIter P (k + 1) (b.esc P k) j

/-- Every point of the tick swept from box `b` to box `c` clears terrain + margin. -/
def BoxTickClear (P : Params ι) (b c : Box) : Prop :=
  ∀ x, min b.xlo c.xlo ≤ x → x ≤ max b.xhi c.xhi →
    P.terrain.heightAt x + P.margin < min b.hLo c.hLo - P.sag

/-- Every tick of the worst-case escape from `b` at phase `k` clears terrain. -/
def SafeFrom (P : Params ι) (k : Nat) (b : Box) : Prop :=
  ∀ j, BoxTickClear P (escIter P k b j) (escIter P k b (j + 1))

/-- Computable sufficient check for `BoxTickClear`. -/
def tickOK (P : Params ι) (b c : Box) : Bool :=
  decide (P.terrain.maxOver (min b.xlo c.xlo) (max b.xhi c.xhi) + P.margin < min b.hLo c.hLo - P.sag)

/-- The escape is past its delay, climbing at the guaranteed rate, and above all terrain. -/
def escDone (P : Params ι) (top : Rat) (k : Nat) (b : Box) : Bool :=
  decide (P.delayTicks ≤ k ∧ P.base.climb ≤ b.vzLo ∧ top + P.margin < b.hLo - P.sag)

/-- Run the worst-case escape for at most `n` ticks until it is done. -/
def escLoop (P : Params ι) (top : Rat) : Nat → Nat → Box → Bool
  | n, k, b =>
    escDone P top k b ||
      match n with
      | 0 => false
      | n + 1 => let c := b.esc P k; tickOK P b c && escLoop P top n (k + 1) c

/-- The worst-case escape from box `b`, committed now, is certified clear. -/
def escapeOK (P : Params ι) (b : Box) : Bool :=
  decide (P.vMin ≤ b.VLo) && escLoop P P.terrain.top P.horizon 0 b

/-- After one free tick under `u`, the tick is clear and an escape from the worst state is certified. -/
def escapeClear (P : Params ι) (s : State) (u : ι) : Bool :=
  let b := Box.point s
  let c := b.next P .free u
  tickOK P b c && escapeOK P c

/-- Initial states: an escape committed now is certified. -/
def Init (P : Params ι) (s : State) : Prop := escapeOK P (Box.point s) = true

instance (P : Params ι) (s : State) : Decidable (Init P s) := by unfold Init; infer_instance

end Envelope
