import Jsb.EscapeRegion

/-! Hypotheses of the escape theorems are satisfiable, and the property can fail outside the region. -/

namespace Jsb.EscapeRegion
open Vibecheck

instance (I : Iv) (x : Fx) : Decidable (I.Mem x) := by cases I <;> unfold Iv.Mem <;> infer_instance
instance (S : StateOf Iv) (s : StateOf Fx) : Decidable (S.Mem s) := by unfold StateOf.Mem; infer_instance
instance (B : CLOf Iv) (c : CLOf Fx) : Decidable (B.Mem c) := by unfold CLOf.Mem; infer_instance
instance (l : LinCon) (c : CLOf Fx) : Decidable (l.Holds c) := by unfold LinCon.Holds; infer_instance
instance (a b : Int) (c : CLOf Fx) : Decidable (IncrProp a b c) := by unfold IncrProp; infer_instance

/-- Centre of `box5` (raw values). -/
def c0 : CLOf Fx := ⟨⟨⟨0⟩, ⟨60620800⟩, ⟨2621440⟩, ⟨-57344⟩, ⟨64900⟩, ⟨7209⟩, ⟨7864⟩, ⟨142868480⟩, ⟨4980736⟩, ⟨6553⟩,
  ⟨-206438⟩, ⟨0⟩, ⟨-9830⟩, ⟨475136⟩, ⟨5570⟩, ⟨-9830⟩, ⟨475136⟩, ⟨-62259⟩, ⟨-65536⟩⟩, ⟨13500⟩⟩

/-- `c0` with the nose at the horizon (alpha about 0.02 rad): outside the region. -/
def cLow : CLOf Fx := ⟨{ c0.s with dz := ⟨0⟩, dx := ⟨65536⟩ }, c0.elev⟩

/-- The hypotheses of `escape_box5` are satisfiable. -/
theorem c0_in : box5.Mem c0 ∧ ∀ l ∈ cons, l.Holds c0 := by decide +kernel

example : IncrProp dvzMin dvxMin c0 := escape_box5 c0 c0_in.1 c0_in.2

/-- The property is not vacuous: at low alpha the next tick loses vertical speed. -/
theorem cLow_fails : ¬ IncrProp dvzMin dvxMin cLow := by decide +kernel

end Jsb.EscapeRegion
