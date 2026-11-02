import Lean

/-! `kernel_rfl` closes `a = b` by `Eq.refl a`, leaving the definitional-equality check to the kernel alone. -/

open Lean Meta Elab Tactic

elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (_, a, _) := t.eq? | throwError "kernel_rfl: goal is not an equality"
    g.assign (← mkAuxTheorem t (← mkEqRefl a))
