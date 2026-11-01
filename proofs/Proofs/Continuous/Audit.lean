import Proofs.Continuous.EndTheorem

/-! Axiom audit and a satisfiability witness for the vertical-acceleration clause. -/

namespace Jsb.Cont

/-- Level climb-out at 40 m/s, 1000 m, alpha ≈ 0.12 rad, elevator 0.2, 1600 rpm. -/
noncomputable def sWit : StateOf ℝ :=
  { x := 0, h := 1000, vx := 40, vz := 0, dx := 0.993, dz := 0.12, q := 0.1, rpm := 1600, tmap := 80,
    udot := 0, wdot := 0, stall := 0, ah := 0, au := 0, qd := 0, ah1 := 0, au1 := 0, pvz := 0, pvz2 := 0 }

theorem sWit_region : AuRegion sWit 0.2 := by
  have hs : √((40 * 0.993 + 0 * 0.12) * (40 * 0.993 + 0 * 0.12) + (40 * 0.12 - 0 * 0.993) * (40 * 0.12 - 0 * 0.993)
      : ℝ) ≤ 41 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [sWit]
  norm_num at hs; linarith [hs]

example : 0.6 ≤ (evalR ⟨0.2, 1, 0, 0⟩ sWit).1.au := au_lower sWit 0.2 sWit_region

#print axioms au_lower
#print axioms dvz_of_bridge
#print axioms sWit_region

end Jsb.Cont
