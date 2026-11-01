import Proofs.TermSound.Bounds

namespace Proofs.TermSound

open Complex

noncomputable section

/-! Non-vacuity: trims inside the end sets, every hypothesis of the main theorems discharged; rejections. -/

def trimH : St := ⟨0, 0, 300, 0, uStar EH 300, vzStar EH 300, lc⟩
def c0H : ℂ := centre trimH
def trimR : St := ⟨0, 0, 300, 0, uStar ER 300, vzStar ER 300, 0⟩
/-- A disturbance at the full budget in every component. -/
def dMax : St := ⟨dP, -dP, -dZ, dPSI, -dU, dVZ, -dL⟩

theorem dMax_small : Small dMax := by
  norm_num [Small, dMax, dP, dZ, dPSI, dU, dVZ, dL, abs_of_pos]

theorem trimH_mem : DynH c0H 300 0 1000 trimH := by
  refine ⟨?_, le_refl _, by norm_num [trimH, ZCAPH], fun _ => ⟨?_, ?_⟩⟩
  · simp [q, eu, evz, trimH, r2L]
  · simp [trimH, RL]
  · simp [c0H, trimH]

theorem trimR_mem : DynR 0 300 5 1000 trimR := by
  refine ⟨?_, le_refl _, by norm_num [trimR, ZCAPR], fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [q, eu, evz, trimR, r2L]
  · simp [q, trimR, r2T]
  · simp [trimR]
  · simp [trimR, kapY]
  · simp [trimR]

/-- An off-trim member: 0.05 m/s fast, 0.2 m/s extra climb, bank 0.2° steep, centre 3 m off. -/
def offH : St := ⟨3, 0, 300, 0, uStar EH 300 + 5 / 100, vzStar EH 300 + 2 / 10, lc + 1 / 300⟩

theorem offH_mem : DynH c0H 300 3 1000 offH := by
  refine ⟨?_, le_refl _, by norm_num [offH, ZCAPH], fun _ => ⟨?_, ?_⟩⟩
  · norm_num [q, eu, evz, offH, r2L, PL]
  · norm_num [offH, RL, abs_of_pos]
  · have : centre offH - c0H = 3 := by
      apply Complex.ext <;> simp [centre, c0H, offH, trimH, pos, cis]
    rw [this]; norm_num [offH, kappa]

theorem helix_trim_forever :
    ∀ n, DynH c0H 300 0 1000 (traj stepHelix trimH (fun _ => dMax) n) :=
  helix_forever (by norm_num) (by norm_num) (by norm_num [ZT]) trimH_mem (fun _ => dMax_small)

theorem ray_trim_forever :
    ∀ n, DynR 0 300 5 1000 (traj stepRay trimR (fun _ => dMax) n) :=
  ray_forever (by norm_num) (by norm_num) (by norm_num [ZT]) trimR_mem (fun _ => dMax_small)

def sinkH : St := ⟨0, 0, 300, 0, uStar EH 300, -1, lc⟩
def steepH : St := ⟨0, 0, 300, 0, uStar EH 300, vzStar EH 300, 1⟩
def movedH : St := ⟨10, 0, 300, 0, uStar EH 300, vzStar EH 300, lc⟩
def headR : St := ⟨0, 0, 300, 17 / 100, uStar ER 300, vzStar ER 300, 0⟩
def lowR : St := ⟨100, 0, 300, 0, uStar ER 300, vzStar ER 300, 0⟩

/-- Rejected: sinking at 1 m/s. -/
theorem not_mem_sinking : ¬ DynH c0H 300 0 1000 sinkH := by
  rintro ⟨hQ, -⟩
  norm_num [q, eu, evz, sinkH, r2L, PL, vzStar, uStar, EH, E1, kV, v0] at hQ

/-- Rejected: a 45° bank below `ztop`. -/
theorem not_mem_steep : ¬ DynH c0H 300 0 1000 steepH := by
  rintro ⟨-, -, -, h⟩
  have := (h (by norm_num [steepH])).1
  norm_num [steepH, lc, RL, abs_of_pos] at this

/-- Rejected: turning about a centre 10 m from `c0` at the entry height. -/
theorem not_mem_moved : ¬ DynH c0H 300 3 1000 movedH := by
  rintro ⟨-, -, -, h⟩
  have := (h (by norm_num [movedH])).2
  have e : centre movedH - c0H = 10 := by
    apply Complex.ext <;> simp [centre, c0H, movedH, trimH, pos, cis]
  rw [e] at this; norm_num [movedH] at this

/-- Rejected: heading 10° off the held track. -/
theorem not_mem_heading : ¬ DynR 0 300 5 1000 headR := by
  rintro ⟨-, -, -, h⟩
  have := (h (by norm_num [headR])).1
  norm_num [q, PT, r2T, headR] at this

/-- Rejected: under the climb line, 100 m along track with no height gained. -/
theorem not_mem_low : ¬ DynR 0 300 5 1000 lowR := by
  rintro ⟨-, -, -, h⟩
  have := (h (by norm_num [lowR])).2.2.2
  norm_num [G, lowR] at this

end

#print axioms long_step
#print axioms dynH_robust
#print axioms dynR_robust
#print axioms helix_forever
#print axioms ray_forever
#print axioms helix_bounds
#print axioms ray_bounds
#print axioms helix_trim_forever
#print axioms ray_trim_forever
#print axioms offH_mem
#print axioms not_mem_sinking
#print axioms not_mem_steep
#print axioms not_mem_moved
#print axioms not_mem_heading
#print axioms not_mem_low

end Proofs.TermSound
