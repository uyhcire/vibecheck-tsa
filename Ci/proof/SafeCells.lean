import Ci.proof.SafeProof

/-! Kernel evaluation of the interval safety check on the 53 cell boxes, and the one-tick safety and climb theorem
for the terminal set of `Ci.Proof.lawT`. -/

namespace Ci.Proof.SafeIv
open Vibecheck Jsb Ci.Lawfirst

/-- Bisection weights: every coordinate but x, h and the stall bit, normalised by the box's own widths. -/
def dimsOf (B : CLOf Iv) : List (Nat × Int) :=
  (List.range 20).filterMap fun i =>
    if i == 0 || i == 1 || i == 11 then none else
    let w := width (B.get i)
    if w ≤ 0 then none else some (i, 1000000000000 / w)

def cellOk (i : Nat) : Bool := checkRec ok [] (dimsOf (cellBox i)) 22 (cellBox i)

-- kernel evaluation of 56 interval ticks (53 cells, 3 extra bisection leaves); about 1-2 s each
set_option maxHeartbeats 400000000 in
theorem cells_ok : ∀ i ∈ List.range TData.boxTab.size, cellOk i = true := by decide +kernel

theorem cell_sound (i : Nat) (hi : i < TData.boxTab.size) (c : CLOf Fx) (hc : (cellBox i).Mem c) : Pt c :=
  checkRec_sound ok Pt [] _ ok_sound 22 (cellBox i) (cells_ok i (List.mem_range.mpr hi)) c hc (by simp)

/-- One-tick safety and climb of the terminal set: from every state in T the tick passes `safeOk` at all 8
substeps and climbs (vz ≥ 2 m/s and h rising, or h ≥ 2500 m) at all 8. -/
theorem tick_safe_climb (s : State) (m : Mem) (hT : lawT.inT (s, m) = true) :
    (Ci.tickT lawT s m).safe = true ∧ (Ci.tickT lawT s m).climb = true := by
  have hb : boxOk (s, m) = true := by
    have : inT (s, m) = true := hT
    unfold inT at this; simp only [Bool.and_eq_true] at this; exact this.2
  unfold boxOk at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hi, hac⟩, hm⟩ := hb
  exact cell_sound _ hi (pt (s, m)) hm m rfl hac

end Ci.Proof.SafeIv
