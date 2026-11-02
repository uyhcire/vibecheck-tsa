import ExpProofs.Continuous.AuBound
import ExpJsb.TickDecomp

/-! The vz half of the one-tick escape property for the `Fx` closed loop, from the real-number clause `au_lower`
plus two bridge hypotheses stated per substep: the visited `Fx` states lie in `AuRegion` (drift containment), and
one `Fx` evaluation of `au` is within `ε` of the real evaluation at the same point (rounding). No integration
truncation term appears: the tick's vz increment is a sum of evaluated `au` values (`ExpJsb.tick_dvz_lower`). -/

namespace ExpJsb.Cont
open ExpJsb ExpVibecheck

/-- Real value of a fixed-point number. -/
noncomputable def ofFx (x : Fx) : ℝ := ofRaw x.raw

/-- Fixed-point state `k` substeps into the escape tick from `c`. -/
def sk (c : CLOf Fx) (k : Nat) : StateOf Fx := iter k (step 7 true (Escape.input c)) c.s

/-- The real-number evaluation at the state the `Fx` code evaluates in substep `k + 1`, with the tick's elevator. -/
noncomputable def realAt (c : CLOf Fx) (k : Nat) : StateOf ℝ × ProbeOf ℝ :=
  evalR ⟨ofFx (Escape.command c), 1, 0, 0⟩ ((integrate 7 true (sk c k)).map ofFx)

theorem dvz_of_bridge (c : CLOf Fx) (ε : ℝ) (hε : ε ≤ 0.01)
    (hF : ∀ k, k ≤ 7 → Fits (sk c k).au)
    (hdrift : ∀ k, k < 7 → AuRegion ((integrate 7 true (sk c k)).map ofFx) (ofFx (Escape.command c)))
    (hround : ∀ k, k < 7 → (realAt c k).1.au - ε ≤ ofFx (sk c (k + 1)).au)
    (h0 : -0.83 ≤ 2 * ofFx c.s.au - ofFx c.s.au1) :
    EscapeRegion.dvzMin ≤ (Escape.tick c).s.vz.raw - c.s.vz.raw := by
  have hA : ∀ k, 1 ≤ k → k ≤ 7 → (38667 : Int) ≤ (sk c k).au.raw := by
    intro k hk1 hk7
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 := au_lower _ _ (hdrift j (by omega))
    have h2 := hround j (by omega)
    unfold realAt at h2
    have h4 : 0.59 ≤ ofFx (sk c (j + 1)).au := by linarith
    have h3 : (38666.24 : ℝ) ≤ (sk c (j + 1)).au.raw := by
      unfold ofFx ofRaw at h4; linarith
    have : (38666 : ℝ) < (sk c (j + 1)).au.raw := by linarith
    exact_mod_cast this
  have h := tick_dvz_lower c 38667 hF hA
  have h0' : (-54395 : ℝ) ≤ 2 * (c.s.au.raw : ℝ) - c.s.au1.raw := by
    unfold ofFx ofRaw at h0; linarith
  have h0'' : (-54395 : Int) ≤ 2 * c.s.au.raw - c.s.au1.raw := by exact_mod_cast h0'
  unfold EscapeRegion.dvzMin
  omega


end ExpJsb.Cont
