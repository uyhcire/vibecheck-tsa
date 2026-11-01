import GateSafety.Spec

/-! `safe`: the gate is safe, by induction over reachable states. Invariant: the held controller is safe forever
from the current state. A checked candidate is safe forever; the next frame of a controller that is safe
forever is again safe forever. The plant is the one the checks fly, so no model error enters. -/

namespace GateSafety
variable {S I L M : Type} (G : Gate S I L M) (Crash : S → Prop)

theorem SafeForever.fly {x : L × S} (h : SafeForever G Crash x) : SafeForever G Crash (G.fly x) :=
  fun k => h (k + 1)

theorem rolloutOK_sound (hc : ClearSound G Crash) (ht : TermSound G Crash) :
    ∀ n x, G.rolloutOK n x = true → SafeForever G Crash x
  | 0, x, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true] at h
    exact ht x h.2
  | n + 1, x, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h with ⟨hx, hd | hr⟩
    · exact ht x hd
    · have tail := rolloutOK_sound hc ht n _ hr
      intro k
      cases k with
      | zero => exact hc _ hx
      | succ k => exact tail k

theorem frame_safe (hc : ClearSound G Crash) (ht : TermSound G Crash) (p : S × (M × L)) (u : I)
    (hp : SafeForever G Crash (p.2.2, p.1)) : SafeForever G Crash ((G.frame p u).2.2, (G.frame p u).1) := by
  have h : SafeForever G Crash ((G.choose p.1 p.2.1 p.2.2 u).getD p.2.2, p.1) := by
    cases hch : G.choose p.1 p.2.1 p.2.2 u with
    | none => exact hp
    | some l =>
      simp only [Gate.choose] at hch
      have hr := List.find?_some hch
      exact rolloutOK_sound G Crash hc ht _ _ hr
  exact SafeForever.fly G Crash h

theorem reach_safe (Init : S → Prop) (hc : ClearSound G Crash) (ht : TermSound G Crash)
    (hi : InitChecked G Init) : ∀ p, Reach G Init p → SafeForever G Crash (p.2.2, p.1) := by
  intro p hp
  induction hp with
  | init h => exact rolloutOK_sound G Crash hc ht _ _ (hi _ h)
  | step u _ ih => exact frame_safe G Crash hc ht _ u ih

/-- **The gate is safe**, given a sound clearance test, a sound end-of-escape test, and checked starts. -/
theorem safe (Init : S → Prop) (hc : ClearSound G Crash) (ht : TermSound G Crash) (hi : InitChecked G Init) :
    Safe G Crash Init :=
  fun p hp => reach_safe G Crash Init hc ht hi p hp 0

end GateSafety
