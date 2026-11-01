import GateSafety.ProofsR

/-! `safeU`: `safeR` for a closed loop that ends at `Done` states (a landing): it takes no frame from a `Done` state,
and the end-of-escape assumption only has to cover the frames up to the first `Done` one (`SafeUntil`). -/

namespace GateSafety
variable {S I L M : Type} (G : Gate S I L M) (Crash : S → Prop) (Done : S → Prop) (Init : S → Prop)

/-- Flying controller `x.1` from `x.2`: no frame is a crash, up to and including the first `Done` one. -/
def SafeUntil (x : L × S) : Prop :=
  ∀ k, (∀ j < k, ¬ Done (G.flyN j x).2) → ¬ Crash (G.flyN k x).2

/-- States the closed loop reaches when it stops at `Done` states: a start, then frames taken only from states that
are not `Done`. -/
inductive ReachU : S × (M × L) → Prop
  | init {s : S} : Init s → ReachU (s, (G.m₀, G.start s))
  | step {p : S × (M × L)} (u : I) : ¬ Done p.1 → ReachU p → ReachU (G.frame p u)

/-- Where the gate's rollouts begin: its start controller at an allowed start, or a candidate it proposes at a
state of `ReachU`. -/
inductive OriginU : L × S → Prop
  | start {s : S} : Init s → OriginU (G.start s, s)
  | cand {p : S × (M × L)} {u : I} {l : L} : ReachU G Done Init p → l ∈ G.propose p.2.1 p.1 p.2.2 u →
      OriginU (l, p.1)

/-- **The end-of-escape test means safe until done, on the gate's own rollouts**: if a rollout that begins at an
`OriginU` passes `term` after `n` frames, flying on from there crashes at no frame up to the first `Done` one. -/
def TermSoundRU : Prop :=
  ∀ x, OriginU G Done Init x → ∀ n, G.term (G.flyN n x) = true → SafeUntil G Crash Done (G.flyN n x)

theorem SafeUntil.of_step {x : L × S} (hc : ¬ Crash x.2) (h : SafeUntil G Crash Done (G.fly x)) :
    SafeUntil G Crash Done x
  | 0, _ => hc
  | k + 1, hp => h k fun j hj => hp (j + 1) (by omega)

theorem SafeUntil.fly {x : L × S} (h : SafeUntil G Crash Done x) (hd : ¬ Done x.2) :
    SafeUntil G Crash Done (G.fly x) := fun k hp =>
  h (k + 1) fun j hj => by
    cases j with
    | zero => exact hd
    | succ j => exact hp j (by omega)

theorem rolloutOK_soundU (hc : ClearSound G Crash) {x₀ : L × S}
    (ht : ∀ n, G.term (G.flyN n x₀) = true → SafeUntil G Crash Done (G.flyN n x₀)) :
    ∀ n k, G.rolloutOK n (G.flyN k x₀) = true → SafeUntil G Crash Done (G.flyN k x₀)
  | 0, k, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true] at h
    exact ht k h.2
  | n + 1, k, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h with ⟨hx, hd | hr⟩
    · exact ht k hd
    · rw [flyN_succ'] at hr
      have tail := rolloutOK_soundU hc ht n (k + 1) hr
      rw [← flyN_succ'] at tail
      exact SafeUntil.of_step G Crash Done (hc _ hx) tail

theorem reach_safeU (hc : ClearSound G Crash) (ht : TermSoundRU G Crash Done Init) (hi : InitChecked G Init) :
    ∀ p, ReachU G Done Init p → SafeUntil G Crash Done (p.2.2, p.1) := by
  intro p hp
  induction hp with
  | init h => exact rolloutOK_soundU G Crash Done hc (ht _ (.start h)) _ 0 (hi _ h)
  | @step p u hnd hp ih =>
    have h : SafeUntil G Crash Done ((G.choose p.1 p.2.1 p.2.2 u).getD p.2.2, p.1) := by
      cases hch : G.choose p.1 p.2.1 p.2.2 u with
      | none => exact ih
      | some l =>
        simp only [Gate.choose] at hch
        have hr : G.rolloutOK G.horizon (G.flyN 0 (l, p.1)) = true := by
          have := List.find?_some hch; exact this
        exact rolloutOK_soundU G Crash Done hc (ht _ (.cand hp (List.mem_of_find?_eq_some hch))) _ 0 hr
    exact SafeUntil.fly G Crash Done h hnd

/-- **The gate is safe until done**: no state the stopping closed loop reaches is a crash, given a sound clearance
test, an end-of-escape test sound up to `Done` on the gate's own rollouts, and checked starts. -/
theorem safeU (hc : ClearSound G Crash) (ht : TermSoundRU G Crash Done Init) (hi : InitChecked G Init) :
    ∀ p, ReachU G Done Init p → ¬ Crash p.1 :=
  fun p hp => reach_safeU G Crash Done Init hc ht hi p hp 0 (fun _ h => absurd h (Nat.not_lt_zero _))

end GateSafety
