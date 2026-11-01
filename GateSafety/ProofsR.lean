import GateSafety.Proofs

/-! `safeR`: `safe` with the end-of-escape assumption restricted to rollouts the gate actually flies
(`TermSoundR`), instead of every controller state (`TermSound`), which a fabricated controller state can falsify. -/

namespace GateSafety
variable {S I L M : Type} (G : Gate S I L M) (Crash : S → Prop) (Init : S → Prop)

/-- Where the gate's rollouts begin: its start controller at an allowed start, or a candidate it proposes at a
reachable state. -/
inductive Origin : L × S → Prop
  | start {s : S} : Init s → Origin (G.start s, s)
  | cand {p : S × (M × L)} {u : I} {l : L} : Reach G Init p → l ∈ G.propose p.2.1 p.1 p.2.2 u → Origin (l, p.1)

/-- **The end-of-escape test means safe forever, on the gate's own rollouts**: if a rollout that begins at an
`Origin` passes `term` after `n` frames, flying on from there never crashes. -/
def TermSoundR : Prop :=
  ∀ x, Origin G Init x → ∀ n, G.term (G.flyN n x) = true → SafeForever G Crash (G.flyN n x)

theorem TermSound.toR {Crash : S → Prop} (h : TermSound G Crash) : TermSoundR G Crash Init :=
  fun _ _ _ ht => h _ ht

theorem flyN_succ' (n : Nat) (x : L × S) : G.fly (G.flyN n x) = G.flyN (n + 1) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (G.fly x)

theorem rolloutOK_soundR (hc : ClearSound G Crash) {x₀ : L × S} (ht : ∀ n, G.term (G.flyN n x₀) = true →
    SafeForever G Crash (G.flyN n x₀)) : ∀ n k, G.rolloutOK n (G.flyN k x₀) = true →
    SafeForever G Crash (G.flyN k x₀)
  | 0, k, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true] at h
    exact ht k h.2
  | n + 1, k, h => by
    simp only [Gate.rolloutOK, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h with ⟨hx, hd | hr⟩
    · exact ht k hd
    · rw [flyN_succ'] at hr
      have tail := rolloutOK_soundR hc ht n (k + 1) hr
      intro j
      cases j with
      | zero => exact hc _ hx
      | succ j =>
        have := tail j
        rwa [← flyN_succ'] at this

theorem reach_safeR (hc : ClearSound G Crash) (ht : TermSoundR G Crash Init) (hi : InitChecked G Init) :
    ∀ p, Reach G Init p → SafeForever G Crash (p.2.2, p.1) := by
  intro p hp
  induction hp with
  | init h => exact rolloutOK_soundR G Crash hc (ht _ (.start h)) _ 0 (hi _ h)
  | @step p u hp ih =>
    have h : SafeForever G Crash ((G.choose p.1 p.2.1 p.2.2 u).getD p.2.2, p.1) := by
      cases hch : G.choose p.1 p.2.1 p.2.2 u with
      | none => exact ih
      | some l =>
        simp only [Gate.choose] at hch
        have hr : G.rolloutOK G.horizon (G.flyN 0 (l, p.1)) = true := by
          have := List.find?_some hch; exact this
        exact rolloutOK_soundR G Crash hc (ht _ (.cand hp (List.mem_of_find?_eq_some hch))) _ 0 hr
    exact SafeForever.fly G Crash h

/-- **The gate is safe**, given a sound clearance test, an end-of-escape test sound on the gate's own rollouts, and
checked starts. -/
theorem safeR (hc : ClearSound G Crash) (ht : TermSoundR G Crash Init) (hi : InitChecked G Init) :
    Safe G Crash Init :=
  fun p hp => reach_safeR G Crash Init hc ht hi p hp 0

end GateSafety
