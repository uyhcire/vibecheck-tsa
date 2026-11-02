import ExpVibecheck.Filter
import ExpVibecheck.Spec

namespace ExpVibecheck

theorem clampAdm_admissible (u : Input) : u.clampAdm.Admissible := by
  refine ⟨Fx.clamp_ge _ _ _, Fx.clamp_le _ _ _ (by decide), Fx.clamp_ge _ _ _,
    Fx.clamp_le _ _ _ (by decide)⟩

theorem clampAdm_of_admissible (u : Input) (h : u.Admissible) : u.clampAdm = u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Input.clampAdm, Fx.clamp_of_mem _ _ _ h1 h2, Fx.clamp_of_mem _ _ _ h3 h4]

theorem park_admissible : Autoland.park.Admissible := by decide

theorem control_admissible (r : Runway) (s : State) : (Autoland.control r s).Admissible := by
  unfold Autoland.control
  split
  · refine ⟨Fx.clamp_ge _ _ _, Fx.clamp_le _ _ _ (by decide), ?_, ?_⟩
    · simp only [Autoland.air]; split
      · decide
      · exact Fx.clamp_ge _ _ _
    · simp only [Autoland.air]; split
      · decide
      · exact Fx.clamp_le _ _ _ (by decide)
  · split
    · exact park_admissible
    · simp only [Autoland.takeoff]; split <;> decide
  · exact park_admissible

theorem rolloutOK_mono (r : Runway) : ∀ n s, rolloutOK r n s = true → rolloutOK r (n + 1) s = true
  | 0, s, h => by
    unfold rolloutOK at h ⊢
    split at h
    · exact absurd h (by simp)
    · split at h
      · simp_all
      · split at h
        · exact absurd h (by simp)
        · simp at h
  | n + 1, s, h => by
    unfold rolloutOK at h
    rw [rolloutOK]
    split at h
    · exact absurd h (by simp)
    · rename_i hc
      simp only [hc, ite_false]
      split at h
      · simp_all
      · rename_i hp
        simp only [hp, ite_false]
        split at h
        · exact absurd h (by simp)
        · rename_i hs
          simp only [hs, ite_false]
          exact rolloutOK_mono r n _ h

theorem Fx.zero_raw : (0 : Fx).raw = 0 := rfl

theorem accel_parked (s : State) (hvx : s.vx = 0) (hvz : s.vz = 0) :
    (accel s 0).ax = 0 ∧ (accel s 0).az = -P.g := by
  have hu : s.u = 0 := by
    apply Fx.ext_raw; simp [State.u, hvx, hvz, Fx.zero_raw]
  have ha : s.alphaV = 0 := by
    apply Fx.ext_raw; simp [State.alphaV, hvx, hvz, Fx.zero_raw]
  have hup : max s.u 0 = 0 := by rw [hu]; rfl
  have hl : liftShape 0 (P.tauStall * 0) = 0 := by
    apply Fx.ext_raw; simp [liftShape, Fx.zero_raw]
  constructor <;> apply Fx.ext_raw <;> simp [accel, hup, ha, hl, hvx, hvz, Fx.zero_raw]

theorem parked_step (r : Runway) (s : State) (h : s.parked) :
    (step s (Autoland.control r s)).parked := by
  obtain ⟨hph, hvx, hvz, hrw⟩ := h
  have hc : Autoland.control r s = Autoland.park := by
    simp [Autoland.control, hph, hvx]
  have hthr : effThrottle s Autoland.park = 0 := by
    simp [effThrottle, Autoland.park]
  obtain ⟨hax, haz⟩ := accel_parked s hvx hvz
  rw [hc]
  have hx : s.x + dt s.vx = s.x := by apply Fx.ext_raw; simp [dt, hvx, Fx.zero_raw]
  have hv : max 0 (s.vx + dt (0 - if Autoland.park.brake = true then P.rollFriction + P.brakeDecel
      else P.rollFriction)) = 0 := by
    apply Fx.ext_raw
    simp [Fx.max_raw, dt, hvx, Fx.zero_raw, Autoland.park, P.rollFriction, P.brakeDecel,
      OfScientific.ofScientific]
    decide
  have hg : ¬ (0 < -P.g) := by decide
  obtain ⟨rw', hrw'⟩ := Option.isSome_iff_exists.1 hrw
  simp only [step, hph, stepGround, hthr, hax, haz, hx, hv, hrw', hg, ite_false]
  exact ⟨rfl, rfl, rfl, by simp [hrw']⟩
theorem not_crashed_of_parked (s : State) (h : s.parked) : ¬ s.crashed := by
  rintro ⟨k, hk⟩; rw [h.1] at hk; cases hk

theorem rollout_step (r : Runway) (n : Nat) (s : State) (h : rolloutOK r n s = true) :
    rolloutOK r n (step s (Autoland.control r s)) = true := by
  unfold rolloutOK at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hp
      have hp' := parked_step r s hp
      unfold rolloutOK
      simp [not_crashed_of_parked _ hp', hp']
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact rolloutOK_mono r _ _ h

theorem not_crashed_of_rollout (r : Runway) (n : Nat) (s : State) (h : rolloutOK r n s = true) :
    ¬ s.crashed := by
  unfold rolloutOK at h; split at h
  · exact absurd h (by simp)
  · assumption

theorem mem_preferred (s : State) (r : Runway) : r ∈ preferred s ↔ r ∈ runways := by
  simp only [preferred, List.mem_append, List.mem_filter]
  by_cases h : s.x < r.start <;> simp [h]

theorem inS_iff (s : State) : inS s = true ↔ ∃ r ∈ runways, rolloutOK r horizon s = true := by
  simp only [inS, List.any_eq_true, mem_preferred]

theorem escape_spec (s : State) (h : inS s = true) :
    ∃ r ∈ runways, rolloutOK r horizon s = true ∧ escape s = Autoland.control r s := by
  unfold escape escapeRunway
  match hf : (preferred s).find? (fun r => rolloutOK r horizon s) with
  | some r => exact ⟨r, (mem_preferred s r).1 (List.mem_of_find?_eq_some hf),
      by simpa using List.find?_some hf, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    obtain ⟨r, hr, hok⟩ := (inS_iff s).1 h
    exact absurd hok (by simpa using hf r ((mem_preferred s r).2 hr))

theorem escape_admissible (s : State) : (escape s).Admissible := by
  unfold escape; split
  · exact control_admissible _ _
  · exact park_admissible

theorem filter_admissible (s : State) (u : Input) : (filter s u).Admissible := by
  unfold filter; simp only; split
  · exact clampAdm_admissible u
  · exact escape_admissible s

theorem filter_invariant (s : State) (u : Input) (h : inS s = true) :
    inS (step s (filter s u)) = true := by
  unfold filter; simp only; split
  · assumption
  · obtain ⟨r, hr, hok, he⟩ := escape_spec s h
    rw [he]
    exact (inS_iff _).2 ⟨r, hr, rollout_step r _ s hok⟩

theorem filter_passthrough (s : State) (u : Input) (hu : u.Admissible)
    (hs : inS (step s u) = true) : filter s u = u := by
  unfold filter; simp only [clampAdm_of_admissible u hu, hs, ite_true]

theorem inS_safe (s : State) (h : inS s = true) : ¬ s.crashed := by
  obtain ⟨r, _, hok⟩ := (inS_iff s).1 h
  exact not_crashed_of_rollout r _ s hok

theorem init_inS (s : State) (h : Init s) : inS s = true := by
  refine (inS_iff s).2 ⟨runways.head (by decide), by simp [runways], ?_⟩
  unfold rolloutOK
  simp [not_crashed_of_parked _ h.1, h.1]

/-- The verified safety filter. -/
def solution : Certificate where
  inS := inS
  filter := filter
  init_sub := init_inS
  safe := inS_safe
  admissible := filter_admissible
  invariant := filter_invariant
  passthrough := fun s u _ hu hs => filter_passthrough s u hu hs

/-- No pilot input sequence crashes the aircraft, from any initial state. -/
theorem flight_never_crashes (s₀ : State) (h₀ : Init s₀) (pilot : Nat → Input) (n : Nat) :
    ¬ (traj solution s₀ pilot n).crashed :=
  never_crash solution s₀ h₀ pilot n

end ExpVibecheck
