import ExpVibecheck.Safety

namespace ExpVibecheck

theorem stepElev_bounds (e c : Fx) (h1 : -1 ≤ e) (h2 : e ≤ 1) :
    -1 ≤ stepElev e c ∧ stepElev e c ≤ 1 := by
  simp only [stepElev, Fx.le_def, Fx.add_raw, Fx.clamp_raw, Fx.sub_raw, Fx.neg_raw,
    P.elevStep] at *
  have : (0.125 : Fx).raw = 8192 := rfl
  have h1' : (-1 : Fx).raw = -65536 := rfl
  have h1'' : (1 : Fx).raw = 65536 := rfl
  simp only [this, h1', h1''] at *
  omega

theorem stepElev_rate (e c : Fx) :
    Fx.abs (stepElev e c - e) ≤ P.elevStep := by
  simp only [stepElev, Fx.abs, Fx.le_def, Fx.add_raw, Fx.clamp_raw, Fx.sub_raw, Fx.neg_raw,
    P.elevStep]
  have : (0.125 : Fx).raw = 8192 := rfl
  simp only [this]
  split <;> simp only [Fx.neg_raw, Fx.sub_raw, Fx.add_raw, Fx.clamp_raw, Fx.neg_raw, this] <;>
    omega

theorem step_elev_bounds (s : State) (u : Input) (h1 : -1 ≤ s.elev) (h2 : s.elev ≤ 1) :
    -1 ≤ (step s u).elev ∧ (step s u).elev ≤ 1 := by
  have hb := stepElev_bounds s.elev u.stick h1 h2
  unfold step
  split
  · unfold stepAir; simp only
    split
    · exact hb
    · split
      · exact hb
      · split
        · exact hb
        · split
          · split <;> (try split) <;> exact hb
          · exact hb
  · unfold stepGround; simp only
    split
    · exact hb
    · split <;> exact hb
  · exact ⟨h1, h2⟩

/-- `elevStep` is 2 per second. -/
theorem step_elev_rate (s : State) (u : Input) :
    Fx.abs ((step s u).elev - s.elev) ≤ P.elevStep := by
  have hr := stepElev_rate s.elev u.stick
  unfold step
  split
  · unfold stepAir; simp only
    split
    · exact hr
    · split
      · exact hr
      · split
        · exact hr
        · split
          · split <;> (try split) <;> exact hr
          · exact hr
  · unfold stepGround; simp only
    split
    · exact hr
    · split <;> exact hr
  · simp only [Fx.abs, Fx.sub_raw, Fx.le_def, P.elevStep]
    have : (0.125 : Fx).raw = 8192 := rfl
    split <;> simp_all <;> omega

theorem fuel_step (f t : Fx) (h : 0 ≤ t) : max 0 (f - dt t) ≤ max 0 f := by
  simp only [Fx.le_def, Fx.max_raw, Fx.sub_raw, dt, Fx.div16_raw] at *
  have : (0 : Fx).raw = 0 := rfl
  simp only [this] at *
  omega

theorem step_fuel_le (s : State) (u : Input) (hu : u.Admissible) (hf : 0 ≤ s.fuel) :
    (step s u).fuel ≤ s.fuel := by
  have ht : 0 ≤ effThrottle s u := by
    unfold effThrottle; split
    · exact hu.2.2.1
    · exact Fx.le_def _ _ ▸ (Int.le_refl 0)
  have hmax : max 0 s.fuel = s.fuel := by
    apply Fx.ext_raw; simp only [Fx.max_raw]; simp only [Fx.le_def] at hf
    have : (0 : Fx).raw = 0 := rfl
    omega
  have key := fuel_step s.fuel (effThrottle s u) ht
  rw [hmax] at key
  unfold step
  split
  · unfold stepAir; simp only
    split
    · exact key
    · split
      · exact key
      · split
        · exact key
        · split
          · split <;> (try split) <;> exact key
          · exact key
  · unfold stepGround; simp only
    split
    · exact key
    · split <;> exact key
  · exact Fx.le_def _ _ ▸ (Int.le_refl s.fuel.raw)

end ExpVibecheck
