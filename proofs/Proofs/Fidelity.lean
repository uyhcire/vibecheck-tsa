import Proofs.CodeEuler

namespace Vibecheck.Ideal

open Vibecheck

/-- Trajectory box for hard maneuvering: `|v·| ≤ 100`, `|d·| ≤ 1.05`, `|q| ≤ 4`, `|u| ≤ 100`, `|alphaV| ≤ 25`. -/
noncomputable def maneuverBox : Box := ⟨100, 105 / 100, 4, 100, 25⟩

/-- Trajectory box for cruise: `|v·| ≤ 60`, `|d·| ≤ 1.05`, `|q| ≤ 1/2`, `|u| ≤ 60`, `|alphaV| ≤ 10`. -/
noncomputable def cruiseBox : Box := ⟨60, 105 / 100, 1 / 2, 60, 10⟩

/-- Euler-vs-flow bounds on `maneuverBox`; units m, m, m/s, m/s, 1, 1, rad/s. -/
noncomputable def eManeuver : Fin 7 → ℝ := ![31 / 100, 33 / 100, 26, 26, 15 / 100, 15 / 100, 34 / 10]

/-- Euler-vs-flow bounds on `cruiseBox`; units m, m, m/s, m/s, 1, 1, rad/s. -/
noncomputable def eCruise : Fin 7 → ℝ := ![9 / 100, 11 / 100, 2, 2, 2 / 100, 2 / 100, 1 / 4]

theorem eFlow_maneuver (i : Fin 7) : eFlow maneuverBox i ≤ eManeuver i := by
  fin_cases i <;>
    simp only [eFlow, lipF, maxF, dAN, dV, maneuverBox, eManeuver, Δt, kN_eq, tauStall_eq, kD_eq,
      kElev_eq, kAlpha_eq, kQ_eq, g_eq, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] <;>
    norm_num

theorem eFlow_cruise (i : Fin 7) : eFlow cruiseBox i ≤ eCruise i := by
  fin_cases i <;>
    simp only [eFlow, lipF, maxF, dAN, dV, cruiseBox, eCruise, Δt, kN_eq, tauStall_eq, kD_eq,
      kElev_eq, kAlpha_eq, kQ_eq, g_eq, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] <;>
    norm_num

/-- Theorem B: an exact solution staying in `maneuverBox` ends within `eManeuver` of Euler. -/
theorem flow_near_euler (e θ : ℝ) (he : |e| ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) (y : ℝ → Fin 7 → ℝ)
    (hy : ∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt y (F e θ (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox maneuverBox (y t)) (i : Fin 7) :
    |y Δt i - euler e θ (y 0) i| ≤ eManeuver i :=
  (flow_near_euler_box maneuverBox he hθ y hy hbox i).trans (eFlow_maneuver i)

/-- Theorem B on `cruiseBox`. -/
theorem flow_near_euler_cruise (e θ : ℝ) (he : |e| ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (y : ℝ → Fin 7 → ℝ)
    (hy : ∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt y (F e θ (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox cruiseBox (y t)) (i : Fin 7) :
    |y Δt i - euler e θ (y 0) i| ≤ eCruise i :=
  (flow_near_euler_box cruiseBox he hθ y hy hbox i).trans (eFlow_cruise i)

theorem flow_near_code_box (b : Box) (s : State) (u : Input)
    (hvx : |fxR s.vx| ≤ 100) (hvz : |fxR s.vz| ≤ 100) (hq : |fxR s.q| ≤ 4)
    (hd : |fxR s.dx ^ 2 + fxR s.dz ^ 2 - 1| ≤ 1 / 100) (he : |fxR s.elev| ≤ 1)
    (hthr : 0 ≤ fxR u.throttle ∧ fxR u.throttle ≤ 1)
    (hfly : (stepAir s u).phase = .air)
    (y : ℝ → Fin 7 → ℝ) (hy0 : y 0 = toReal s)
    (hy : ∀ t ∈ Set.Icc 0 Δt,
      HasDerivWithinAt y (F (fxR s.elev) (fxR (effThrottle s u)) (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox b (y t)) (i : Fin 7) :
    |y Δt i - toReal (stepAir s u) i| ≤ δA i + eFlow b i := by
  have hA := stepAir_near_euler s u hvx hvz hq hd he hthr hfly i
  have hB := flow_near_euler_box b he (effThrottle_mem s u hthr) y hy hbox i
  rw [hy0] at hB
  have := abs_sub_le (y Δt i) (euler (fxR s.elev) (fxR (effThrottle s u)) (toReal s) i)
    (toReal (stepAir s u) i)
  rw [abs_sub_comm (euler _ _ _ i)] at this
  linarith

/-- Corollary: exact flow from `toReal s` vs `stepAir s u`, within `δA + eManeuver`. -/
theorem flow_near_code (s : State) (u : Input)
    (hvx : |fxR s.vx| ≤ 100) (hvz : |fxR s.vz| ≤ 100) (hq : |fxR s.q| ≤ 4)
    (hd : |fxR s.dx ^ 2 + fxR s.dz ^ 2 - 1| ≤ 1 / 100) (he : |fxR s.elev| ≤ 1)
    (hthr : 0 ≤ fxR u.throttle ∧ fxR u.throttle ≤ 1)
    (hfly : (stepAir s u).phase = .air)
    (y : ℝ → Fin 7 → ℝ) (hy0 : y 0 = toReal s)
    (hy : ∀ t ∈ Set.Icc 0 Δt,
      HasDerivWithinAt y (F (fxR s.elev) (fxR (effThrottle s u)) (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox maneuverBox (y t)) (i : Fin 7) :
    |y Δt i - toReal (stepAir s u) i| ≤ δA i + eManeuver i :=
  (flow_near_code_box maneuverBox s u hvx hvz hq hd he hthr hfly y hy0 hy hbox i).trans
    (add_le_add le_rfl (eFlow_maneuver i))

/-- Corollary on `cruiseBox`. -/
theorem flow_near_code_cruise (s : State) (u : Input)
    (hvx : |fxR s.vx| ≤ 100) (hvz : |fxR s.vz| ≤ 100) (hq : |fxR s.q| ≤ 4)
    (hd : |fxR s.dx ^ 2 + fxR s.dz ^ 2 - 1| ≤ 1 / 100) (he : |fxR s.elev| ≤ 1)
    (hthr : 0 ≤ fxR u.throttle ∧ fxR u.throttle ≤ 1)
    (hfly : (stepAir s u).phase = .air)
    (y : ℝ → Fin 7 → ℝ) (hy0 : y 0 = toReal s)
    (hy : ∀ t ∈ Set.Icc 0 Δt,
      HasDerivWithinAt y (F (fxR s.elev) (fxR (effThrottle s u)) (y t)) (Set.Icc 0 Δt) t)
    (hbox : ∀ t ∈ Set.Icc 0 Δt, InBox cruiseBox (y t)) (i : Fin 7) :
    |y Δt i - toReal (stepAir s u) i| ≤ δA i + eCruise i :=
  (flow_near_code_box cruiseBox s u hvx hvz hq hd he hthr hfly y hy0 hy hbox i).trans
    (add_le_add le_rfl (eFlow_cruise i))

end Vibecheck.Ideal
