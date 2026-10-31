import Proofs.Fidelity

namespace Vibecheck.Ideal

open Vibecheck

theorem fxR_ofNat (n : ℕ) : fxR (OfNat.ofNat n : Fx) = n := by
  rw [fxR_eq, Fx.ofNat_raw]; push_cast; ring

def sLevel : State :=
  { x := 100, h := 200, vx := 40, vz := 0, dx := 1, dz := 0, q := 0, elev := 0, fuel := 50,
    phase := .air }

def uHalf : Input := { stick := 0, throttle := 0.5, brake := false }

example (i : Fin 7) :
    |toReal (stepAir sLevel uHalf) i
      - euler (fxR sLevel.elev) (fxR (effThrottle sLevel uHalf)) (toReal sLevel) i| ≤ δA i := by
  have h40 : fxR (40 : Fx) = 40 := by simpa using fxR_ofNat 40
  have h1 : fxR (1 : Fx) = 1 := by simpa using fxR_ofNat 1
  refine stepAir_near_euler sLevel uHalf ?_ ?_ ?_ ?_ ?_ ?_ (by decide) i <;>
    simp only [sLevel, uHalf, h40, h1, fxR_zero, fxR_half] <;> norm_num

/-- Tail-first at 10 m/s: `u < 0`, so no lift or drag and the exact flow is free fall. -/
def sBack : State :=
  { x := 100, h := 200, vx := -10, vz := 0, dx := 1, dz := 0, q := 0, elev := 0, fuel := 50,
    phase := .air }

def uIdle : Input := { stick := 0, throttle := 0, brake := false }

noncomputable def yBack (t : ℝ) : Fin 7 → ℝ :=
  ![100 - 10 * t, 200 - g * t ^ 2 / 2, -10, -(g * t), 1, 0, 0]

theorem yBack_zero : yBack 0 = toReal sBack := by
  have h10 : fxR (-10 : Fx) = -10 := by
    rw [show (-10 : Fx) = -(10 : Fx) from rfl, fxR_neg]; simpa using fxR_ofNat 10
  have h100 : fxR (100 : Fx) = 100 := by simpa using fxR_ofNat 100
  have h200 : fxR (200 : Fx) = 200 := by simpa using fxR_ofNat 200
  have h1 : fxR (1 : Fx) = 1 := by simpa using fxR_ofNat 1
  funext i; fin_cases i <;> simp [yBack, toReal, sBack, h10, h100, h200, h1, fxR_zero]

theorem yBack_ode (t : ℝ) :
    HasDerivWithinAt yBack (F (fxR sBack.elev) (fxR (effThrottle sBack uIdle)) (yBack t))
      (Set.Icc 0 Δt) t := by
  have he : fxR sBack.elev = 0 := fxR_zero
  have hθ : fxR (effThrottle sBack uIdle) = 0 := by
    simp only [effThrottle, uIdle]; split_ifs <;> exact fxR_zero
  rw [he, hθ]
  refine (hasDerivAt_pi.2 (fun i => ?_)).hasDerivWithinAt
  have hup : upR (-10) (-(g * t)) 1 0 = 0 := by simp [upR, uR]
  fin_cases i <;>
    simp only [yBack, F, axR, azR, qdotR, aNR, hup, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
  · have := ((hasDerivAt_id t).const_mul 10).const_sub 100
    convert this using 1 <;> simp
  · have := ((hasDerivAt_pow 2 t).const_mul g).div_const 2 |>.const_sub 200
    convert this using 1; simp; ring
  · convert hasDerivAt_const t (-10 : ℝ) using 1; simp
  · have := ((hasDerivAt_id t).const_mul g).neg
    convert this using 1
    · funext x; simp
    · simp
  · convert hasDerivAt_const t (1 : ℝ) using 1; simp
  · convert hasDerivAt_const t (0 : ℝ) using 1; simp
  · convert hasDerivAt_const t (0 : ℝ) using 1; simp

theorem yBack_box (b : Box) (hV : 10 ≤ b.V) (hD : 1 ≤ b.D) (hQ : 0 ≤ b.Q) (hU : 10 ≤ b.U)
    (hA : 1 ≤ b.A) (t : ℝ) (ht : t ∈ Set.Icc 0 Δt) : InBox b (yBack t) := by
  have hg : g ≤ 10 := by rw [g_eq]; norm_num
  have hg0 : 0 ≤ g := by rw [g_eq]; norm_num
  have ht1 : t ≤ 1 / 16 := ht.2
  have hgt : |-(g * t)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg hg0 ht.1)]; nlinarith [ht.1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [yBack, uR, alphaVR, Matrix.cons_val, Fin.isValue]
  · norm_num; linarith
  · linarith
  · norm_num; linarith
  · simp; linarith
  · simpa using hQ
  · norm_num; linarith
  · simp only [mul_zero, mul_one, zero_sub, neg_neg]
    rw [abs_neg] at hgt; linarith

example (i : Fin 7) :
    |yBack Δt i - toReal (stepAir sBack uIdle) i| ≤ δA i + eManeuver i ∧
    |yBack Δt i - toReal (stepAir sBack uIdle) i| ≤ δA i + eCruise i := by
  have h10 : fxR (-10 : Fx) = -10 := by
    rw [show (-10 : Fx) = -(10 : Fx) from rfl, fxR_neg]; simpa using fxR_ofNat 10
  have h1 : fxR (1 : Fx) = 1 := by simpa using fxR_ofNat 1
  have hs : |fxR sBack.vx| ≤ 100 ∧ |fxR sBack.vz| ≤ 100 ∧ |fxR sBack.q| ≤ 4 ∧
      |fxR sBack.dx ^ 2 + fxR sBack.dz ^ 2 - 1| ≤ 1 / 100 ∧ |fxR sBack.elev| ≤ 1 ∧
      (0 ≤ fxR uIdle.throttle ∧ fxR uIdle.throttle ≤ 1) := by
    simp only [sBack, uIdle, h10, h1, fxR_zero]; norm_num
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hs
  have hfly : (stepAir sBack uIdle).phase = .air := by decide
  exact ⟨flow_near_code sBack uIdle a1 a2 a3 a4 a5 a6 hfly yBack yBack_zero
      (fun t _ => yBack_ode t)
      (yBack_box maneuverBox (by norm_num [maneuverBox]) (by norm_num [maneuverBox])
        (by norm_num [maneuverBox]) (by norm_num [maneuverBox]) (by norm_num [maneuverBox])) i,
    flow_near_code_cruise sBack uIdle a1 a2 a3 a4 a5 a6 hfly yBack yBack_zero
      (fun t _ => yBack_ode t)
      (yBack_box cruiseBox (by norm_num [cruiseBox]) (by norm_num [cruiseBox])
        (by norm_num [cruiseBox]) (by norm_num [cruiseBox]) (by norm_num [cruiseBox])) i⟩

end Vibecheck.Ideal
