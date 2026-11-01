import Mathlib
import Vibecheck.Model

/-! Real-number vector field `F` and Euler step `euler` for `stepAir`; coefficients are the exact grid values of `P`. -/

namespace Vibecheck.Ideal

open Vibecheck

/-- Exact real value of a fixed-point number (`Fx.toRat`, cast to `ℝ`). -/
noncomputable def fxR (a : Fx) : ℝ := (a.toRat : ℝ)

/-- Gravity (m/s²): real value of `P.g`. -/
noncomputable def g : ℝ := fxR P.g
/-- Lift coefficient: real value of `P.kN`. -/
noncomputable def kN : ℝ := fxR P.kN
/-- `tan` of the stall angle: real value of `P.tauStall`. -/
noncomputable def tauStall : ℝ := fxR P.tauStall
/-- Post-stall lift floor: real value of `P.stallFloor` (= 1/2). -/
noncomputable def stallFloor : ℝ := fxR P.stallFloor
/-- Drag coefficient: real value of `P.kD`. -/
noncomputable def kD : ℝ := fxR P.kD
/-- Maximum thrust (m/s²): real value of `P.thrustMax` (= 5). -/
noncomputable def thrustMax : ℝ := fxR P.thrustMax
/-- Elevator pitch authority: real value of `P.kElev`. -/
noncomputable def kElev : ℝ := fxR P.kElev
/-- Pitch stiffness: real value of `P.kAlpha`. -/
noncomputable def kAlpha : ℝ := fxR P.kAlpha
/-- Pitch damping: real value of `P.kQ`. -/
noncomputable def kQ : ℝ := fxR P.kQ

/-- The time step, `1/16` s. -/
noncomputable def Δt : ℝ := 1 / 16

/-- Body-axis airspeed `u = v · d` (real `State.u`). -/
def uR (vx vz dx dz : ℝ) : ℝ := vx * dx + vz * dz

/-- Angle-of-attack proxy `V sin α = vx·dz − vz·dx` (real `State.alphaV`). -/
def alphaVR (vx vz dx dz : ℝ) : ℝ := vx * dz - vz * dx

/-- Forward airspeed clipped at zero, `max u 0`. -/
noncomputable def upR (vx vz dx dz : ℝ) : ℝ := max (uR vx vz dx dz) 0

/-- Real `liftShape`: identity on `|a| ≤ t`, continuous post-stall drop outside. -/
noncomputable def liftShapeR (a t : ℝ) : ℝ :=
  if t < a then max (t - (a - t)) (stallFloor * t)
  else if a < -t then -(max (t - (-a - t)) (stallFloor * t))
  else a

/-- Real normal (lift) acceleration `aN = kN · up · liftShape(alphaV, tauStall · up)`. -/
noncomputable def aNR (vx vz dx dz : ℝ) : ℝ :=
  kN * upR vx vz dx dz * liftShapeR (alphaVR vx vz dx dz) (tauStall * upR vx vz dx dz)

/-- Real horizontal acceleration (real `Accel.ax`). -/
noncomputable def axR (thr vx vz dx dz : ℝ) : ℝ :=
  thrustMax * thr * dx - aNR vx vz dx dz * dz - kD * upR vx vz dx dz * vx

/-- Real vertical acceleration (real `Accel.az`). -/
noncomputable def azR (thr vx vz dx dz : ℝ) : ℝ :=
  thrustMax * thr * dz + aNR vx vz dx dz * dx - kD * upR vx vz dx dz * vz - g

/-- Real pitch acceleration (real `Accel.qdot`). -/
noncomputable def qdotR (elev vx vz dx dz q : ℝ) : ℝ :=
  kElev * upR vx vz dx dz * upR vx vz dx dz * elev
    - kAlpha * upR vx vz dx dz * alphaVR vx vz dx dz - kQ * upR vx vz dx dz * q

/-- The vector field on `(x, h, vx, vz, dx, dz, q)` = coordinates `0 … 6`, actuators fixed. -/
noncomputable def F (elev thr : ℝ) (y : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![y 2, y 3, axR thr (y 2) (y 3) (y 4) (y 5), azR thr (y 2) (y 3) (y 4) (y 5),
    -(y 6 * y 5), y 6 * y 4, qdotR elev (y 2) (y 3) (y 4) (y 5) (y 6)]

/-- The seven dynamic fields of a state, as exact reals. -/
noncomputable def toReal (s : State) : Fin 7 → ℝ :=
  ![fxR s.x, fxR s.h, fxR s.vx, fxR s.vz, fxR s.dx, fxR s.dz, fxR s.q]

/-- One forward-Euler step of `F` with step `Δt`. -/
noncomputable def euler (elev thr : ℝ) (y : Fin 7 → ℝ) : Fin 7 → ℝ := y + Δt • F elev thr y

/-- Box bounds: `|vx|,|vz| ≤ V`, `|dx|,|dz| ≤ D`, `|q| ≤ Q`, `|u| ≤ U`, `|alphaV| ≤ A`. -/
structure Box where
  V : ℝ
  D : ℝ
  Q : ℝ
  U : ℝ
  A : ℝ

/-- `y` lies in the box `b`. -/
structure InBox (b : Box) (y : Fin 7 → ℝ) : Prop where
  vx : |y 2| ≤ b.V
  vz : |y 3| ≤ b.V
  dx : |y 4| ≤ b.D
  dz : |y 5| ≤ b.D
  q : |y 6| ≤ b.Q
  u : |uR (y 2) (y 3) (y 4) (y 5)| ≤ b.U
  alpha : |alphaVR (y 2) (y 3) (y 4) (y 5)| ≤ b.A

end Vibecheck.Ideal
