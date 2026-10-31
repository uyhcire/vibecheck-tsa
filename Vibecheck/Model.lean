import Vibecheck.World

/-! Forward-Euler side-view dynamics, step 1/16 s; forces per unit mass; pitch as unit vector `(dx, dz)`. -/

namespace Vibecheck

inductive CrashKind
  | terrain | hardLanding | overrun | overspeed | overstress
  deriving DecidableEq, Repr, Inhabited

inductive Phase
  | air
  | ground
  | crashed (why : CrashKind)
  deriving DecidableEq, Repr, Inhabited

structure State where
  x : Fx
  h : Fx
  vx : Fx
  vz : Fx
  dx : Fx
  dz : Fx
  /-- Pitch rate (rad/s), positive nose-up. -/
  q : Fx
  /-- Elevator deflection in `[-1, 1]`, positive nose-up. -/
  elev : Fx
  /-- Fuel, in seconds of full throttle. -/
  fuel : Fx
  phase : Phase
  deriving DecidableEq, Repr, Inhabited

structure Input where
  /-- Commanded elevator in `[-1, 1]`, positive nose-up. -/
  stick : Fx
  /-- Throttle in `[0, 1]`. -/
  throttle : Fx
  brake : Bool
  deriving DecidableEq, Repr, Inhabited

namespace P
def g : Fx := 9.81
def kN : Fx := 0.056
/-- `tan` of the stall angle of attack (15°). -/
def tauStall : Fx := 0.268
def stallFloor : Fx := 0.5
def kD : Fx := 0.0006
def thrustMax : Fx := 5
def kElev : Fx := 0.00131
def kAlpha : Fx := 0.0036
def kQ : Fx := 0.084
/-- Elevator travel per step (2 per second). -/
def elevStep : Fx := 0.125
def fuelMax : Fx := 90
def vne : Fx := 95
/-- Normal acceleration limit: 6 g. -/
def nMax : Fx := 58.86
def rollFriction : Fx := 0.2
def brakeDecel : Fx := 3
def maxSink : Fx := 3
def minTdPitch : Fx := -0.05
def maxTdPitch : Fx := 0.26
def maxTdSpeed : Fx := 50
/-- Max nose-up body pitch (`dz`) on the ground before tail strike limits it (12°). -/
def maxGroundPitch : Fx := 0.208
/-- Minimum height above terrain (m) away from runways. -/
def clearance : Fx := 8
end P

/-- Required height above terrain at `x`: `clearance`, or 0 over a runway. -/
def clearanceAt (x : Fx) : Fx := if (runwayAt x).isSome then 0 else P.clearance

def dt (a : Fx) : Fx := Fx.div16 a

def Input.Admissible (u : Input) : Prop :=
  -1 ≤ u.stick ∧ u.stick ≤ 1 ∧ 0 ≤ u.throttle ∧ u.throttle ≤ 1

instance (u : Input) : Decidable u.Admissible := by unfold Input.Admissible; infer_instance

def Input.clampAdm (u : Input) : Input :=
  { u with stick := Fx.clamp (-1) 1 u.stick, throttle := Fx.clamp 0 1 u.throttle }

def State.u (s : State) : Fx := s.vx * s.dx + s.vz * s.dz

/-- Angle-of-attack proxy `V·sin α` (m/s): velocity component below the body axis. -/
def State.alphaV (s : State) : Fx := s.vx * s.dz - s.vz * s.dx

/-- Lift vs `a = V sin α`; `t = u·tan α_stall`; continuous post-stall drop. -/
def liftShape (a t : Fx) : Fx :=
  if t < a then max (t - (a - t)) (P.stallFloor * t)
  else if a < -t then -(max (t - (-a - t)) (P.stallFloor * t))
  else a

structure Accel where
  ax : Fx
  az : Fx
  qdot : Fx
  aN : Fx

def accel (s : State) (thr : Fx) : Accel :=
  let up := max s.u 0
  let a := s.alphaV
  let aN := P.kN * up * liftShape a (P.tauStall * up)
  let aT := P.thrustMax * thr
  let drag := P.kD * up
  { ax := aT * s.dx - aN * s.dz - drag * s.vx
    az := aT * s.dz + aN * s.dx - drag * s.vz - P.g
    qdot := P.kElev * up * up * s.elev - P.kAlpha * up * a - P.kQ * up * s.q
    aN := aN }

def effThrottle (s : State) (u : Input) : Fx := if 0 < s.fuel then u.throttle else 0

/-- Rotate the body axis by `q·dt`, then pull it back toward unit length. -/
def rotate (dx dz q : Fx) : Fx × Fx :=
  let ex := dx - dt (q * dz)
  let ez := dz + dt (q * dx)
  let k := (3 - (ex * ex + ez * ez)) * 0.5
  (ex * k, ez * k)

def stepElev (e stick : Fx) : Fx :=
  e + Fx.clamp (-P.elevStep) P.elevStep (Fx.clamp (-1) 1 stick - e)

def stepAir (s : State) (u : Input) : State :=
  let thr := effThrottle s u
  let A := accel s thr
  let (dx', dz') := rotate s.dx s.dz s.q
  let s' : State :=
    { x := s.x + dt s.vx, h := s.h + dt s.vz,
      vx := s.vx + dt A.ax, vz := s.vz + dt A.az,
      dx := dx', dz := dz', q := s.q + dt A.qdot,
      elev := stepElev s.elev u.stick,
      fuel := max 0 (s.fuel - dt thr),
      phase := .air }
  if Fx.abs A.aN > P.nMax then { s' with phase := .crashed .overstress }
  else if s'.u > P.vne then { s' with phase := .crashed .overspeed }
  else if clipsBreakpoint s.x (s.h - P.clearance) s'.x (s'.h - P.clearance) then
    { s' with phase := .crashed .terrain }
  else if s'.h ≤ terrain s'.x + clearanceAt s'.x then
    match runwayAt s'.x with
    | none => { s' with phase := .crashed .terrain }
    | some r =>
      if -P.maxSink ≤ s'.vz ∧ P.minTdPitch ≤ s'.dz ∧ s'.dz ≤ P.maxTdPitch ∧ s'.u ≤ P.maxTdSpeed
      then { s' with h := r.elev, vz := 0, phase := .ground }
      else { s' with phase := .crashed .hardLanding }
  else s'

def stepGround (s : State) (u : Input) : State :=
  let thr := effThrottle s u
  let A := accel s thr
  let fr := if u.brake then P.rollFriction + P.brakeDecel else P.rollFriction
  let vx' := max 0 (s.vx + dt (A.ax - fr))
  let (dx', dz') := rotate s.dx s.dz s.q
  let pitchOk := 0 ≤ dz' ∧ dz' ≤ P.maxGroundPitch
  let s' : State :=
    { s with
      x := s.x + dt s.vx, vx := vx', vz := 0,
      dx := if pitchOk then dx' else s.dx, dz := if pitchOk then dz' else s.dz,
      q := if pitchOk then s.q + dt A.qdot else 0,
      elev := stepElev s.elev u.stick,
      fuel := max 0 (s.fuel - dt thr) }
  match runwayAt s'.x with
  | none => { s' with phase := .crashed .overrun }
  | some _ => if 0 < A.az then { s' with vz := dt A.az, phase := .air } else s'

def step (s : State) (u : Input) : State :=
  match s.phase with
  | .air => stepAir s u
  | .ground => stepGround s u
  | .crashed _ => s

def State.crashed (s : State) : Prop := ∃ k, s.phase = .crashed k

instance (s : State) : Decidable s.crashed :=
  match h : s.phase with
  | .crashed k => isTrue ⟨k, h⟩
  | .air => isFalse (by rintro ⟨k, hk⟩; simp_all)
  | .ground => isFalse (by rintro ⟨k, hk⟩; simp_all)

def State.parked (s : State) : Prop :=
  s.phase = .ground ∧ s.vx = 0 ∧ s.vz = 0 ∧ (runwayAt s.x).isSome

instance (s : State) : Decidable s.parked := by unfold State.parked; infer_instance

/-- The start: parked at the beginning of the first runway, level, full tanks. -/
def initState : State :=
  { x := 20, h := 50, vx := 0, vz := 0, dx := 1, dz := 0, q := 0, elev := 0,
    fuel := P.fuelMax, phase := .ground }

def Init (s : State) : Prop := s.parked ∧ s.q = 0 ∧ s.dx = 1 ∧ s.dz = 0

end Vibecheck
