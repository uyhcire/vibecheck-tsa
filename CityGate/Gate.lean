import GateSafety.Spec
import CityGate.Geometry

/-! PLACEHOLDER (agent L replaces this file, adding `Law.lean` and `Terminal.lean`): the city gate as a
`GateSafety.Gate`. Keep these names and types. -/

namespace CityGate
open GateSafety

/-- A controller's state (escape law, its rollout bookkeeping, a pilot candidate's latched input, ...). -/
structure Ctl where
  extra : Float
  deriving Inhabited

/-- The proposal layer's memory. -/
structure Mem where
  frame : Nat
  deriving Inhabited

def cityGate : Gate Plane Surf Ctl Mem where
  step := Plane.step
  ctl c _ := (⟨0, 0, 0, 1⟩, c)
  clear x := clearAt x.1.extra x.2
  term _ := false
  horizon := 2048
  propose _ _ _ _ := []
  update m _ _ _ _ := { frame := m.frame + 1 }
  start _ := ⟨0⟩
  m₀ := ⟨0⟩

/-- `cityGate.clear` passes only where `clearAt` does. -/
theorem cityGate_clear (x : Ctl × Plane) (h : cityGate.clear x = true) : ∃ e, clearAt e x.2 = true :=
  ⟨x.1.extra, h⟩

/-- The closed-loop state at the start (point-mass conventions, as `JsbPlant::new`): map point, altitude, airspeed,
flight path, heading (counter-clockwise from east), bank (positive left), load factor, throttle. -/
def startPlane (x y z v gam psi phi n thr : Float) : Plane :=
  let _ := n
  Plane.init x y z v gam psi phi 0 thr

def startState (x y z v gam psi phi n thr : Float) : Plane × (Mem × Ctl) :=
  let s := startPlane x y z v gam psi phi n thr
  (s, (cityGate.m₀, cityGate.start s))

theorem startState_eq (x y z v gam psi phi n thr : Float) :
    startState x y z v gam psi phi n thr =
      (startPlane x y z v gam psi phi n thr, (cityGate.m₀, cityGate.start (startPlane x y z v gam psi phi n thr))) :=
  rfl

/-- Display only: points (east, north, up; m) along the held controller's predicted path. -/
def predictPath (_g : Plane × (Mem × Ctl)) : Array (Float × Float × Float) := #[]

end CityGate
