import CityJsb.Plant

/-! The aircraft the gate flies: `JsbExact` (JSBSim 1.3.3 c172p, bit-exact), one JSBSim frame (1/128 s) per step, placed
on the city map. Trusted surface.

Infinite fuel: every step has `fuelFreeze` on (JSBSim's `propulsion/fuel_freeze`), as the safety spec's plant
`CitySafety.specStep` does (its decision 7), so the gate's rollouts predict the spec's plant. `libcityjsb`'s
`cityjsb_step` (`CityJsb.stepE`) burns fuel; it agrees with `Plane.step` while the tanks hold fuel except in the
tank contents and what follows from them (mass, CG, inertia). -/

namespace CityGate

/-- Applied input: JSBSim's elevator, aileron, rudder (each in [-1, 1]) and throttle ([0, 1]) commands. -/
structure Surf where
  elev : Float
  ail : Float
  rud : Float
  thr : Float
  deriving Inhabited

/-- The aircraft: its `JsbExact` state, the observation after its last frame (`CityJsb.obs` layout), and the map
point (east, north, m) it was placed at. -/
structure Plane where
  st : JsbExact.State Float
  ob : FloatArray
  ox : Float
  oy : Float

/-- One JSBSim frame with input `u`, mixture 0.9 and brakes released, with fuel frozen (`CitySafety.specStep`;
`CityJsb.stepE` with `fuelFreeze` on). Destructured so the old state is not shared and `JsbExact` updates it in
place. -/
def Plane.step (p : Plane) (u : Surf) : Plane :=
  match p with
  | ⟨st, _, ox, oy⟩ =>
    let i : JsbExact.Input Float := { elev := u.elev, ail := u.ail, rud := u.rud, thr := u.thr, mix := 0.9, brkL := 0, brkR := 0 }
    let r := JsbExact.step st i (fuelFreeze := true)
    { st := r.1, ob := CityJsb.obs r.1 r.2, ox, oy }

/-- Map position (m): east and north of the map origin, altitude above sea level (as `JsbPlant::state`). -/
def Plane.pos (p : Plane) : Float × Float × Float :=
  (p.ox + p.ob[1]!, p.oy + p.ob[0]!, p.ob[2]!)

/-- An aircraft at map point `(ox, oy)`, `hM` m above sea level, in JSBSim's conventions (`CityJsb.init`: airspeed,
flight path, heading clockwise from north, bank, angle of attack), after one frame at throttle `thr` with the
surfaces centred (so `ob` is defined). -/
def Plane.init (ox oy hM v gam psi phi alpha thr : Float) : Plane :=
  let st := CityJsb.init hM v gam psi phi alpha
  ({ st, ob := FloatArray.empty, ox, oy } : Plane).step ⟨0, 0, 0, thr⟩

end CityGate
