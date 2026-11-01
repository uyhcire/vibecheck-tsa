import CityJsb.Plant
import CityGate.Landing

/-! The aircraft the gate flies: `JsbExact` (JSBSim 1.3.3 c172p, bit-exact), one JSBSim frame (1/128 s) per step, placed
on the city map. Trusted surface.

Infinite fuel: every step has `fuelFreeze` on (JSBSim's `propulsion/fuel_freeze`), as the safety spec's plant
`CitySafety.specStep` does (its decision 7), so the gate's rollouts predict the spec's plant. `libcityjsb`'s
`cityjsb_step` (`CityJsb.stepE`) burns fuel; it agrees with `Plane.step` while the tanks hold fuel except in the
tank contents and what follows from them (mass, CG, inertia). -/

namespace CityGate

/-- Applied input: JSBSim's elevator, aileron, rudder (each in [-1, 1]), throttle ([0, 1]) and wheel brake ([0, 1],
both sides) commands. -/
structure Surf where
  elev : Float
  ail : Float
  rud : Float
  thr : Float
  brk : Float
  deriving Inhabited

/-- The aircraft: its `JsbExact` state, the observation after its last frame (`CityJsb.obs` layout), and the map
point (east, north, m) it was placed at. -/
structure Plane where
  st : JsbExact.State Float
  ob : FloatArray
  ox : Float
  oy : Float

/-- One JSBSim frame with input `u` (both wheel brakes at `u.brk`), mixture 0.9, with fuel frozen
(`CitySafety.specStep`). Destructured so the old state is not shared and `JsbExact` updates it in place. -/
def Plane.step (p : Plane) (u : Surf) : Plane :=
  match p with
  | ⟨st, _, ox, oy⟩ =>
    let i : JsbExact.Input Float :=
      { elev := u.elev, ail := u.ail, rud := u.rud, thr := u.thr, mix := 0.9, brkL := u.brk, brkR := u.brk }
    let r := JsbExact.step st i (fuelFreeze := true)
    { st := r.1, ob := CityJsb.obs r.1 r.2, ox, oy }

/-- Map position (m): east and north of the map origin, and map altitude = JSBSim's altitude above sea level plus
`Landing.mapDatum` (so JSBSim's ground plane is the runway surface; as `JsbPlant::state`). -/
def Plane.pos (p : Plane) : Float × Float × Float :=
  (p.ox + p.ob[1]!, p.oy + p.ob[0]!, p.ob[2]! + Landing.mapDatum)

/-- An aircraft at map point `(ox, oy)`, `hM` m above sea level, in JSBSim's conventions (`CityJsb.init`: airspeed,
flight path, heading clockwise from north, bank, angle of attack), after one frame at throttle `thr` with the
surfaces centred (so `ob` is defined). -/
def Plane.init (ox oy hM v gam psi phi alpha thr : Float) : Plane :=
  let st := CityJsb.init hM v gam psi phi alpha
  ({ st, ob := FloatArray.empty, ox, oy } : Plane).step ⟨0, 0, 0, thr, 0⟩

end CityGate
