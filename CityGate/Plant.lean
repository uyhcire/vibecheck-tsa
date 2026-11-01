import CityJsb.Plant

/-! The aircraft the gate flies: `JsbExact` (JSBSim 1.3.3 c172p, bit-exact), one JSBSim frame (1/128 s) per step, placed
on the city map. Trusted surface. -/

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

/-- One JSBSim frame with input `u` (`CityJsb.stepE`, what `libcityjsb` steps). Destructured so the old state is
not shared and `JsbExact` updates it in place. -/
def Plane.step (p : Plane) (u : Surf) : Plane :=
  match p with
  | ⟨st, _, ox, oy⟩ =>
    let r := CityJsb.stepE st u.elev u.ail u.rud u.thr
    { st := r.1, ob := r.2, ox, oy }

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
