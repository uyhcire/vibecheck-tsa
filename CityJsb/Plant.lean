import JsbExact.Model
import CityJsb.Template
import CityJsb.Import

/-! `JsbExact` as a plant for the city demo: build an in-flight state at the origin (latitude and longitude 0)
and step it one JSBSim frame (1/128 s) at a time, reporting what the demo needs in SI units. -/

namespace CityJsb
open JsbExact

def ft : Float := 0.3048
def g0 : Float := 32.174

/-- `FGColumnVector3`-style Euler angles (roll, pitch, heading) to the local-to-body matrix. -/
def tl2bOf (phi tht psi : Float) : M33 Float :=
  let (cf, sf, ct, st, cp, sp) := (phi.cos, phi.sin, tht.cos, tht.sin, psi.cos, psi.sin)
  M33.mk' (ct * cp) (ct * sp) (-st)
    (sf * st * cp - cf * sp) (sf * st * sp + cf * cp) (sf * ct)
    (cf * st * cp + sf * sp) (cf * st * sp - sf * cp) (cf * ct)

/-- An in-flight state at `east`, `north` metres on the tangent plane at latitude and longitude 0 and `hM` metres
above it: true airspeed `v` m/s, flight-path angle `gam`, heading `psi` (clockwise from north), bank `phi`, angle of
attack `alpha`; engine and mass state from the template. -/
def initAt (east north hM v gam psi phi alpha : Float) : State Float :=
  let ri : V3 Float := ⟨Gen.a + hM / ft, east / ft, north / ft⟩
  let tec2l := (locDerive ri).tec2l
  let l2b := tl2bOf phi (gam + alpha) psi
  let ti2b := l2b.mul tec2l
  let q := ti2b.toQuat
  let uvw : V3 Float := ⟨v / ft * alpha.cos, 0, v / ft * alpha.sin⟩
  let omega : V3 Float := ⟨0, 0, Gen.omega[2]!⟩
  let vi := V3.add (tec2l.T.mulV (l2b.T.mulV uvw)) (V3.cross omega ri)
  let pqri := ti2b.mulV omega
  let t := template
  { t with
    q := q
    qdot := q.qdot pqri
    pqri := pqri
    ri := ri
    vi := vi
    vih0 := vi
    vih1 := vi
    aih0 := V3.zero
    epa := (0 : Float)
    pqridot := V3.zero
    uvwidot := V3.zero
    uvwdot := V3.zero
    stall := (0 : Float)
    wind := V3.zero }

/-- `initAt` above the origin (latitude and longitude 0), `hM` metres above sea level. -/
def init (hM v gam psi phi alpha : Float) : State Float := initAt 0 0 hM v gam psi phi alpha

/-- North, east (from the origin), altitude above sea level, NED velocity, airspeed, Euler angles, body rates,
alpha, beta, normal load factor, height above terrain, dynamic pressure (Pa), engine rpm, ECEF position. -/
def obs (s : State Float) (d : Diag Float) : FloatArray :=
  let nz := -(d.faero.z + d.fprop.z) / (d.mass * g0)
  ⟨#[d.loc.z * ft, d.loc.y * ft, d.hsl * ft, d.vned.x * ft, d.vned.y * ft, d.vned.z * ft, d.vt * ft,
     d.euler.x, d.euler.y, d.euler.z, d.pqr.x, d.pqr.y, d.pqr.z, d.alpha, d.beta, nz, d.agl * ft,
     d.qbar * 47.880258, s.rpm, d.loc.x * ft, d.loc.y * ft, d.loc.z * ft]⟩

@[export cityjsb_init]
def initE (hM v gam psi phi alpha : Float) : State Float := init hM v gam psi phi alpha

@[export cityjsb_step_lean]
def stepE (s : State Float) (elev ail rud thr : Float) : State Float × FloatArray :=
  let (s', d) := step s { elev, ail, rud, thr, mix := 0.9, brkL := 0, brkR := 0 }
  (s', obs s' d)

/-- `stepE` with JSBSim's `propulsion/fuel_freeze` as given (`libcityjsb`'s per-plant setting): `true` is the plant
of the safety spec (`CitySafety.specStep`), `false` is `stepE`. -/
@[export cityjsb_step_ff_lean]
def stepFfE (s : State Float) (ff : Bool) (elev ail rud thr : Float) : State Float × FloatArray :=
  let (s', d) := step s { elev, ail, rud, thr, mix := 0.9, brkL := 0, brkR := 0 } (fuelFreeze := ff)
  (s', obs s' d)

/-- `obs` of the state a dump was taken at, from its derived fields; equals `obs` after the step that reached it. -/
def obsFromDump (a : FloatArray) : Option FloatArray :=
  if a.size != dumpNames.size then none else
  let g := fun (n : String) => a[dumpIndex[n]?.getD 0]!
  let nz := -(g "d_faero3" + g "d_fprop3") / (g "d_mass" * g0)
  some ⟨#[g "ecef3" * ft, g "ecef2" * ft, g "hsl" * ft, g "vned1" * ft, g "vned2" * ft, g "vned3" * ft,
    g "d_vt" * ft, g "phi", g "theta", g "psi", g "pqr1", g "pqr2", g "pqr3", g "d_alpha", g "d_beta", nz,
    g "d_agl" * ft, g "d_qbar" * 47.880258, g "rpm", g "ecef1" * ft, g "ecef2" * ft, g "ecef3" * ft]⟩

@[export cityjsb_obs_from_dump_lean]
def obsFromDumpE (a : FloatArray) : Option FloatArray := obsFromDump a

/-- One frame, returning the dump a JSBSim host would export after it (`toDump`): `JsbExact` standing in for
JSBSim when testing a dump consumer. -/
@[export cityjsb_step_dump_lean]
def stepDumpE (s : State Float) (elev ail rud thr : Float) : State Float × FloatArray :=
  let (s', d) := step s { elev, ail, rud, thr, mix := 0.9, brkL := 0, brkR := 0 }
  (s', toDump s' d)

/-- `stepDumpE` with `fuelFreeze` as given. -/
@[export cityjsb_step_dump_ff_lean]
def stepDumpFfE (s : State Float) (ff : Bool) (elev ail rud thr : Float) : State Float × FloatArray :=
  let (s', d) := step s { elev, ail, rud, thr, mix := 0.9, brkL := 0, brkR := 0 } (fuelFreeze := ff)
  (s', toDump s' d)

/-- `none` unless the dump has `dumpNames.size` fields. -/
@[export cityjsb_from_dump_lean]
def fromDumpE (a : FloatArray) : Option (State Float) := fromDump a

@[export cityjsb_dump_len_lean]
def dumpLenE (_ : Unit) : USize := dumpNames.size.toUSize

@[export cityjsb_dump_field_lean]
def dumpFieldE (i : USize) : String := dumpNames.getD i.toNat ""

end CityJsb
