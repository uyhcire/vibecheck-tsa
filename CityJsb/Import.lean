import JsbExact.Model
import Std.Data.HashMap

/-! A `JsbExact` state from a JSBSim state dump (`jsbx/export_state.hpp`); derived fields in the dump are ignored. -/

namespace CityJsb
open JsbExact

private def v3n (p : String) : List String := [p ++ "1", p ++ "2", p ++ "3"]
private def m9n (p : String) : List String :=
  (List.range 3).flatMap fun r => (List.range 3).map fun c => p ++ toString (r + 1) ++ toString (c + 1)

/-- Field names of a state dump, in order; mirrors `jsbx::dump_state` for the c172p's gear units. -/
def dumpNames : Array String := List.toArray <|
  ["time"] ++ ["qi1", "qi2", "qi3", "qi4", "qdot1", "qdot2", "qdot3", "qdot4"] ++
  v3n "pqri" ++ v3n "ri" ++ v3n "vi" ++ v3n "vih0_" ++ v3n "vih1_" ++ v3n "aih0_" ++ ["epa"] ++
  v3n "pqridot" ++ v3n "uvwidot" ++ v3n "uvwdot" ++ ["stall"] ++ v3n "cg" ++
  ["tank0", "tank1", "tmap", "running", "fuelflow", "starved", "rpm"] ++ v3n "actxyz" ++ v3n "lastcg" ++
  ((List.range Gen.gears.size).flatMap fun i =>
    let p := s!"g{i}_"
    [p ++ "wow", p ++ "lm0", p ++ "lm1", p ++ "lm2", p ++ "slip", p ++ "steer"] ++ v3n (p ++ "act") ++
      m9n (p ++ "mT") ++ [p ++ "d_fz"]) ++
  v3n "d_ffric" ++ v3n "d_wind" ++ v3n "d_aerouvw" ++ v3n "uvw" ++ v3n "pqr" ++ v3n "ecef" ++
  ["phi", "theta", "psi", "hsl", "lat", "lon"] ++ v3n "vned" ++
  v3n "d_faero" ++ v3n "d_maero" ++ v3n "d_fprop" ++ v3n "d_mprop" ++ v3n "d_fgear" ++ v3n "d_mgear" ++
  v3n "d_ftot" ++ v3n "d_mtot" ++ v3n "d_fnat" ++ v3n "d_mmrc" ++
  ["d_alpha", "d_beta", "d_adot", "d_qbar", "d_vt", "d_mach", "d_pt", "d_hmac", "d_rho", "d_p", "d_t", "d_a"] ++
  v3n "d_grav" ++ ["d_thrust", "d_hp", "d_ihp", "d_mdotair", "d_preq", "d_vind", "d_mass"] ++
  m9n "d_J" ++ m9n "d_Jinv" ++ ["d_agl", "d_de", "d_da", "d_dr", "d_df"]

/-- Reads only the state `JsbExact.step` consumes, plus the constant wind (`d_wind`). -/
def stateFrom (g : String → Option Float) : Option (State Float) := do
  let v := fun (p : String) => do
    return (⟨← g (p ++ "1"), ← g (p ++ "2"), ← g (p ++ "3")⟩ : V3 Float)
  let flag := fun (n : String) => do return (← g n) != 0.0
  let gear := fun (i : Nat) => do
    let p := s!"g{i}_"
    let m := fun (rc : String) => g (p ++ "mT" ++ rc)
    return ({ wow := ← flag (p ++ "wow"), lm0 := ← g (p ++ "lm0"), lm1 := ← g (p ++ "lm1"),
              lm2 := ← g (p ++ "lm2"), slip := ← g (p ++ "slip"), steer := ← g (p ++ "steer"),
              act := ← v (p ++ "act"),
              mT := M33.mk' (← m "11") (← m "12") (← m "13") (← m "21") (← m "22") (← m "23") (← m "31")
                (← m "32") (← m "33") } : GearState Float)
  let gears ← (List.range Gen.gears.size).toArray.mapM gear
  return { q := ⟨← g "qi1", ← g "qi2", ← g "qi3", ← g "qi4"⟩,
           qdot := ⟨← g "qdot1", ← g "qdot2", ← g "qdot3", ← g "qdot4"⟩,
           pqri := ← v "pqri", ri := ← v "ri", vi := ← v "vi", vih0 := ← v "vih0_", vih1 := ← v "vih1_",
           aih0 := ← v "aih0_", epa := ← g "epa", pqridot := ← v "pqridot", uvwidot := ← v "uvwidot",
           uvwdot := ← v "uvwdot", stall := ← g "stall", cg := ← v "cg", tank0 := ← g "tank0",
           tank1 := ← g "tank1", tmap := ← g "tmap", running := ← flag "running", fuelflow := ← g "fuelflow",
           starved := ← flag "starved", rpm := ← g "rpm", act := ← v "actxyz", lastcg := ← v "lastcg",
           wind := ← v "d_wind", gears }

def dumpIndex : Std.HashMap String Nat := Std.HashMap.ofList (dumpNames.toList.zipIdx)

/-- A dump laid out as `dumpNames`. -/
def fromDump (a : FloatArray) : Option (State Float) :=
  if a.size != dumpNames.size then none
  else stateFrom fun n => dumpIndex[n]?.map fun i => a[i]!

end CityJsb
