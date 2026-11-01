import CityJsb.Import
import Std.Data.HashMap

/-! Reading a dump log (`.names` + `.bin`, as `jsbx/harness.cpp` and `jsbx::DriftLog` write) and comparing
`JsbExact` against it, for `cityimporttest` and `jsbdrift`. -/

namespace DumpRun
open JsbExact CityJsb

structure Run where
  names : Array String
  nf : Nat
  data : FloatArray
  index : Std.HashMap String Nat

def Run.records (r : Run) : Nat := r.data.size / r.nf

def Run.get? (r : Run) (k : Nat) (n : String) : Option Float := r.index[n]?.map fun c => r.data[k * r.nf + c]!

def Run.get (r : Run) (k : Nat) (n : String) (dflt : Float := 0.0) : Float := (r.get? k n).getD dflt

def load (pfx : String) : IO Run := do
  let names := ((← IO.FS.readFile (pfx ++ ".names")).splitOn "\n").filter (· ≠ "") |>.toArray
  let bytes ← IO.FS.readBinFile (pfx ++ ".bin")
  let n := bytes.size / 8
  let mut fa : FloatArray := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let mut u : UInt64 := 0
    for j in [0:8] do
      u := u ||| ((bytes[8 * i + j]!).toUInt64 <<< (8 * j).toUInt64)
    fa := fa.push (Float.ofBits u)
  return { names, nf := names.size, data := fa, index := Std.HashMap.ofList names.toList.zipIdx }

/-- Record `k`'s state dump in `dumpNames` order, as a host would pass it to `cityjsb_from_dump`. -/
def Run.dump (r : Run) (k : Nat) : Option FloatArray :=
  dumpNames.foldlM (init := FloatArray.emptyWithCapacity dumpNames.size) fun a n => (r.get? k n).map a.push

def Run.input (r : Run) (k : Nat) : Input Float :=
  { elev := r.get k "u_elev", ail := r.get k "u_ail", rud := r.get k "u_rud", thr := r.get k "u_thr",
    mix := r.get k "u_mix" 0.9, brkL := r.get k "u_brkL", brkR := r.get k "u_brkR" }

/-- Whether record `k + 1` continues record `k`'s episode. -/
def Run.continues (r : Run) (k : Nat) : Bool :=
  k + 1 < r.records && r.get (k + 1) "ep" == r.get k "ep" && r.get k "stop" == 0.0

/-- The dump fields a step reproduces, named as in the dump. -/
def fields (s : State Float) (d : Diag Float) : List (String × Float) :=
  let v := fun (p : String) (x : V3 Float) => [(p ++ "1", x.x), (p ++ "2", x.y), (p ++ "3", x.z)]
  v "uvw" d.uvw ++ v "pqr" d.pqr ++ v "ecef" d.loc ++
  [("phi", d.euler.x), ("theta", d.euler.y), ("psi", d.euler.z), ("hsl", d.hsl), ("rpm", s.rpm),
   ("qi1", s.q.q0), ("qi2", s.q.q1), ("qi3", s.q.q2), ("qi4", s.q.q3)] ++
  v "vi" s.vi ++ v "ri" s.ri ++ v "pqri" s.pqri ++ v "uvwdot" s.uvwdot ++ v "pqridot" s.pqridot ++ v "uvwidot" s.uvwidot ++
  [("epa", s.epa), ("stall", s.stall), ("tank0", s.tank0), ("tank1", s.tank1), ("tmap", s.tmap),
   ("fuelflow", s.fuelflow), ("running", if s.running then 1.0 else 0.0)] ++ v "cg" s.cg ++ v "actxyz" s.act ++
  v "vned" d.vned ++
  [("d_alpha", d.alpha), ("d_beta", d.beta), ("d_adot", d.adot), ("d_qbar", d.qbar), ("d_vt", d.vt),
   ("d_mach", d.mach), ("d_pt", d.pt), ("d_hmac", d.hmac), ("d_rho", d.rho), ("d_p", d.p), ("d_t", d.t),
   ("d_a", d.a), ("d_thrust", d.thrust), ("d_hp", d.hp), ("d_mass", d.mass), ("d_agl", d.agl),
   ("d_de", d.de), ("d_da", d.da), ("d_dr", d.dr)] ++
  v "d_grav" d.grav ++ v "d_fnat" d.fnat ++ v "d_mmrc" d.mmrc ++ v "d_faero" d.faero ++ v "d_maero" d.maero ++ v "d_fprop" d.fprop ++ v "d_mprop" d.mprop ++
  v "d_ftot" d.ftot ++ v "d_mtot" d.mtot ++ v "d_fgear" d.fgear ++ v "d_mgear" d.mgear ++ v "d_ffric" d.ffric ++
  v "lastcg" s.lastcg ++
  ((List.range s.gears.size).flatMap fun i =>
    let g := s.gears[i]!
    let p := s!"g{i}_"
    [(p ++ "wow", if g.wow then 1.0 else 0.0), (p ++ "lm0", g.lm0), (p ++ "lm1", g.lm1), (p ++ "lm2", g.lm2),
     (p ++ "slip", g.slip), (p ++ "steer", g.steer), (p ++ "d_fz", d.gearFz[i]!)] ++ v (p ++ "act") g.act)

end DumpRun
