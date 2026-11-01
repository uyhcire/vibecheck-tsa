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
def fields (s : State Float) (d : Diag Float) : List (String × Float) := CityJsb.diagFields s d

end DumpRun
