import CityJsb.Plant

/-! `fuelfreezecheck h v gam psi phi alpha e a r t FRAMES`: the reference for `fuelcheck` (flight/src/bin/fuelcheck.rs). Each
argument is the decimal `UInt64` bit pattern of a `Float`. Steps `JsbExact.step` from `CityJsb.init`, first with the surfaces `e a r t` (the frame `JsbPlant::new` flies), then with the
pseudo-random surfaces `fuelcheck` flies, once with `fuelFreeze := true` and once with `false`, and prints an FNV-1a
hash of the observation bits (`CityJsb.obs`) of every frame for each. -/

open JsbExact CityJsb

def fnv (h : UInt64) (x : UInt64) : UInt64 := (h ^^^ x) * 1099511628211

def inp (e a r t : Float) : Input Float := { elev := e, ail := a, rud := r, thr := t, mix := 0.9, brkL := 0, brkR := 0 }

def run (ff : Bool) (s0 : State Float) (first : Input Float) (frames : Nat) : UInt64 := Id.run do
  let mut s := (step s0 first (fuelFreeze := ff)).1
  let mut x : UInt64 := 12345
  let mut h : UInt64 := 14695981039346656037
  let u := fun (x : UInt64) => (x >>> 11).toFloat / 9007199254740992.0
  for _ in [0:frames] do
    let mut surf : Array Float := #[]
    for (a, b) in [((-1.0 : Float), (1.0 : Float)), (-1.0, 1.0), (-0.5, 0.5), (0.0, 1.0)] do
      x := x * 6364136223846793005 + 1442695040888963407
      surf := surf.push (a + (b - a) * u x)
    let (s', d) := step s (inp surf[0]! surf[1]! surf[2]! surf[3]!) (fuelFreeze := ff)
    s := s'
    for v in (obs s' d).data do
      h := fnv h v.toBits
  return h

def main (args : List String) : IO Unit := do
  let f := fun (i : Nat) => Float.ofBits (args[i]!.toNat!.toUInt64)
  let s0 := init (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
  let first := inp (f 6) (f 7) (f 8) (f 9)
  let frames := args[10]!.toNat!
  IO.println s!"freeze {run true s0 first frames}"
  IO.println s!"drain {run false s0 first frames}"
