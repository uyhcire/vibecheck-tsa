import CityGate

/-! Spot check of the Lean autoland against Rust's `Auto` (`flight/src/autoland.rs`): two starts with 8 lb per tank,
200 frames each, every frame's surfaces (elevator, aileron, rudder, throttle, brake) and map position as bit
patterns. Start A: variant 1 (left first) from (0, 0, 300 m) heading north at 45 m/s (navigation); start B:
variant 0 from (-2000, -1340, 150 m) heading east at 40 m/s (on final, in the funnel).
`lake build citygatespot && .lake/build/bin/citygatespot`. -/

open CityGate Esc

def hex (f : Float) : String := String.ofList (Nat.toDigits 16 f.toBits.toNat)

def run (tag : String) (variant : Nat) (x y z v psi : Float) : IO Unit := do
  let mut p := startPlane x y z v 0.0 psi 0.0 1.0 0.7 8.0
  let mut a := Auto.new variant
  for k in [0:200] do
    let (u, a') := a.controls p
    p := p.step u
    a := a'
    let (px, py, pz) := p.pos
    IO.println s!"{tag} {k} {hex u.elev} {hex u.ail} {hex u.rud} {hex u.thr} {hex u.brk} {hex px} {hex py} {hex pz}"

def main : IO Unit := do
  run "A" 1 0.0 0.0 300.0 45.0 FRAC_PI_2
  run "B" 0 (-2000.0) (-1340.0) 150.0 40.0 0.0
