import CityGate

/-! Spot check of the Lean escape law against Rust's `Law::step`: one start (north up the street `x = -120 m`,
100 m, 45 m/s) and the street escape, every frame's surfaces and position as bit patterns, plus frames/s.
`lake build citygatespot && .lake/build/bin/citygatespot`. -/

open CityGate Esc

def hex (f : Float) : String := String.ofList (Nat.toDigits 16 f.toBits.toNat)

def main : IO Unit := do
  let mut p := startPlane (-120.0) (-300.0) 100.0 45.0 0.0 FRAC_PI_2 0.0 (Float.cos 0.0) 0.7
  let mut law := Law.new STREET
  let t0 ← IO.monoNanosNow
  let mut lines : Array String := #[]
  for k in [0:1024] do
    let (u, l) := law.step p
    p := p.step u
    law := l
    let (x, y, z) := p.pos
    lines := lines.push s!"{k} {hex u.elev} {hex u.ail} {hex u.rud} {hex u.thr} {hex x} {hex y} {hex z}"
  let t1 ← IO.monoNanosNow
  for l in lines do IO.println l
  IO.eprintln s!"lean: {1024 * 1000000000 / (t1 - t0)} frames/s; raster top {top}"
