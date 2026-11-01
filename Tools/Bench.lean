import Jsb.Model
open Vibecheck Jsb Jsb.C172
def timeIt (name : String) (n : Nat) (f : Nat → Int) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut sink : Int := 0
  for i in [0:n] do sink := sink + f i
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {(t1 - t0) / n} ns (sink {sink})"
def main : IO Unit := do
  let s : State := { x := 0, h := ⟨1000*65536⟩, vx := ⟨50*65536⟩, vz := ⟨0⟩, dx := ⟨65536⟩, dz := ⟨100⟩, q := ⟨0⟩, rpm := ⟨2400*65536⟩, tmap := ⟨80*65536⟩, udot := ⟨0⟩, wdot := ⟨0⟩, stall := ⟨0⟩, ah := ⟨0⟩, au := ⟨0⟩, qd := ⟨0⟩, ah1 := ⟨0⟩, au1 := ⟨0⟩, pvz := ⟨0⟩, pvz2 := ⟨0⟩ }
  let inp : Input := { elev := ⟨1000⟩, thr := ⟨30000⟩ }
  let n := 20000
  timeIt "integrate" n fun i => (integrate 7 true { s with vx := ⟨s.vx.raw + i⟩ }).vz.raw
  timeIt "evaluate" n fun i => (evaluate 7 inp { s with vx := ⟨s.vx.raw + i⟩ }).1.ah.raw
  timeIt "atan2" n fun i => (atan2Fx ⟨65536 + i⟩ ⟨50*65536⟩).raw
  timeIt "sqrt" n fun i => (sqrtFx ⟨2500*65536 + i⟩).raw
  timeIt "tbl2" n fun i => (C172.tbl_x_5.eval ⟨5000 + i⟩ ⟨0⟩).raw
  timeIt "liftForce" n fun i => (liftForce { adot := ⟨i⟩, alpha := ⟨5000 + i⟩, ci2vel := ⟨800⟩, elevRad := ⟨1000⟩, flapDeg := 0, hbMac := ⟨65536*14⟩, magBeta := 0, magElevRad := ⟨1000⟩, qAero := ⟨100⟩, qbar := ⟨110000⟩, rho := ⟨70000⟩, stallHyst := 0, uAero := ⟨50*65536⟩, vInd := ⟨5*65536⟩ }).raw
