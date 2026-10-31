import Vibecheck
open Vibecheck

def fmt (f : Float) : String :=
  let r := (f * 10).round / 10
  toString r

def pitchDeg (s : State) : Float := Float.atan2 s.dz.toFloat s.dx.toFloat * 57.2958

def showS (t : Nat) (s : State) : String :=
  s!"t={t/16} x={fmt s.x.toFloat} h={fmt s.h.toFloat} vx={fmt s.vx.toFloat} vz={fmt s.vz.toFloat} u={fmt s.u.toFloat} th={fmt (pitchDeg s)} aV={fmt s.alphaV.toFloat} q={fmt s.q.toFloat} el={fmt s.elev.toFloat} fuel={fmt s.fuel.toFloat} {repr s.phase}"

partial def runCtl (r : Runway) (s : State) (t : Nat) (every : Nat) : IO State := do
  if t % every == 0 then IO.println (showS t s)
  if s.crashed || s.parked && t > 0 then IO.println (showS t s); return s
  if t > 16 * 400 then IO.println "timeout"; return s
  runCtl r (step s (Autoland.control r s)) (t+1) every

def main (args : List String) : IO Unit := do
  let rw := (runways.toArray)
  let which := (args.headD "1").toNat!
  let r := rw[which]!
  -- rolling start so the parked check doesn't end immediately
  let s0 := { initState with vx := 1 }
  let _ ← runCtl r s0 0 (args.tail.headD "16").toNat!
  let t0 ← IO.monoNanosNow
  let ok := rolloutOK r horizon s0
  let t1 ← IO.monoNanosNow
  IO.println s!"rolloutOK={ok} took {(t1-t0).toFloat / 1e6} ms"
