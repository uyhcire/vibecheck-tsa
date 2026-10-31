import Vibecheck
open Vibecheck

def fmt (f : Float) : String := toString ((f * 10).round / 10)

def pitchDeg (s : State) : Float := Float.atan2 s.dz.toFloat s.dx.toFloat * 57.2958

/-- Where an autoland rollout ends: (steps, final state). -/
def rolloutEnd (r : Runway) : Nat → State → Nat → Nat × State
  | 0, s, k => (k, s)
  | n + 1, s, k =>
    if s.crashed || s.parked || r.stop < s.x then (k, s)
    else rolloutEnd r n (step s (Autoland.control r s)) (k + 1)

def scriptStick (t : Float) : Fx :=
  if t < 6 then 0 else if t < 12 then 0.5 else if t < 30 then 0.05 else -1

def main : IO Unit := do
  let mut s := initState
  for i in [0:16*70] do
    let t := i.toFloat / 16
    let u : Input := { stick := scriptStick t, throttle := 1, brake := false }
    let a := filter s u
    if i % 16 == 0 || a != u then
      let ends := runways.map fun r =>
        let (k, e) := rolloutEnd r horizon s 0
        s!"{k}:{repr e.phase}@{fmt e.x.toFloat}"
      IO.println s!"t={fmt t} x={fmt s.x.toFloat} h={fmt s.h.toFloat} u={fmt s.u.toFloat} th={fmt (pitchDeg s)} {repr s.phase} override={a != u} stick={fmt a.stick.toFloat} | {ends}"
    s := step s a
