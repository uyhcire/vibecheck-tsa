import Spec.CitySafetyChecks

/-! Runs `CitySafety.passThrough` on `CitySafety.tiny` and reports the first frame `vertexCrash` holds. -/

open CitySafety JsbExact

def toF (r : Rat) : Float := Float.ofInt r.num / r.den.toFloat

/-- Nose gear and lowest airframe point, in map metres. -/
def describe (s : State Float) : String :=
  match airframe tiny s with
  | none => "pose undefined"
  | some ps =>
    let low := ps.foldl (fun m p => min m (toF p.z)) 1e9
    match ps.head? with
    | some p => s!"nose gear at ({toF p.x}, {toF p.y}, {toF p.z}) m, lowest airframe point z = {low} m"
    | none => ""

def run (name : String) (c : StartCond) (u : Surfaces) (frames : Nat) : IO Unit := do
  let mut s := c.state
  IO.println s!"{name}: start {describe s}"
  for k in [0:frames] do
    let s' := (passThrough.frame (s, ()) u).1
    if vertexCrash tiny s' then
      IO.println s!"{name}: vertexCrash after frame {k + 1} (t = {(k + 1).toFloat / 128} s): {describe s'}"
      return
    s := s'
    if (k + 1) % (128 * 5) == 0 then IO.println s!"  t = {(k + 1) / 128} s: {describe s}"
  IO.println s!"{name}: no vertexCrash in {frames} frames: {describe s}"

def main : IO Unit := do
  for c in startConds do
    let hit := vertexCrash tiny c.state
    IO.println s!"start psi={c.psi}: vertexCrash tiny at the start = {hit}"
  run "cruise from the first start" start0 cruise (128 * 60)
  run "dive south into the ground" ⟨-1800, -740, 291, 50, 3.141592653589793, 0.0223, 8⟩ ⟨0.5, 0, 0, 0, 0⟩ (128 * 120)
