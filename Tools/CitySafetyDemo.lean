import Spec.CitySafetyChecks

/-! Runs `CitySafety.passThrough` on `CitySafety.tiny` and reports the first frame `vertexSweptCrash` holds. -/

open CitySafety JsbExact

def toF (r : Rat) : Float := Float.ofInt r.num / r.den.toFloat

/-- Nose gear and lowest airframe point, in map metres. -/
def describe (s : State Float) : String :=
  match airframe s with
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
    if vertexSweptCrash tiny s s' then
      IO.println s!"{name}: vertexSweptCrash on frame {k} -> {k + 1} (t = {(k + 1).toFloat / 128} s): {describe s'}"
      return
    s := s'
    if (k + 1) % (128 * 5) == 0 then IO.println s!"  t = {(k + 1) / 128} s: {describe s}"
  IO.println s!"{name}: no vertexSweptCrash in {frames} frames: {describe s}"

def main : IO Unit := do
  for c in startConds do
    let hit := vertexSweptCrash tiny c.state (passThrough.frame (c.state, ()) idle).1
    IO.println s!"start psi={c.psi}: vertexSweptCrash tiny over one idle frame = {hit}"
  run "cruise north into the tower" north cruise (128 * 60)
  run "dive south into the ground" ⟨0, 0, 1500, 50, 3.141592653589793, 0.0223⟩ ⟨0.5, 0, 0, 0⟩ (128 * 120)
