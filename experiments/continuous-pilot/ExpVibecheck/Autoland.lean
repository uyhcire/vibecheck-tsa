import ExpVibecheck.Model

/-! Escape controller (autoland); its quality affects intervention rate, never soundness. -/

namespace ExpVibecheck
namespace Autoland

def park : Input := { stick := 0, throttle := 0, brake := true }

/-- Vertical-speed command (m/s) toward runway `r`. -/
def vzCommand (r : Runway) (s : State) (up : Fx) : Fx :=
  let aim := r.start + 200
  let dist := aim - s.x
  let above := s.h - r.elev
  if r.start - 80 ≤ s.x ∧ above < max 8 (Fx.abs s.vz * 2.5) then
    -(0.4 + 0.12 * above)
  else
    let hGlide := r.elev + 0.07 * dist
    let clearEnd := min (s.x + 800) (r.start - 150)
    let hClear := if s.x < clearEnd then maxTerrain s.x clearEnd + 60 else 0
    let lo : Fx := if dist < 700 then -5 else -11
    if hClear < hGlide then
      Fx.clamp lo 10 (0.25 * (hGlide - s.h) - 0.07 * up)
    else
      Fx.clamp lo 10 (0.25 * (hClear - s.h))

def air (r : Runway) (s : State) : Input :=
  let up := max s.u 15
  let flare := r.start - 80 ≤ s.x ∧ s.h - r.elev < max 8 (Fx.abs s.vz * 2.5)
  let near := r.start - 1500 < s.x
  let vTarget : Fx := if near then 34 else 40
  let vzc0 := vzCommand r s up
  let vzc := if up < 31 then min vzc0 (s.vz - (31 - up)) else vzc0
  let thr := if flare then 0 else Fx.clamp 0 1 (0.45 + 0.15 * (vTarget - up) + 0.05 * (vzc - s.vz))
  let aNc := Fx.clamp 2 25 (P.g + 1.2 * (vzc - s.vz))
  let tanA := Fx.clamp (-0.1) 0.21 (aNc / (P.kN * up * up))
  let stick := Fx.clamp (-1) 1 (tanA * 2.75 - 0.3 * s.q)
  { stick := stick, throttle := thr, brake := false }

def takeoff (s : State) : Input :=
  { stick := if s.u < 27 then 0 else 0.7, throttle := 1, brake := false }

def control (r : Runway) (s : State) : Input :=
  match s.phase with
  | .air => air r s
  | .ground =>
    if s.vx = 0 ∨ (r.start ≤ s.x ∧ s.x ≤ r.stop) then park else takeoff s
  | .crashed _ => park

end Autoland
end ExpVibecheck
