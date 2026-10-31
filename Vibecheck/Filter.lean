import Vibecheck.Autoland

namespace Vibecheck

/-- Max escape-rollout length: 200 s. -/
def horizon : Nat := 3200

def rolloutOK (r : Runway) : Nat → State → Bool
  | n, s =>
    if s.crashed then false
    else if s.parked then true
    else if r.stop < s.x then false
    else match n with
      | 0 => false
      | n + 1 => rolloutOK r n (step s (Autoland.control r s))

/-- Runways ahead first (nearest first), then the rest: escapes keep flying forward. -/
def preferred (s : State) : List Runway :=
  runways.filter (fun r => s.x < r.start) ++ runways.filter (fun r => !(s.x < r.start))

def inS (s : State) : Bool := (preferred s).any fun r => rolloutOK r horizon s

def escapeRunway (s : State) : Option Runway :=
  (preferred s).find? fun r => rolloutOK r horizon s

def escape (s : State) : Input :=
  match escapeRunway s with
  | some r => Autoland.control r s
  | none => Autoland.park

def filter (s : State) (u : Input) : Input :=
  let u := u.clampAdm
  if inS (step s u) then u else escape s

/-- The escape trajectory, for display. -/
def rolloutPath (r : Runway) : Nat → State → List State
  | 0, s => [s]
  | n + 1, s =>
    if s.crashed ∨ s.parked then [s] else s :: rolloutPath r n (step s (Autoland.control r s))

end Vibecheck
