import Vibecheck.Fixed

namespace Vibecheck

structure Runway where
  start : Fx
  stop : Fx
  elev : Fx
  deriving DecidableEq, Repr, Inhabited

/-- Terrain breakpoints `(x, z)` in metres, sorted by `x`; flat beyond both ends. -/
def terrainPts : List (Fx × Fx) :=
  [ (-400, 50), (0, 50), (700, 50),
    (900, 70), (1150, 150), (1350, 240), (1500, 215), (1650, 300), (1750, 280),
    (1950, 160), (2300, 110), (2700, 140), (3100, 120),
    (3300, 120), (4100, 120),
    (4300, 170), (4550, 330), (4700, 410), (4850, 370), (5050, 470), (5150, 300),
    (5500, 210), (5900, 90), (6300, 40),
    (6600, 30), (7700, 30),
    (7900, 60), (8200, 260), (8500, 520), (8900, 560) ]

/-- The runways, in order of `start`. Each lies on a flat stretch of `terrainPts`. -/
def runways : List Runway :=
  [ ⟨0, 650, 50⟩, ⟨3350, 4050, 120⟩, ⟨6650, 7600, 30⟩ ]

/-- Linear interpolation between `(x0,z0)` and `(x1,z1)` at `x` (requires `x0 < x1`). -/
def lerp (x0 z0 x1 z1 x : Fx) : Fx := z0 + (z1 - z0) * ((x - x0) / (x1 - x0))

def terrainOn : List (Fx × Fx) → Fx → Fx
  | [], _ => 0
  | [(_, z)], _ => z
  | (x0, z0) :: (x1, z1) :: rest, x =>
    if x ≤ x0 then z0
    else if x ≤ x1 then lerp x0 z0 x1 z1 x
    else terrainOn ((x1, z1) :: rest) x

def terrain (x : Fx) : Fx := terrainOn terrainPts x

def runwayAt (x : Fx) : Option Runway :=
  runways.find? fun r => r.start ≤ x ∧ x ≤ r.stop

def maxTerrain (a b : Fx) : Fx :=
  terrainPts.foldl (fun m p => if a < p.1 ∧ p.1 < b then max m p.2 else m)
    (max (terrain a) (terrain b))

def clipsBreakpoint (x0 h0 x1 h1 : Fx) : Bool :=
  terrainPts.any fun p => x0 < p.1 ∧ p.1 < x1 ∧ lerp x0 h0 x1 h1 p.1 < p.2

end Vibecheck
