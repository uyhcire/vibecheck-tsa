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
    (1100, 60), (1400, 110), (1700, 180), (1850, 215), (2000, 195), (2200, 250), (2300, 240),
    (2550, 170), (2850, 125), (3100, 120),
    (3300, 120), (4100, 120),
    (4400, 165), (4750, 250), (5000, 310), (5150, 290), (5300, 360), (5450, 300),
    (5750, 200), (6100, 110), (6500, 50),
    (6900, 30), (8000, 30),
    (8200, 60), (8500, 200), (8800, 420), (9200, 560) ]

/-- The runways, in order of `start`. Each lies on a flat stretch of `terrainPts`. -/
def runways : List Runway :=
  [ ⟨0, 650, 50⟩, ⟨3350, 4050, 120⟩, ⟨6950, 7900, 30⟩ ]

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
