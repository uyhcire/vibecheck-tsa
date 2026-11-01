import CityJsb.Plant

/-!
# Safety of a filter in the city flight demo (DRAFT for review)

`Safe M F`: for every start in `Init` and every sequence of pilot commands, no state the closed loop of the plant
(`JsbExact`) and the filter `F` reaches is a `Crash` with the city map `M`.

Trusted surface of `Safe` (`#spec_surface Safe` in `Spec/CitySafetyChecks.lean` lists it):
* this file: `ratOf`, `InRange`, `Surfaces`, `Surfaces.Valid`, `clampTo`, `Surfaces.clamp`, `Surfaces.toInput`,
  `StartCond`, `StartCond.state`, `startConds`, `Init`, `Filter`, `Filter.frame`, `Reach`, `Pt`, `Box`,
  `Box.Contains`, `CityMap`, `clampR`, `CityMap.terrain`, `Solid`, `combo`, `InHull`, `contactPoints`,
  `flightGearPoints`, `ft`, `Report`, `report`, `mulRows`, `mapPoint`, `airframe`, `HullHits`, `Crash`, `Safe`;
* the plant: `JsbExact.step` and what it calls, the generated `JsbExact.Gen` (from `c172p.xml`),
  `CityJsb.template` and `CityJsb.initAt`. These are trusted because they match JSBSim 1.3.3 bit for bit on the
  validation datasets (measured, not proved);
* libm, opaque to Lean: `jx_sin`, `jx_cos`, `__sincos_stret` (via `JsbExact.jxSin` and friends), `Float.atan2`,
  `Float.pow`, `Float.exp`, `Float.atan`, `Float.asin`, and `Float.sin`, `Float.cos` in `initAt`. Lean's logic knows
  nothing about their values, so a proof of `Safe` needs stated contracts for them (for example error bounds).

Decisions:
1. Airframe: the convex hull of the stock c172p's 7 contact points and FlightGear's c172p's 13 default contact
   points, the points at which FlightGear decides crashes.
2. Numbers: the plant reports the aircraft's pose as `Float`s (`report`: the CG's location and altitude, and the
   rotation matrix `Tb2l`), read exactly (`ratOf`); airframe points, hulls, terrain and buildings are exact in `Rat`
   from there. A non-finite pose is a crash.
3. Map frame: the demo's. The reported CG position is east = ECEF y, north = ECEF z, up = altitude above sea level
   (`Diag.hsl`), as `CityJsb.obs` reports it. Airframe points are placed from it with the reported `Tb2l`, in the
   local north-east-down frame at the CG, which turns by at most 0.03° against the map axes over the ±3000 m map
   (under 6 mm across the airframe).
4. Beyond the ±3000 m grid the terrain continues the edge profile (`World::terrain`'s clamp; 731 to 927 m on the
   demo map); the gate's "off the map is clear" is not sound under this.
5. Contact is checked at each frame's state. Frames are 1/128 s (0.39 m at 50 m/s), so contact strictly between
   two frames is not counted; `Spec/CitySafetyChecks.lean` shows a 2 cm ledge this misses.
6. Touching counts as contact (all solids are closed).
-/

namespace CitySafety
open JsbExact

/-! ## Numbers -/

/-- The exact value of a finite `Float`, decoded from its IEEE 754 binary64 bits; `none` for NaN and infinities.
Normal numbers are `(2^52 + m) * 2^(e - 1075)`, subnormal ones `m * 2^(-1074)`. -/
def ratOf (f : Float) : Option Rat :=
  let b : Nat := f.toBits.toNat
  let e : Nat := b / 2 ^ 52 % 2 ^ 11
  let m : Nat := b % 2 ^ 52
  let mag : Rat := if e = 0 then (m : Rat) / 2 ^ 1074 else ((2 ^ 52 + m : Nat) : Rat) * 2 ^ e / 2 ^ 1075
  if e = 2 ^ 11 - 1 then none else some (if b / 2 ^ 63 = 1 then -mag else mag)

/-! ## Pilot commands and the filter -/

/-- The four controls commanded every frame, in JSBSim's normalised units (`fcs/elevator-cmd-norm` and so on). -/
structure Surfaces where
  elev : Float
  ail : Float
  rud : Float
  thr : Float

/-- `x` is a finite number in `[lo, hi]`. -/
def InRange (lo hi : Rat) (x : Float) : Prop := ∃ r, ratOf x = some r ∧ lo ≤ r ∧ r ≤ hi

/-- A physically possible command: elevator, aileron and rudder in `[-1, 1]`, throttle in `[0, 1]`. -/
def Surfaces.Valid (u : Surfaces) : Prop :=
  InRange (-1) 1 u.elev ∧ InRange (-1) 1 u.ail ∧ InRange (-1) 1 u.rud ∧ InRange 0 1 u.thr

/-- `x` clamped to `[lo, hi]`; NaN becomes `lo`. -/
def clampTo (lo hi x : Float) : Float := if lo ≤ x then (if x ≤ hi then x else hi) else lo

/-- What reaches the plant from a filter's output: every control clamped to its range. -/
def Surfaces.clamp (u : Surfaces) : Surfaces :=
  ⟨clampTo (-1) 1 u.elev, clampTo (-1) 1 u.ail, clampTo (-1) 1 u.rud, clampTo 0 1 u.thr⟩

/-- The plant input for given controls: mixture 0.9 and brakes released, as in the demo (`CityJsb.stepE`). -/
def Surfaces.toInput (u : Surfaces) : Input Float :=
  { elev := u.elev, ail := u.ail, rud := u.rud, thr := u.thr, mix := 0.9, brkL := 0, brkR := 0 }

/-- A safety filter: a memory of type `σ`, its value at the start, and one frame's decision, which maps the memory,
the plant state and the pilot's command to the controls to apply and the next memory. -/
structure Filter where
  σ : Type
  start : State Float → σ
  act : σ → State Float → Surfaces → Surfaces × σ

/-- One closed-loop frame (1/128 s): the filter sees the state and the pilot's command `u`, its output is clamped,
and the plant steps once. -/
def Filter.frame (F : Filter) (p : State Float × F.σ) (u : Surfaces) : State Float × F.σ :=
  let (a, m) := F.act p.2 p.1 u
  ((step p.1 a.clamp.toInput).1, m)

/-! ## Starting states -/

/-- A start: map position `x` east, `y` north (m, see `mapPoint`), `z` metres above the plane tangent to sea level at
the map origin (at `x = y = 0` this is the altitude above sea level), true airspeed `v` (m/s), heading `psi`
(rad, clockwise from north) and angle of attack `alpha` (rad); flight-path angle and bank are zero. -/
structure StartCond where
  x : Float
  y : Float
  z : Float
  v : Float
  psi : Float
  alpha : Float

/-- The plant state of a start; engine, fuel and mass state are `CityJsb.template`'s. -/
def StartCond.state (c : StartCond) : State Float := CityJsb.initAt c.x c.y c.z c.v 0 c.psi 0 c.alpha

/-- The allowed starts: wings level, level flight at 50 m/s, 1500 m above the map origin (on the demo map, seed
1337, the terrain peaks at 927 m and the roofs at 459 m), heading north, east, south or west. -/
def startConds : List StartCond :=
  [⟨0, 0, 1500, 50, 0, 0.0223⟩, ⟨0, 0, 1500, 50, 1.5707963267948966, 0.0223⟩,
   ⟨0, 0, 1500, 50, 3.141592653589793, 0.0223⟩, ⟨0, 0, 1500, 50, 4.71238898038469, 0.0223⟩]

/-- The allowed starting states. -/
def Init (s : State Float) : Prop := ∃ c ∈ startConds, s = c.state

/-- The plant states and filter memories the closed loop can reach: a start, then any number of frames, each with
any physically possible pilot command. -/
inductive Reach (F : Filter) : State Float × F.σ → Prop
  | init {s : State Float} : Init s → Reach F (s, F.start s)
  | step {p : State Float × F.σ} (u : Surfaces) : u.Valid → Reach F p → Reach F (F.frame p u)

/-! ## The city -/

/-- A point on the map (m): `x` east, `y` north, `z` altitude above sea level. -/
structure Pt where
  x : Rat
  y : Rat
  z : Rat

/-- A building: the closed box `[x0, x1] × [y0, y1] × [z0, z1]` (m), as `Building` in `flight/src/world.rs`. -/
structure Box where
  x0 : Rat
  x1 : Rat
  y0 : Rat
  y1 : Rat
  z0 : Rat
  z1 : Rat

/-- `q` is in the box `b`, boundary included. -/
def Box.Contains (b : Box) (q : Pt) : Prop :=
  b.x0 ≤ q.x ∧ q.x ≤ b.x1 ∧ b.y0 ≤ q.y ∧ q.y ≤ b.y1 ∧ b.z0 ≤ q.z ∧ q.z ≤ b.z1

/-- A city map, as `World` in `flight/src/world.rs`: terrain heights on an `n × n` grid of spacing `spacing` whose
corner vertex `(0, 0)` is at `(-half, -half)`, and buildings. The demo has `half = 3000`, `spacing = 20`, `n = 301`. -/
structure CityMap where
  half : Rat
  spacing : Rat
  n : Nat
  /-- Height (m) of grid vertex `(i, j)`, at `(-half + i * spacing, -half + j * spacing)`; `terr[j * TN + i]`. -/
  height : Nat → Nat → Rat
  boxes : List Box

/-- `x` clamped to `[lo, hi]`. -/
def clampR (lo hi x : Rat) : Rat := max lo (min hi x)

/-- Terrain height (m) at `(x, y)`: `World::terrain` in exact arithmetic. Grid coordinates are clamped to the grid,
so beyond the edge the terrain continues the edge's profile. Each cell is split along its diagonal from vertex
`(i, j)` to `(i + 1, j + 1)` and the height is interpolated linearly in the triangle containing the point. -/
def CityMap.terrain (M : CityMap) (x y : Rat) : Rat :=
  let fx := clampR 0 (M.n - 1 : Nat) ((x + M.half) / M.spacing)
  let fy := clampR 0 (M.n - 1 : Nat) ((y + M.half) / M.spacing)
  let i := min fx.floor.toNat (M.n - 2)
  let j := min fy.floor.toNat (M.n - 2)
  let u := fx - i
  let v := fy - j
  let (h00, h10, h01, h11) := (M.height i j, M.height (i + 1) j, M.height i (j + 1), M.height (i + 1) (j + 1))
  if v ≤ u then h00 + u * (h10 - h00) + v * (h11 - h10) else h00 + v * (h01 - h00) + u * (h11 - h01)

/-- `q` is in something solid: at or below the terrain, or in a building. Touching counts. -/
def Solid (M : CityMap) (q : Pt) : Prop :=
  q.z ≤ M.terrain q.x q.y ∨ ∃ b ∈ M.boxes, b.Contains q

/-! ## The airframe -/

/-- The weighted sum `w₁ p₁ + w₂ p₂ + …` (extra weights or points are ignored). -/
def combo : List Rat → List Pt → Pt
  | w :: ws, p :: ps => let r := combo ws ps; ⟨w * p.x + r.x, w * p.y + r.y, w * p.z + r.z⟩
  | _, _ => ⟨0, 0, 0⟩

/-- `q` is in the convex hull of `ps`: a weighted average of them with non-negative weights summing to 1. -/
def InHull (ps : List Pt) (q : Pt) : Prop :=
  ∃ ws : List Rat, ws.length = ps.length ∧ (∀ w ∈ ws, 0 ≤ w) ∧ ws.sum = 1 ∧ combo ws ps = q

/-- The c172p's 7 contact points from `c172p.xml` (JSBSim structural frame, inches, x aft, y right, z up): nose gear,
left and right main gear, propeller hub, tail skid, left and right wingtips. -/
def contactPoints : List (V3 Float) := Gen.gears.toList.map fun g => ⟨g[1]!, g[2]!, g[3]!⟩

/-- FlightGear's c172p contact points (FGData 2024.1, `Aircraft/c172p/c172p.xml`), at their positions in the default
configuration (no float, amphibian or ski kit, gear intact, solid ground), in the frame and units of `contactPoints`.
FlightGear decides crashes at these points. Its structural frame is shifted by (+0.77, 0, +0.07) in from this one: the
mean offset of the three gear points both files share, which then agree to within 0.8 in (0.56 in RMS). -/
def flightGearPoints : List (V3 Float) :=
  [⟨-6.5, 0, -20.2⟩,      -- NOSE (-7.3, 0, -20.3)
   ⟨58.1, -43, -15.2⟩,    -- LEFT_MAIN (57.3, -43, -15.3)
   ⟨58.1, 43, -15.0⟩,     -- RIGHT_MAIN (57.3, 43, -15.1)
   ⟨227.5, 0, 17.1⟩,      -- TAIL_SKID (226.7, 0, 17)
   ⟨20.8, -232, 50.1⟩,    -- LEFT_TIP (20, -232, 50)
   ⟨20.8, 232, 50.1⟩,     -- RIGHT_TIP (20, 232, 50)
   ⟨-6.0, 0, 0.1⟩,        -- FRONT_BROKEN_GEAR (-6.8, 0, 0)
   ⟨59.0, -48, 0.1⟩,      -- LEFT_BROKEN_GEAR (58.2, -48, 0)
   ⟨59.0, 48, 0.1⟩,       -- RIGHT_BROKEN_GEAR (58.2, 48, 0)
   ⟨-118.2, 0, 35.1⟩,     -- NOSE_TOP (-119, 0, 35)
   ⟨-118.2, 0, 8.1⟩,      -- NOSE, type STRUCTURE (-119, 0, 8)
   ⟨-3.9, 0, 60.1⟩,       -- COCKPIT_TOP (-4.7, 0, 60)
   ⟨254.3, 0, 90.1⟩]      -- TOP_VS (253.5, 0, 90)

/-- One foot in metres, exactly. -/
def ft : Rat := 3048 / 10000

/-- What the plant reports about the aircraft in state `s`, in `Float` as `step` computes it: the CG's ECEF location
(ft; `Diag.loc`: Earth rotated by `s.epa`, CG at `s.ri`), its altitude above sea level (ft; `Diag.hsl`: distance from
the Earth's centre minus the sea-level radius at its geocentric latitude), and the body-to-local rotation matrix
`Tb2l` from the attitude `s.q` (rows local north, east, down; columns body x forward, y right, z down). -/
structure Report where
  loc : V3 Float
  hsl : Float
  tb2l : M33 Float

def report (s : State Float) : Report :=
  let ce := S.cosS s.epa
  let se := S.sinS s.epa
  let ti2ec : M33 Float := M33.mk' ce se 0 (-se) ce 0 0 0 1
  let loc := ti2ec.mulV s.ri
  let l := locDerive loc
  { loc, hsl := l.radius - seaLevelRadius l, tb2l := (s.q.toM.mul (l.tec2l.mul ti2ec).T).T }

/-- `m · v` for a 3 × 3 matrix given row by row as 9 numbers (missing entries count as 0). -/
def mulRows (m : List Rat) (v : Rat × Rat × Rat) : Rat × Rat × Rat :=
  let a := fun i => m.getD i 0
  (a 0 * v.1 + a 1 * v.2.1 + a 2 * v.2.2, a 3 * v.1 + a 4 * v.2.1 + a 5 * v.2.2, a 6 * v.1 + a 7 * v.2.1 + a 8 * v.2.2)

/-- Map position of the structural point `r` (inches) of the aircraft in state `s`, or `none` if a number involved is
not finite. Exact (`ratOf`) from the plant's reported values: the point's offset from the CG is `Ts2b · (r - cg)` in
body axes (ft; `Ts2b` maps structural inches, x aft, to body feet, x forward), `Tb2l` turns it into local north, east
and down, and the map position is the reported CG position (east = ECEF y, north = ECEF z, up = `hsl`, as the demo's
`CityJsb.obs`) plus that offset, converted to metres. -/
def mapPoint (s : State Float) (r : V3 Float) : Option Pt := do
  let rep := report s
  let ts2b ← Gen.Ts2b.toList.mapM ratOf
  let tb2l ← [rep.tb2l.a11, rep.tb2l.a12, rep.tb2l.a13, rep.tb2l.a21, rep.tb2l.a22, rep.tb2l.a23,
    rep.tb2l.a31, rep.tb2l.a32, rep.tb2l.a33].mapM ratOf
  let off := ((← ratOf r.x) - (← ratOf s.cg.x), (← ratOf r.y) - (← ratOf s.cg.y), (← ratOf r.z) - (← ratOf s.cg.z))
  let (n, e, d) := mulRows tb2l (mulRows ts2b off)
  return ⟨((← ratOf rep.loc.y) + e) * ft, ((← ratOf rep.loc.z) + n) * ft, ((← ratOf rep.hsl) - d) * ft⟩

/-- Map positions of the airframe points in state `s`, or `none` if any is undefined. -/
def airframe (s : State Float) : Option (List Pt) := (contactPoints ++ flightGearPoints).mapM (mapPoint s)

/-- Some point of the convex hull of `ps` is in something solid. -/
def HullHits (M : CityMap) (ps : List Pt) : Prop := ∃ q, InHull ps q ∧ Solid M q

/-- The aircraft in state `s` touches the city: some point of the convex hull of its airframe points is in
something solid. A state with a non-finite pose counts as a crash (the simulation has broken down). -/
def Crash (M : CityMap) (s : State Float) : Prop :=
  match airframe s with
  | none => True
  | some ps => HullHits M ps

/-- The filter `F` keeps the aircraft from touching the city `M`, whatever the pilot does: no state the closed loop
can reach is a crash. Contact is checked at each frame's state (decision 5). -/
def Safe (M : CityMap) (F : Filter) : Prop :=
  ∀ p, Reach F p → ¬ Crash M p.1

end CitySafety
