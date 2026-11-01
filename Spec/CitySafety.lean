import CityJsb.Plant

/-!
# Safety of a filter in the city flight demo (DRAFT for review)

`Safe M F`: for every start in `Init` and every sequence of pilot commands, no state the closed loop of the plant
(`JsbExact`) and the filter `F` reaches is a `Crash` with the city map `M`.

Trusted surface of `Safe` (`#spec_surface Safe` in `Spec/CitySafetyChecks.lean` lists it):
* this file: `ratOf`, `InRange`, `Surfaces`, `Surfaces.Valid`, `clampTo`, `Surfaces.clamp`, `Surfaces.toInput`,
  `StartCond`, `StartCond.state`, `startConds`, `Init`, `Filter`, `Filter.frame`, `Reach`, `Pt`, `Box`,
  `Box.Contains`, `CityMap`, `clampR`, `CityMap.terrain`, `Solid`, `combo`, `InHull`, `contactPoints`, `ft`,
  `mapPoint`, `airframe`, `HullHits`, `Crash`, `Safe`;
* the plant: `JsbExact.step` and what it calls, the generated `JsbExact.Gen` (from `c172p.xml`),
  `CityJsb.template` and `CityJsb.initAt`. These are trusted because they match JSBSim 1.3.3 bit for bit on the
  validation datasets (measured, not proved);
* libm, opaque to Lean: `jx_sin`, `jx_cos`, `__sincos_stret` (via `JsbExact.jxSin` and friends), `Float.atan2`,
  `Float.pow`, `Float.exp`, `Float.atan`, `Float.asin`, and `Float.sin`, `Float.cos` in `initAt`. Lean's logic knows
  nothing about their values, so a proof of `Safe` needs stated contracts for them (for example error bounds).

Decisions for review:
1. Airframe: the convex hull of the 7 contact points, so wings and fuselage between the points count; the fin top
   and the wingtips' chord are outside it.
2. Numbers: plant `Float`s are read exactly (`ratOf`); geometry is exact in `Rat`, except that the cosine and sine of
   the Earth angle are the plant's own libm values. A non-finite pose is a crash.
3. Map frame: the tangent plane at latitude and longitude 0. The demo's `z` is altitude above sea level instead;
   the two differ by d²/2R, up to 0.7 m at the map's edges and 1.4 m at its corners, with the tangent plane lower.
4. Beyond the ±3000 m grid the terrain continues the edge profile (`World::terrain`'s clamp; 731 to 927 m on the
   demo map); the gate's "off the map is clear" is not sound under this.
5. Contact is checked at every frame's state (1/128 s), as JSBSim does, not along the path between frames.
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

/-- A start: map position `x` east, `y` north, `z` up (m, see `mapPoint`), true airspeed `v` (m/s), heading `psi`
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

/-- A point on the map (m): `x` east, `y` north, `z` up. -/
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

/-- One foot in metres, exactly. -/
def ft : Rat := 3048 / 10000

/-- Map position of the structural point `r` (inches) of the aircraft in state `s`, or `none` if a number involved
is not finite. The pose is the plant's: CG at `s.cg` in the structural frame and at `s.ri` (ft) in the inertial
frame, body-to-inertial rotation from `s.q` (`Quat.toM`), Earth rotated by `s.epa` (whose cosine and sine are the
plant's own, as in `step`). The map is the plane tangent to the WGS84 ellipsoid at latitude and longitude 0: ECEF
`(a, 0, 0)` is the map origin, ECEF y is east, ECEF z is north and ECEF x − a is up. -/
def mapPoint (s : State Float) (r : V3 Float) : Option Pt := do
  let ce ← ratOf (S.cosS s.epa)
  let se ← ratOf (S.sinS s.epa)
  let a ← ratOf Gen.a
  let (q0, q1, q2, q3) := (← ratOf s.q.q0, ← ratOf s.q.q1, ← ratOf s.q.q2, ← ratOf s.q.q3)
  let (cx, cy, cz) := (← ratOf s.cg.x, ← ratOf s.cg.y, ← ratOf s.cg.z)
  let (rx, ry, rz) := (← ratOf r.x, ← ratOf r.y, ← ratOf r.z)
  let (px, py, pz) := (← ratOf s.ri.x, ← ratOf s.ri.y, ← ratOf s.ri.z)
  -- body axes (ft): x forward, y right, z down
  let (bx, by_, bz) := ((cx - rx) / 12, (ry - cy) / 12, (cz - rz) / 12)
  let (t11, t12, t13) := (q0*q0 + q1*q1 - q2*q2 - q3*q3, 2 * (q1*q2 + q0*q3), 2 * (q1*q3 - q0*q2))
  let (t21, t22, t23) := (2 * (q1*q2 - q0*q3), q0*q0 - q1*q1 + q2*q2 - q3*q3, 2 * (q2*q3 + q0*q1))
  let (t31, t32, t33) := (2 * (q1*q3 + q0*q2), 2 * (q2*q3 - q0*q1), q0*q0 - q1*q1 - q2*q2 + q3*q3)
  let ix := px + t11 * bx + t21 * by_ + t31 * bz
  let iy := py + t12 * bx + t22 * by_ + t32 * bz
  let iz := pz + t13 * bx + t23 * by_ + t33 * bz
  let (ex, ey, ez) := (ce * ix + se * iy, -se * ix + ce * iy, iz)
  return ⟨ey * ft, ez * ft, (ex - a) * ft⟩

/-- Map positions of the contact points in state `s`, or `none` if any is undefined. -/
def airframe (s : State Float) : Option (List Pt) := contactPoints.mapM (mapPoint s)

/-- Some point of the convex hull of `ps` is in something solid. -/
def HullHits (M : CityMap) (ps : List Pt) : Prop := ∃ q, InHull ps q ∧ Solid M q

/-- The aircraft in state `s` touches the city: some point of the convex hull of its contact points is in
something solid. A state with a non-finite pose counts as a crash (the simulation has broken down). -/
def Crash (M : CityMap) (s : State Float) : Prop :=
  match airframe s with
  | none => True
  | some ps => HullHits M ps

/-- The filter `F` keeps the aircraft from crashing into the city `M`, whatever the pilot does. -/
def Safe (M : CityMap) (F : Filter) : Prop := ∀ p, Reach F p → ¬ Crash M p.1

end CitySafety
