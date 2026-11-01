import CityJsb.Plant

/-!
# Safety of a filter in the city flight demo (DRAFT for review)

`Safe M F`: for every start in `Init` and every sequence of pilot commands, no state the closed loop of the plant
(`JsbExact`) and the filter `F` reaches is a `Crash` with the city map `M`.

Trusted surface of `Safe` (`#spec_surface Safe` in `Spec/CitySafetyChecks.lean` lists it):
* this file: `ratOf`, `InRange`, `Surfaces`, `Surfaces.Valid`, `clampTo`, `Surfaces.clamp`, `Surfaces.toInput`,
  `StartCond`, `StartCond.state`, `startConds`, `Init`, `Filter`, `Filter.frame`, `Reach`, `Pt`, `Box`,
  `Box.Contains`, `CityMap`, `clampR`, `CityMap.terrain`, `Solid`, `combo`, `InHull`, `contactPoints`,
  `outlinePoints`, `ft`, `pointEcef`, `altitudeFt`, `mapPoint`, `airframe`, `HullHits`, `SweptCrash`, `Safe`;
* the plant: `JsbExact.step` and what it calls, the generated `JsbExact.Gen` (from `c172p.xml`),
  `CityJsb.template` and `CityJsb.initAt`. These are trusted because they match JSBSim 1.3.3 bit for bit on the
  validation datasets (measured, not proved);
* libm, opaque to Lean: `jx_sin`, `jx_cos`, `__sincos_stret` (via `JsbExact.jxSin` and friends), `Float.atan2`,
  `Float.pow`, `Float.exp`, `Float.atan`, `Float.asin`, and `Float.sin`, `Float.cos` in `initAt`. Lean's logic knows
  nothing about their values, so a proof of `Safe` needs stated contracts for them (for example error bounds).

Decisions:
1. Airframe: the convex hull of the 7 JSBSim contact points and 5 outline points from FlightGear's c172p visual
   model (fin top, each wingtip's leading and trailing edge).
2. Numbers: each airframe point's map position is the plant's own `Float` computation, read exactly (`ratOf`);
   hulls, terrain and buildings are exact in `Rat` from there. A non-finite pose is a crash.
3. Map frame: the demo's. East and north are ECEF y and z, up is altitude above sea level (`Diag.hsl`'s formula),
   per point. Hulls are taken in these coordinates (see `SweptCrash`).
4. Beyond the ±3000 m grid the terrain continues the edge profile (`World::terrain`'s clamp; 731 to 927 m on the
   demo map); the gate's "off the map is clear" is not sound under this.
5. Contact is checked over each frame's sweep: the hull of the airframe points at both ends of the frame.
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

/-- Points of the aircraft's outline that are not contact points, in the frame and units of `contactPoints`: vertices
of FlightGear's c172p visual model (FGData 2024.1, `Aircraft/c172p/Models/c172-common.ac`, metres, x aft, y up,
z left), placed as that aircraft's `Models/c172p.xml` places it: pitched 3° nose down about the VRP (34, 0, 35.75) in
of its `c172p.xml`. Its gear wheels land within 1 in of `contactPoints`' gear. -/
def outlinePoints : List (V3 Float) :=
  [⟨246.6, 0, 88.7⟩,       -- fin top: highest vertex of object `vstab.001`, (5.463, 1.061, 0) m
   ⟨32.2, -221.5, 58.0⟩,   -- left wingtip leading edge: `wing_left` tip rib, (-0.015, 0.567, 5.626) m
   ⟨75.2, -221.5, 52.5⟩,   -- left wingtip trailing edge: `wing_left` tip rib, (1.067, 0.370, 5.626) m
   ⟨32.2, 221.5, 58.0⟩,    -- right wingtip leading edge: mirror of the left
   ⟨75.2, 221.5, 52.5⟩]    -- right wingtip trailing edge: mirror of the left

/-- One foot in metres, exactly. -/
def ft : Rat := 3048 / 10000

/-- ECEF position (ft) of the structural point `r` (inches) of the aircraft in state `s`, computed in `Float` as `step`
and `gearForces` compute a contact point's location: Earth rotated by `s.epa`, CG at `s.ri` and `s.cg`, attitude
`s.q`. (`gearForces` also shifts the CG's location while a gear leg is on the ground; that case is already a crash.) -/
def pointEcef (s : State Float) (r : V3 Float) : V3 Float :=
  let ce := S.cosS s.epa
  let se := S.sinS s.epa
  let ti2ec : M33 Float := M33.mk' ce se 0 (-se) ce 0 0 0 1
  let locv := ti2ec.mulV s.ri
  let tec2l := (locDerive locv).tec2l
  let tb2l := (s.q.toM.mul (tec2l.mul ti2ec).T).T
  let whlBody := (m9 Gen.Ts2b : M33 Float).mulV (V3.sub r s.cg)
  V3.add (tec2l.T.mulV (tb2l.mulV whlBody)) locv

/-- Altitude above sea level (ft) of the ECEF point `p`, as `step` computes the aircraft's (`Diag.hsl`): distance
from the Earth's centre minus the sea-level radius at the point's geocentric latitude. -/
def altitudeFt (p : V3 Float) : Float :=
  let l := locDerive p
  l.radius - seaLevelRadius l

/-- Map position of the structural point `r` of the aircraft in state `s`, or `none` if a number involved is not
finite. The map frame is the demo's (`CityJsb.obs`, `MapFrame` at latitude and longitude 0): east is ECEF y, north is
ECEF z and up is altitude above sea level, each the plant's `Float` value read exactly and converted to metres. -/
def mapPoint (s : State Float) (r : V3 Float) : Option Pt := do
  let p := pointEcef s r
  return ⟨(← ratOf p.y) * ft, (← ratOf p.z) * ft, (← ratOf (altitudeFt p)) * ft⟩

/-- Map positions of the airframe points in state `s`, or `none` if any is undefined. -/
def airframe (s : State Float) : Option (List Pt) := (contactPoints ++ outlinePoints).mapM (mapPoint s)

/-- Some point of the convex hull of `ps` is in something solid. -/
def HullHits (M : CityMap) (ps : List Pt) : Prop := ∃ q, InHull ps q ∧ Solid M q

/-- The aircraft in state `s` touches the city: some point of the convex hull of its airframe points is in
something solid. A state with a non-finite pose counts as a crash (the simulation has broken down). `Safe` rules out
`Crash` at every reachable state (`safe_no_crash` in `Spec/CitySafetyChecks.lean`). -/
def Crash (M : CityMap) (s : State Float) : Prop :=
  match airframe s with
  | none => True
  | some ps => HullHits M ps

/-- The frame from `s` to `s'` touches the city: some point of the convex hull of the airframe points at both
states is in something solid. This hull contains each point's straight-line path from `s` to `s'`
(`segment_in_sweep`); the plant has no state between frames that would define a curved path. The hull is taken in map
coordinates, whose `z` follows the Earth's curvature, so a straight segment there is a curve in space: for the
12 m airframe the two differ by at most L²/8R ≈ 3 µm. A non-finite pose at either end counts as a crash. -/
def SweptCrash (M : CityMap) (s s' : State Float) : Prop :=
  match airframe s, airframe s' with
  | some ps, some ps' => HullHits M (ps ++ ps')
  | _, _ => True

/-- The filter `F` keeps the aircraft from touching the city `M`, whatever the pilot does: no frame the closed loop
can take from a reachable state touches it. -/
def Safe (M : CityMap) (F : Filter) : Prop :=
  ∀ p u, Reach F p → u.Valid → ¬ SweptCrash M p.1 (F.frame p u).1

end CitySafety
