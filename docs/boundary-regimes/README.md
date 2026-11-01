# Boundary regimes of the gate filter

Under the safety objective (`docs/safety-objective.md`), the closed loop is safe when no reachable state is a **crash: actual contact between the airframe and terrain or a building, with no clearance margin**. Flight-envelope limits (α, load factor, minimum airspeed, stall) are not part of safety, and margins and terminal sets are a filter's design choices. Near any one obstacle the boundary between states the aircraft can still escape from and states it cannot is made of distinct pieces, each named by what binds first. This folder maps those pieces in Luis Pabon's procedural city (`flight/src/world.rs`, seed 1337): for each, slices through the state space at real locations, markers along them drawn at contact, the binding cause at every point, and one-line GUI demos of the closest calls.

The gate filter (`--safety-filter exact-rollout`, `flight/src/envfilter.rs`) is the subject: it accepts a state when one of its six escapes, flown by exact rollout on a fork of the JSBSim c172p, keeps **4 m** of airframe clearance and reaches a terminal set (a verified climb-out). That 4 m is the gate's own design choice, so it is reported separately from the contact markers, as a property of the filter.

Start with [SHOWCASE.md](SHOWCASE.md) for the demos.

## Regimes

| Regime | Slice | Parameter | Gate accepts (its 4 m margin) | Proven safe (contact) | Best found (contact) | Proven unsafe | Gate's own margin | Escape library and terminal sets | Outer-bound slack | Dominant source of the gap |
|---|---|---|---|---|---|---|---|---|---|---|
| [1 terrain or roof below](01-terrain-roof-below/README.md) | street dive | height above the street (m) | 32.6 | 28.7 | 20.6 | 4.7 | 3.9 | 8.1 | 15.9 | escape law's load-factor cap |
| | park dive | height above the park (m) | 33.0 | 28.7 | 24.1 | 5.9 | 4.3 | 4.6 | 18.2 | load-factor cap ≈ margin |
| | slow valley | airspeed (m/s) | 24.8 | 20.4 | ≤ 20.0 | – | 4.4 | ≥ 0.4 | – | the gate's margin |
| | fast dive | airspeed (m/s) | 63.1 | 66.9 | ≥ 95.0 | – | 3.8 | ≥ 28.1 | – | escape law's load-factor cap |
| [2 wall beside](02-wall-beside/README.md) | distance | distance to the face (m) | 16.0 | 12.0 | 9.5 | 0.0 | 4.0 | 2.5 | 9.5 | the gate's margin |
| | angle | heading angle into the face (°) | 17.7 | 20.8 | 28.4 | – | 3.1 | 7.6 | – | escape library (no 50°+ roll-away) |
| [3 canyon](03-canyon/README.md) | canyon run | height above the street (m) | 121.1 | 109.9 | 26.6 | – | 11.1 | 83.3 | – | terminal sets |
| [4 wall ahead](04-wall-ahead/README.md) | head-on | distance to the face (m) | 188.0 | 181.1 | 114.9 | 25.3 | 6.9 | 66.2 | 89.6 | escape library (no break-turn) |
| | slow wallow | distance to the face (m) | 194.1 | 194.1 | 121.8 | 13.8 | 0.0 | 72.4 | 108.0 | escape library (no break-turn) |
| [5 rising terrain](05-rising-terrain/README.md) | ridge | distance to the crest (m) | 360.4 | 357.8 | 274.3 | 194.2 | 2.6 | 83.5 | 80.2 | escape library (no break-turn) |

Gaps are in the slice's unit and read left to right: **gate's own margin** = gate accepts → proven safe (what the 4 m costs on this slice); **escape library and terminal sets** = proven safe → best found (the rest of the gate's conservatism); **outer-bound slack** = best found → proven unsafe (the bound's looseness, or the search's weakness; the true boundary lies in between). "–": no marker in the slice's range. On the speed and angle slices larger values are closer to danger; there "proven safe" can sit past "gate accepts" (the margin costs speed or angle).

**Regimes: what changed and why.**

- **Five regimes, not seven.** The first pass had "low-speed envelope" and "high-speed envelope" regimes. Under the objective an envelope limit is not a safety boundary, so they are gone; their first-pass material is in the [appendix](appendix-envelope/README.md), labelled. The slices that end in contact were re-run here: the slow valley and the fast dive as slices of regime 1 (contact with the ground), the slow wallow as a slice of regime 4 (contact with the tower). On those slices the escape law's α cap (slow) or load-factor cap (fast) is what limits the pull-out, and those caps are the gate's design choices too.
- **The fast dive changed most.** Held to the c172's 3.8 g limit load, the first pass found the boundary at 67 to 71 m/s. With no envelope limit the search pulls out of a 95 m/s dive from 45 m at up to 6.8 g (the plant itself pulls 6.6 g at 66 m/s with full aft stick), so the gap there is the escape law's 3.5 g cap.
- **1 hands over to 3:** in the street dive, once the pull-out clears the floor, every escape but the street escape hits the street's walls: above the floor the street dive is a canyon.
- **3 is the terminal-set regime:** nothing is close ahead and the street-following escapes hit nothing; what binds is that the gate's terminal sets do not fit below the roofs. The objective has no terminal sets, so this whole gap (83 m) belongs to the gate's proof device.

**The biggest source of conservatism** is the escape library's lack of a hard break-turn: on the head-on wall, the slow wallow and the ridge, the richer search's best programs all start by rolling straight into a 66° to 80° bank at 2.2 to 4.9 g, where the library's turns wait for the climb to establish and then hold 30° or 40°; that is 66 to 84 m on each of those slices. The terminal sets dominate the canyon (83 m). **The gate's 4 m margin** costs 2.6 to 4.4 units on most slices, 6.9 m head-on at the wall and 11.1 m in the canyon (where the first escape to verify skims a wall), and nothing on the slow wallow (a terminal test sets that boundary). It is the largest share of the gap only where the gate is otherwise close to the best found: the park dive, the slow valley and the wall beside.

**How meaningful the outer bounds are.** Sound, under stated assumptions, but loose. They give a marker on 6 of the 10 slices: within 16 to 18 m of the best found on the dives, 80 m on the ridge (the tightest bracket relative to the distances involved, because the ridge is wide enough for the crossing test), 90 m and 108 m on the tower face (4.5 and 9 times closer than the best found), and on the wall beside only when already touching. They give nothing on the canyon (an open street), the angle slice and the two airspeed slices. With no load-factor cap the bound is looser than in the first pass (it now credits the full stall-limited lift, 9.6 g at 66 m/s), which moved the dive markers from 9 to 11 m down to 5 to 6 m. The looseness sources are named under "The outer bound" below.

<!-- WILD -->
**In the wild.** `regimes wild 200` flies the 200 hostile-pilot harness episodes under the deployed gate (4 m margin) and classifies each of its 22100 takeovers by the binding cause at the moment it rejected the pilot, judged as the gate judges it (all 200 episodes have takeovers; none crashed). The closest passes dip below 4 m because the gate checks clearance every 8 frames and the flight is sampled every 20 ms:

| Regime | Takeovers | Episodes | Closest pass |
|---|---|---|---|
| 01-terrain-roof-below | 16400 | 200 | 3.7 m (episode 91, t = 50.6 s) |
| 02-wall-beside | 1892 | 132 | 3.5 m (episode 50, t = 11.2 s) |
| 03-canyon | 2975 | 199 | 4.0 m (episode 71, t = 36.5 s) |
| 04-wall-ahead | 298 | 91 | 3.9 m (episode 59, t = 47.1 s) |
| 05-rising-terrain | 263 | 58 | 4.0 m (episode 80, t = 32.0 s) |
| none (an unbudgeted check from that state verifies an escape; the gate's budgeted, round-robin check did not) | 272 | 116 | – |
<!-- /WILD -->

## The markers

Each slice fixes every state variable but one, at typical values, and moves that one toward the obstacle. Along it:

- **Proven safe (contact)**, green: the closest state from which one of the gate's own six escapes (straight; left and right turns at 30° and 40°; street), flown by exact rollout on a fork of the JSBSim c172p (`JsbExact`, bit-exact), keeps positive airframe clearance at every JSBSim frame (1/128 s) and reaches one of the gate's terminal sets with no vertical margin, within 16 s. The rollout is exact and contact is checked at every frame; the terminal sets (a climbing ray above the map, or a steady climbing helix over clear ground) are checked numerically on the settled rollout. So this marker is verified by exact simulation plus numerical terminal checks, not formally proved, and it leans on terminal sets, which the objective leaves to the proof.
- **Best found (contact)**, orange: the closest state from which a much richer search finds an escape the same way. The search flies 318 escape-law variants (straight, or a turn either way at 15° to 62° bank; minimum pull-up time 0 to 3 s; three gain sets: the gate's, one with n ≤ 3.8, α ≤ 0.26 and a stiffer flight-path loop, and one with n ≤ 6, α ≤ 0.27; climb speed 34 or 40 m/s; plus the street escape), then 160 iterations of local search over one to three piecewise-constant fly-by-wire segments (load factor 0 to 6 g, bank target ±80°, full throttle, 0.15 to 3 s each) flown before switching to one of the six best law variants. Horizon 24 s, no load-factor or α ceiling beyond the fly-by-wire's own α protection (0.26 rad). The gate's own escapes count as part of the family. Empirical: a failed search proves nothing, and on the canyon slice the search's successes are not monotone in height.
- **Proven unsafe**, red: the farthest state from which no control can avoid contact, by a sound outer bound that is optimistic for the aircraft (next section).
- **Gate accepts**, blue: the deployed gate's own verdict (`Gate::new`'s search: the same six escapes with its 4 m margin, clearance checked every 8 frames, terminal sets with a 4 m vertical margin). A property of the filter, shown so the margin's share of each gap is visible.

Markers are bisected to 0.5 (m, m/s or degrees) from a 41-point grid. "Closest" means the grid point closest to danger where the predicate holds, refined against its neighbour, so an isolated accepted point counts; where a predicate is not monotone along a slice, the folder says so.

**Contact and the airframe.** Contact is `World::airframe_clearance ≤ 0`: the gate's airframe model, a 4.5 m sphere at the centre of gravity plus a 0.8 m-radius capsule along the drawn wing line, banked with the aircraft, against the exact terrain triangles and building boxes, checked at every JSBSim frame. The objective has since fixed its own contact shape: the convex hull of the c172p's JSBSim and FlightGear contact points, swept between frames (`docs/safety-objective.md`). The gate's envelope is much fatter than that hull below and around the fuselage (on a dive, "0.01 m" puts the centre of gravity 4.5 m above the floor) and likely encloses it at the wingtips too, though that is not checked point by point; so the contact markers here are, if anything, conservative. The map edge follows the objective: leaving the map is not an escape, and a climbing ray must clear the edge profile continued beyond the map. Rerunning every slice under that rule changed no marker or cause (`regimes offmap` lists, per marker, which certificates run past the edge). The gate itself, and the zero-margin gate in the demos, still count leaving the map as clear.

**Binding causes.** At every grid point each of the gate's escapes, judged at contact, is classified (`regimes::classify`): hit the ground, terrain rising ahead, a roof below, a wall beside (more than 45° off the track) or a wall ahead; or, with no hit, the terminal test that failed last (still pulling up, climb not settled, ray blocked by a building or by terrain, helix blocked). A cell marked `n` or `α` had the escape law's load-factor or α cap binding on more than 15% of its frames: limits of the gate's escape law, not of safety. The plots mark where the binding cause of the escape that got farthest changes along the slice.

## The outer bound

`regimes::outer_bound` proves that **no point mass inside this envelope** avoids the actual city geometry (terrain triangles and building boxes):

1. Lift is perpendicular to the velocity, with magnitude at most `0.0036 · q̄ · g` per unit mass: the plant's stall, with no load-factor cap. The 0.0036 /Pa is 15% above the largest perpendicular specific force per unit dynamic pressure the plant produced in `regimes calib` (full-aft-stick pulls from 24 to 66 m/s at idle and full power: 0.00314 /Pa, including thrust's perpendicular component and the first-frame start-up transient). It is a measured property of the plant, not a proof about it.
2. Thrust is along the velocity and at most 7.1 m/s² per unit mass: an ideal actuator disk of the 1.9 m propeller at 200 hp gives at most 5.4 kN static, over the lightest possible mass (empty weight plus pilot, 762 kg). The plant's measured thrust minus drag never exceeded 4.2 m/s².
3. Drag is against the velocity and at most `0.4 · q̄ · S / 762 kg` (the plant's measured worst: 0.19).
4. No other forces than gravity. Controls act instantly: no pitch, roll or engine transients, any bank at once.
5. The aircraft is a point (no wings, no body radius).

From these, `outer_bound` integrates (10 ms steps) sound bounds on the speed interval `[v_lo, v_hi]`, the angle θ between the velocity and its initial direction e (growing at most at `max lift / v + g / v_lo`), the progress along e (`s_lo`, `s_hi`), the distance from the axis (`r⊥ ≤ ∫ v_hi sin θ`), and an altitude ceiling `z_hi` (climb acceleration at most lift + thrust − g). At time t every trajectory lies in the tube {p0 + s e + w : s ∈ [s_lo, s_hi], |w| ≤ r⊥} below `z_hi`. Two tests, every 50 ms of bound time up to 8 s:

- **tube**: the whole tube below the ceiling lies inside the solid;
- **crossing**: every trajectory crosses the plane s = D by the time `s_lo` reaches D, within r⊥ of the axis and below the ceiling's maximum so far; if that disk lies inside the solid, the aircraft hits the solid there.

"Inside the solid" is checked conservatively: the region is tiled with 1.5 m cubes, and every cube that might meet it must lie below the lowest solid height over its footprint (the lowest terrain-grid vertex of every triangle touching it, or the roof of a box covering the whole footprint).

The bound is loose in two ways that matter: it lets the whole lift vector point in any direction at once (a level turn really needs part of it to hold the aircraft up), and it credits gravity's turn rate `g / v` in every direction. It also ignores the airframe's size. So it proves unsafety only near an obstacle; how near is in each folder.

## Demos

Every folder lists, per slice, one-line GUI commands (run them from `flight/`) with outcomes measured headless on the same deterministic simulation. The GUI checks the gate's escapes at full horizon on several threads, with no wall-clock cap (`--time-cap 0`, the default since #23, is kept in the commands for clarity); `regimes demo` reaches the same verdicts on one thread (`CHECK_THREADS = 1`; the verdict does not depend on the thread count), so the GUI flies the same frames:

- the **closest safe call**: the proven-safe state, moved back along its velocity by a lead-in of up to 3 s (as long as that path is clear), flown with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle. The gate runs with its margin set to zero and clearance checked at every frame (`--margin 0 --check-every 1`): the filter that matches the contact objective. It takes over when its check fails and hands back once the pilot's command verifies again. The HUD shows the current and minimum airframe clearance;
- its **just-barely-unsafe twin**: the first start closer than the marker (0.5, 1, 2, 4, … units in) that crashes under the same zero-margin gate with no lead-in. No escape verifies there, so the gate commits blind to the escape that got farthest;
- the **deployed gate** (4 m margin) from its own acceptance marker, for comparison;
- the **closest proven-unsafe call**, with the filter on and off, plus each of the gate's escapes flown from it at contact: all of them touch.

`--start x,y,z,v,γ°,heading°,bank°,throttle` (heading counter-clockwise from east, bank positive left wing down), `--lead S`, `--label TEXT`, `--margin M`, `--check-every N` and the HUD's minimum-clearance row were added for these demos.

## How to reproduce

From `flight/` (after `(cd .. && lake build libcityjsb)`):

```sh
cargo run --release --no-default-features --features jsb --bin regimes -- calib       # the plant's maxima against the outer bound's envelope
cargo run --release --no-default-features --features jsb --bin regimes -- run         # every slice: grid, markers, causes -> */<slice>.json, */<slice>.svg
cargo run --release --no-default-features --features jsb --bin regimes -- demo        # demo flights headless -> */<slice>-demos.md, */<slice>-shots.sh
cargo run --release --no-default-features --features jsb --bin regimes -- index       # the table above
cargo run --release --no-default-features --features jsb --bin regimes -- wild 200    # takeovers in the 200 harness episodes, by regime -> wild.csv
../docs/boundary-regimes/shots.sh                                                     # screenshots (Metal), from any directory
```

`run` and `demo` take slice-name prefixes (`run 04 05`) and `--threads N` (default 6). Everything is deterministic: the searches are seeded by the slice parameter, and runs are headless with no wall-clock caps. `regimes probe KEY` prints a slice's grid with every escape's cause, `regimes offmap` the certificates at each proven-safe marker; `regimes find`, `near X0 X1 Y0 Y1` and `canyons` are the geometry searches used to pick the locations. The slices are defined in `flight/src/bin/regimes.rs` (`slices()`); the verdicts, causes, richer search, outer bound and demo flights in `flight/src/regimes.rs`. `envfilter::rollout_cfg` is the gate's own rollout with a settable margin, horizon, check spacing and fly-by-wire prefix; `RollCfg::filter()` is exactly the gate's check (with the default margin, the 24-episode `crashes` run and `esclab` outputs are unchanged).
