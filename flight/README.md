# Backup-CBF City Flight

Fly a light aircraft through a city with the keyboard: a procedural grid city
or downtown San Francisco, built from real data. A backup control barrier
function (bCBF) safety filter stays silent far from obstacles, takes over near
buildings and terrain, then hands control back. Space toggles the filter, so
you can fly the same crash attempt with and without it.

Native Rust: the simulation, filter and harness are a GUI-free library; the
demo renders with macroquad, with terrain and buildings held in static GPU
buffers through raw miniquad (about 120 fps at 2880×1800 with 4× MSAA on an M3 Max).

## Run

```sh
cd flight
cargo run --release                                   # the demo (grid city)
cargo run --release -- --map sf                       # the demo in San Francisco
cargo run --release --no-default-features --bin harness              # acceptance harness (200 episodes)
cargo run --release --no-default-features --bin harness -- --map sf  # the same in San Francisco
cargo run --release --no-default-features --bin harness -- --extended  # + Phase 2 / Phase 3 rows
cargo run --release --no-default-features --bin harness -- --coverage  # street coverage only
```

Harness flags: `[episodes] [--map grid|sf] [--threads N] [--quick] [--extended] [--coverage] [--only NAME]`. `--quick`
shortens the kamikaze endurance runs from 300 s to 60 s. The harness exits
non-zero if any acceptance check fails.

Demo flags (handy for screenshots): `--map grid|sf`, `--scenario 1..4`,
`--at x,y,agl,heading` (start anywhere, map metres and degrees), `--off`,
`--kamikaze`, `--paths`, `--cam 0..3`, `--shot out.png --frames N`.

## Maps

- **Grid city** (default): procedural, 2,145 boxes on a street grid, with a
  ridge and a mountain rim.
- **San Francisco** (`--map sf`, or Tab in flight): the 6 km square from
  Alamo Square to Yerba Buena Island and from Mission Dolores to Pier 39.
  About 41,000 buildings come from DataSF footprints and their LiDAR peak
  heights, plus OpenStreetMap for everything built after the 2010 LiDAR
  (Salesforce Tower is 326 m). Terrain is USGS 3DEP, and the Bay Bridge West
  Span and the elevated freeways are included. Buildings are convex prisms
  checked exactly, like the grid city's boxes. All of it is in
  `data/sf/sf_world.bin`, compiled into the binary, so nothing downloads at
  run time. `data/sf/README.md` covers the sources, the frame, and how every
  step only ever enlarges obstacles.
  - **Aerial photo (optional):** with `data/sf/sf_naip.jpg` present
    (`python3 data/sf/fetch_naip.py`, USDA NAIP, public domain), the ground
    and the roofs of low buildings show the real city. Without it, streets
    are painted from OpenStreetMap.
  - **Bay Bridge:** drawn as the bridge, with its collision curtain shown as
    a faint glass envelope, because the filter keeps you outside that
    envelope.

## Controls

| Key | Action |
|---|---|
| W/S or ↑/↓ | pitch (stick forward = nose down; `I` inverts) |
| A/D or ←/→ | roll. Release to hold flight path and bank (fly-by-wire) |
| Q / E | throttle down / up |
| Space | safety filter on/off |
| F | filter: P1 blend+commit → P2 closed-form → permissive |
| G | Phase 3 robust margins for model error, on/off (works with any filter) |
| B | escape paths (green valid, red invalid, yellow = committed plan) |
| N | wind: 7 m/s steady + bounded gusts (the filter knows the envelope) |
| M | model error: a weaker, slower aircraft than the filter assumes |
| C | camera: chase, cockpit, orbit, overhead |
| 1–4 | scenarios: tower run (Salesforce run in SF), dive, ridge (Nob Hill in SF), slow and low |
| K | kamikaze autopilot |
| T | run the 200-episode harness in the background |
| Tab | switch map: grid city ↔ San Francisco |
| R / H | reset / help |

The trail is coloured by what the filter was doing: blue = pilot in control,
orange = blending, red = committed escape, white = filter off.

## How it works

**Clearance checks** (`world.rs`). **Buildings are checked exactly:** each
predicted path segment's distance to every nearby building must exceed the
aircraft's 4.5 m radius plus 1 m. Buildings are found through a bucket grid.
Boxes use exact segment-to-box distance. San Francisco's convex prisms use
exact segment-to-prism distance (`seg_prism_dist2`): along the segment, the
squared distance is a quadratic in each interval between the parameters where
the ground track crosses an edge line or an edge-end perpendicular, or the
height crosses the floor or roof. Unit tests check it against dense sampling
and against the box distance. New plans need another 0.5 m plus 0.5 m of overall slack, so
a verified plan can pass about 2 m from a wall. **Terrain** (piecewise-linear
over a 20 m grid, the same triangles the renderer draws) uses a 2.5 m
max-height map dilated sideways by 7.5 m and raised by 6.5 m. Each path
segment is checked against every terrain cell it crosses, at the segment's
own height inside that cell. Both checks cover the continuous path, not just
samples. Off-map counts as a wall.

**Aircraft** (`model.rs`). A point-mass 3D Dubins-style model with speed
dynamics: thrust and drag, lift limited by airspeed (so stall emerges on its
own), and first-order lags on load factor, roll rate and throttle. The numbers
are light-sport: stall 25 m/s, cruise 50 m/s. Physics runs at 100 Hz with RK4
and the filter at 50 Hz. The predictor uses the same equations.

**Escapes** (`escape.rs`). Ten Auto-GCAS-style maneuvers, all at full power,
with the climb angle from a speed-hold through pitch (a slow aircraft trades
less energy) and bank limited to keep the load factor under 85% of the stall
limit. When an escape begins it fixes a path over the ground: a straight climb
line for 0, 3, 6, 10 or 15 s along the nearest street direction (if the track
is within 25° of it), then an orbit left or right around a fixed point. It
follows that path with a crab angle into the measured wind, so a gust causes
a small, bounded wobble instead of a drift that grows with time. An escape
ends once the predicted flight has stayed settled on its orbit for 3 s
(radius, course, bank, roll rate, speed and climb all steady), climbing faster
than the worst downdraft, with the whole circle clear at the current height. From then on
it stays near the same ground circle at ever greater height, so it is safe
forever. `h_i(x)` is the worst clearance along escape `i` (−∞ if it doesn't
settle within 40 s of its pull-up); `h(x) = max_i h_i(x)`.

**Phase 1 filter** (`filter.rs`, default). Each tick it asks how long the
pilot could keep the current command and still escape. If the answer is at
least 1 s, it leaves the pilot alone. Under 1 s it blends 35% toward the best
escape, under 0.4 s 70%, and under 0.1 s fully. This is a time margin, not a
distance margin: in a street canyon the walls are always close even when
escape is easy, so a distance margin blends constantly. The blended command,
held for 0.25 s and followed by an escape, must itself verify; if it does, it
becomes the new committed plan. Otherwise it keeps
flying the plan committed at the last tick that passed (gatekeeper). New plans
must clear a map one cell wider (10 m) by 1 m. Every tick it re-checks the
committed plan against the 7.5 m map and asserts that a verified escape exists.

**Phase 2 filter** (after van Wijk et al.). It interpolates
`u = (1−β) u_pilot + β u_backup` with the smallest β satisfying
`ḣ ≥ −α (h − 12 m)`, a scalar inequality solved in closed form. ḣ comes from
finite differences of a bilinear (smooth) version of `h`. The Phase 1 check
and committed fallback still run underneath as a safety net.

**Permissive mode** (pure gatekeeper). It passes the pilot's command whenever
"pilot for one tick, then the best escape" verifies, and otherwise flies the
committed escape. It's the most permissive option, but it intervenes abruptly.

**Wind.** With full state knowledge the wind is measured (ground velocity
minus air velocity). The filter predicts with the steady wind and is given a
gust envelope: at most 2.5 m/s per horizontal axis and 0.5 m/s vertically,
which the simulator's gusts respect. Margins follow from it:
- Laterally: gust × 1.5 s of path-following error, plus gust × the time the
  pilot's (uncorrected) command is held. New plans pay the tracking term
  twice, so a re-check after a gust still passes.
- Vertically: the predicted path is checked lowered by the worst downdraft so
  far.

In calm air all of these margins are zero.

**Phase 3 robustness (model error)**. The predictor assumes the worst-case
weaker aircraft, and the required clearance grows along the prediction:
1 m/s laterally and 0.25 m/s vertically.

The filter only ever changes the commands sent to the aircraft. Collisions are
always checked against the true geometry (an aircraft sphere of radius 4.5 m
against boxes and terrain), never against the inflated map.

## Results (`harness 200 --extended`, M3 Max)

| Config | Crashes | Invariant violations | Min true clearance | Filter active | Commit | ms / tick |
|---|---|---|---|---|---|---|
| **P1 filter ON (calm)** | **0 / 200** | **0** | 2.0 m | 64% | 0.6% | 2.2 |
| filter OFF | 199 / 200 | – | crash | – | – | – |
| **P1 + gusty wind** | **0 / 199** | **0** | 10.9 m | 68% | 2.5% | 2.2 |
| OFF + gusty wind | 199 / 200 | – | crash | – | – | – |
| P1 + model error | 1 / 200 | 7 eps | crash | 66% | 1.2% | 2.1 |
| P2 closed-form | 0 / 200 | 0 | 2.0 m | 51% | 0.1% | 2.4 |
| Permissive | 0 / 200 | 0 | 2.0 m | 32% | 32% | 0.8 |
| P1+P3 + model error | 0 / 198 | 0 | 2.6 m | 69% | 0.9% | 2.5 |
| P1 + wind + model error | 1 / 199 | 1 ep | crash | 69% | 3.4% | 2.3 |
| P1+P3 + wind + model error | 0 / 195 | 0 | 12.4 m | 72% | 1.8% | 2.4 |

Every configuration uses the same 200 random starts. With the filter on, a
start counts only if it has a verified escape under that configuration (no
filter can rescue an aircraft that starts outside its safe set). That
excludes 1 start in wind, and up to 5 with Phase 3's extra margins.

Minimum true clearance is the gap between the aircraft's 4.5 m sphere and
the nearest building or terrain surface. The 2.0 m floor is exactly the
margin new plans must keep (1 m + 0.5 m + 0.5 m slack), which shows the
predictor and the aircraft agree.

**San Francisco** (`harness 200 --quick --map sf`):

| Config | Crashes | Invariant violations | Min true clearance | Filter active | ms / tick |
|---|---|---|---|---|---|
| **P1 filter ON** | **0 / 200** | **0** | 2.0 m | 66% | 2.35 |
| filter OFF | 200 / 200 | – | crash | – | – |
| P1 ON + gusty wind | 0 / 195 | 2 eps | 8.7 m | 70% | 2.31 |
| P1 ON + model error | 5 / 200 | 13 eps | crash | 67% | 2.35 |

- **Kamikaze:** survives all four SF scenarios (minimum clearance 2.2 to 2.3 m).
- **Street coverage:** 93.6% of street states have a verified escape, and
  77.4% of those below rooftop height. The grid city's are 98% and 93%: SF has
  narrower canyons under taller walls.
- **Gusty wind fails acceptance here:** two episodes briefly lost their
  verified escape, though neither crashed. The grid city shows none, so this
  is still open.

**Flying between buildings.** Of 2,000 random states on street centrelines
20–90 m above the ground, 93% of those below rooftop height have a verified
escape, even with the nose 4° off the street axis. (It was 5.9% with the
original margins and four escapes.) A street-following autopilot holding
40 m on six streets spends this share of its time below rooftops:

| Filter | Below rooftops | Mean intervention |
|---|---|---|
| off | 44.4% | – |
| P1 (time margin) | 40.3% | 0.11 |
| Permissive | 42.2% | 0.05 |
| P2 | 18.4% | 0.26 |

P2 keeps the barrier above a 12 m floor, which is conservative in streets.

Kamikaze autopilot with the filter on survives 300 s in all four scenarios
(minimum clearance 2.0 to 2.1 m). Straight flight well above obstacles shows
0 blended ticks out of 8,000. Episodes are 60 s from random starts inside the
safe set. Pilots are a nose-down-biased random stick, with a kamikaze
autopilot in a quarter of the episodes. Every configuration uses the same seeds.

Timing: the `ms max` column in the harness (~100 ms) comes from 16 threads
sharing the CPU. Single-threaded (`--threads 1`) P1 averages 1.6 ms and its
worst tick is 7 ms in calm air and 14 ms in wind, inside the 20 ms filter period.

## The trusted core

The safety claim rests only on:
1. **Every command sent to the aircraft is verified first:** the command for
   a moment, then an escape whose whole path clears the inflated map and
   reaches the terminal helix.
2. **If that check fails, the aircraft flies the last verified plan**
   (gatekeeper), so a verified escape always exists.
3. **The clearance checks are conservative:** exact segment-to-box and
   segment-to-convex-prism distance for buildings; a dilated, swept height
   map for terrain.
4. **The predictor uses the same equations as the aircraft.**
5. **Wind is the steady wind plus gusts within the stated envelope.**

The blending rules (P1, P2, permissive), the GUI and the autopilots only
choose which candidate command to try. They sit outside the trusted core, so
they can be tuned for feel without touching what needs certifying.

## What is assumed / trusted

- **The guarantee holds only under the nominal model with full state
  knowledge.** It rests on the predictor matching the plant. Here they share
  equations; RK4 at 0.1 s vs 0.01 s differs by millimetres, and by about 1 m on
  the pull-up escapes. The 1 m acceptance margin and the one-cell (2.5 m)
  wider acceptance map absorb that and the sampling-phase effects.
- **Wind is covered** up to the gust envelope (2.5 m/s per horizontal axis,
  0.5 m/s vertical) with the steady wind known: 0 crashes in gusty wind.
  Before escapes followed ground paths and the predictor used the measured
  wind, the same test crashed 89 times in 200.
- **Model error (M) is not covered:** a weaker aircraft than the filter
  assumes crashed 1/200 times. Phase 3 margins (G) cover it: 0/198.
- **San Francisco's geometry is only as good as its data:** 2010 LiDAR plus
  OpenStreetMap, and conservative estimates for the bridge and freeways (see
  `data/sf/README.md`). Each footprint is one prism at its highest LiDAR
  return, so tapered towers such as the Transamerica Pyramid are boxes:
  safe, but blockier than the real building.
- The safety argument is engineering-level and tested, not machine-checked.
  The trusted core above is the part to prove formally.
