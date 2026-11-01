# Backup-CBF City Flight

Fly a light aircraft through a city with the keyboard: a procedural grid city
or San Francisco from downtown to Ocean Beach and the Golden Gate, built from
real data. A backup control barrier
function (bCBF) safety filter stays silent far from obstacles, takes over near
buildings and terrain, then hands control back. Space toggles the filter, so
you can fly the same crash attempt with and without it.

Native Rust: the simulation, filter and harness are a GUI-free library; the
demo renders with macroquad, with terrain and buildings held in static GPU
buffers through raw miniquad (about 120 fps at 2880×1800 with 4× MSAA on an M3 Max, classic renderer).

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

Demo flags (handy for screenshots): `--map grid|sf`, `--scenario 1..5` (1..4 in San Francisco),
`--at x,y,agl,heading` (start anywhere, map metres and degrees), `--off`, `--kamikaze`, `--showcase`,
`--paths`, `--cam 0..4`, `--shot out.png --frames N`.

## Maps

- **Grid city** (default): procedural, 2,145 boxes on a street grid, with a
  ridge and a mountain rim.
- **San Francisco** (`--map sf`, or Tab in flight): a 12.6 × 9.4 km
  rectangle from Ocean Beach and Lands End to Yerba Buena Island, and from
  Noe Valley and Twin Peaks to the Golden Gate: downtown, the Richmond, the
  Sunset north of Taraval, Golden Gate Park, the Presidio and the Golden Gate
  Bridge. About 132,000 building pieces come from DataSF footprints and their
  LiDAR peak heights, plus OpenStreetMap for everything built after the 2010
  LiDAR (Salesforce Tower is 326 m; Sutro Tower stands 298 m on its 254 m
  hill). Terrain is USGS 3DEP, and the Bay Bridge West Span and the elevated
  freeways are included. Buildings are convex prisms
  checked exactly, like the grid city's boxes. All of it is in
  `data/sf/sf_world.bin`, compiled into the binary, so nothing downloads at
  run time. `data/sf/README.md` covers the sources, the frame, and how every
  step only ever enlarges obstacles.
  - **Aerial photo:** with `data/sf/sf_naip.jpg` (USDA NAIP, public
    domain, 1 m per pixel), the ground shows the real city, scaled from photo
    brightness to albedo because the renderer lights it again. Without it, streets are
    painted from OpenStreetMap.
  - **Bay Area backdrop:** with `data/sf/backdrop.jpg`, the 80 km around the
    map is drawn with real terrain and imagery (Mt Tam, the Marin Headlands,
    the East Bay hills). It's visual only; you fly inside the rectangle.
  - **Offline:** both load from disk at start, so the demo needs no network.
    `data/sf/README.md` explains how to re-download them.
  - **Bay Bridge and freeways:** drawn as the bridge (towers, deck, cables)
    and as decks on pillars. Their collision curtains are conservative (no
    flying under them) and not drawn.
  - **Golden Gate Bridge:** inside the map, and you can fly under it.
    `src/golden_gate.rs` describes it once; the renderer draws it from that
    and `world.rs` builds its obstacles from the same numbers, so everything
    drawn lies inside an obstacle. The towers are OpenStreetMap's tower parts
    (both towers agree to 5 cm); the deck, stiffening truss, main cables,
    suspenders, anchorage pylons, the Fort Point arch and the San Francisco
    approach follow the published dimensions (1,280 m main span, 343 m side
    spans, 227 m towers, 67 m clearance). Obstacles: the towers and piers,
    the deck in 10 m slices up to its railings, a thin wall in each cable
    plane from the roadway up past the main cable (cable plus suspenders),
    and the pylons, the arch (filled to the ground) and the approach piers.
    The space under the deck between the towers is open.
  - **Renderers:** the photoreal renderer draws San Francisco with the grid
    city's materials (`src/sfscene.rs`): a facade per footprint edge, light
    stone and stucco below the towers, pastel rowhouses. The classic renderer
    draws plain footprints on the OpenStreetMap-painted ground.

## Photoreal renderer (Metal)

On macOS the demo runs on Metal and starts in a photoreal renderer; `--classic`
(or `V`) selects the original renderer and `--gl` runs it on OpenGL. `V` cycles
classic → photoreal → ray traced. Screenshots: `--shot out.png --frames N` prints
wall-clock fps, GPU and CPU ms per frame; `shots/take.sh <tag> [flags]` takes the
standard four views into `shots/`.

- Linear-light HDR: 4× MSAA RGBA16F scene, ACES tonemap, auto exposure.
- Single-scattering sky (sky-view LUT), sun disc, per-pixel aerial perspective,
  SH sky ambient; GGX materials with CC0 ambientCG textures (`assets/textures`,
  `fetch.py`, `LICENSES.md`; procedural stand-ins without them); facades with
  interior-mapped rooms behind the glass, shopfronts, grime, rooftop units.
- Four-cascade sun shadow maps, SSAO on the ambient term, baked contact occlusion.
- Half-res volumetric pass: height fog with shadowed light shafts, a cloud layer
  with cloud shadows, landing/nav/strobe lights and dusk street lamps.
- Cessna 172-style aircraft with animated ailerons, elevator, rudder and propeller
  (control surfaces from `JsbPlant.surf` with `--jsb`); a made-up registration.
- Post: depth of field with hexagonal or round bokeh and tilt-shift, bloom, and a
  footage mode (lens distortion, chromatic aberration, motion blur, grade, grain,
  vignette, shake, rolling-shutter propeller).
- Ray traced (`--rt`): Metal hardware ray tracing for sun shadows, one diffuse
  bounce and reflections (wet streets), MetalFX temporal upscaling from half
  resolution with a bilateral filter, or the MetalFX temporal denoiser (`U`).

| Key / flag | Action |
|---|---|
| `V` / `--classic`, `--rt`, `--gl` | renderer |
| `,` `.` `;` `'` / `--sun el,az` | sun elevation and azimuth |
| `P` / `--preset 0..3` | weather: clear, hazy, valley fog, dusk |
| `[` `]` `-` `=` `9` `0` / `--fog d,h,g` | fog density, height falloff, anisotropy |
| `O` / `--lens 0..4` | lens: 24 mm f/2.8, 200 mm f/2 hex bokeh, 50 mm f/0.95, tilt-shift, cinematic 50 mm f/4 |
| `6` / `--cinematic` | cinematic preset: fly-by camera (`--cam 4`), clear weather, 50 mm f/4 focused on the aircraft |
| `Z` `X`, `N` `J` | f-stop, focal length |
| `L` / `--footage` | footage look |
| `U` / `--rt-denoiser`, `--rt-scale s` | MetalFX denoiser, ray-traced internal scale |

Measured on an M4 Max at 2880×1800 (GPU time per frame): photoreal 8–9 ms,
footage mode about 9 ms, ray traced 7.5–8.5 ms (MetalFX denoiser 16–20 ms).

Trusted beyond the rest of this README: `vendor/miniquad` is miniquad 0.4.11
with its Metal backend extended (diff it against the crates.io source); the
ray-traced mode talks to Metal and MetalFX through unchecked Objective-C
messages (`src/rt.rs`).

## JSBSim plant (`--jsb`)

With the `jsb` feature, `--jsb` flies JSBSim's c172p instead of the point-mass model, through the bit-exact
Lean port `JsbExact` (`libcityjsb`, built from the repo root). A fly-by-wire loop in `src/jsb.rs` turns the
load-factor / roll-rate / throttle commands into elevator, aileron, rudder and throttle at 128 Hz, with
angle-of-attack protection. The filter still predicts with the point-mass model, so this measures it under
model mismatch; wind and the `M` mismatch toggle do not affect the JSBSim aircraft.

```sh
(cd .. && lake build libcityjsb)
cargo run --release --features jsb -- --jsb                                        # the demo
cargo run --release --no-default-features --features jsb --bin harness -- --jsb    # harness
cargo run --release --no-default-features --features jsb --bin jsbtune             # fly-by-wire tracking
```

### Exact-rollout gatekeeper (`--env gate`)

Proof status (nothing about this filter is proved yet; what is exact and what is numerical): `../docs/gate-proof-status.md`.

`src/envfilter.rs` predicts with the plant itself: each check forks the JSBSim aircraft and flies an escape
law on the copy, frame by frame, so a committed escape flies exactly the frames that were checked.

- **Escape law.** A longitudinal law ported from a synthesised one (`Ci/cegis/Law.lean`, not in this
  repository; full throttle, flight-path loop over a load factor ≤ 3.5 and α ≤ 0.24, trim feedforward,
  pitch-rate feedforward), plus an α integral, load factor divided by cos φ in a bank, roll PI-D, a
  sideslip-nulling rudder and a heading hold. `--law lawfirst` flies the α-command law of `Ci/lawfirst`
  (also not in this repository) instead; `--law cegis1` the earlier cegis law.
- **Escapes.** A straight climb-out, and climbing turns left and right at 30° and 40° bank, after a pull-up
  of at least 1.5 s. A street escape captures the nearest street axis when the track is within 25° of one
  (bank ≤ 20° while capturing), climbs wings level along it, and every 0.25 s looks for a 40° helix whose
  predicted annulus is clear at its height (10 m margin, left side first); then it rolls in. It never
  verifies through its ray ending from below the rooftops: a ray along a street axis must clear the
  ~900 m rim of the map. `--escapes 5` drops the street escape, `3` also the 40° turns.
- **Airframe.** Path samples and the crash check use `World::airframe_clearance`: the 4.5 m sphere plus the
  wing, a 0.8 m capsule around the line through both wingtips (11 m span, as `c172.rs` draws it), placed by
  the bank, heading, flight path and drawn angle of attack. Buildings are exact (segment to box); terrain
  under the wing is sampled every 0.25 m outboard of 4 m span. The tail trails inside the volume the
  sphere has just swept, so it is not checked. The point-mass filter and its crash check keep the sphere.
- **Terminal sets**, checked on the settled rollout (from 6 s on, within 16 s): the straight escape needs a
  climbing ray (80% of the settled gradient, in a corridor widening 2% of distance) that clears every raw
  cell until it is above the map's top or off the map. A turn needs a steady helix (radius and centre agree
  to 10% across two 2 s windows, climbing ≥ 1 m/s) whose ground annulus, widened for that drift, is clear
  at the current height. Every path sample keeps 4 m of true clearance.
- **Scheduling.** Each 20 ms tick checks the pilot's next tick followed by the last escape that verified;
  the pilot keeps control if it verifies. Otherwise the filter commits to the escape verified on the
  previous tick, and committed ticks try the escapes round robin. A deterministic budget of 2,200 JSBSim
  frames per tick (15 ms at the measured 6.7 µs per checked frame) caps the work. The GUI also stops checks
  at a 15 ms wall-clock deadline (`--time-cap MS`, 0 = off): a check cut short fails, so the filter keeps
  its verified escape. Headless runs stay deterministic unless given `--time-cap`.

```sh
cargo run --release --features jsb -- --env gate                                    # fly it (B: escapes)
cargo run --release --features jsb -- --env gate --episode 59                       # replay an episode
cargo run --release --features jsb -- --env gate --showcase --paths                # Tower gap showcase
cargo run --release --no-default-features --features jsb --bin crashes -- /tmp/s 100 --env gate --scenario 5
cargo run --release --no-default-features --features jsb --bin crashes -- /tmp/c 200 --env gate
cargo run --release --no-default-features --features jsb --bin adversary -- /tmp/a gate 200
cargo run --release --no-default-features --features jsb --bin esclab -- trace     # escape-law traces
```

With `B`, the latest rollout is drawn green (verified) or red, and the committed escape yellow; turning
escapes end in their terminal helix.

`crashes` on the 200 hostile episodes plus the 4 kamikaze scenarios (JSBSim plant). A start is verified when
the filter accepts the pilot's first tick.

| Filter | Crashes / 200 (verified starts) | Unverified starts | Kamikaze crashes | Ticks committed |
|---|---|---|---|---|
| P1 point-mass filter (`--jsb`) | 27 | – | 2 / 4 | – |
| gate, 3 escapes (`--escapes 3`) | 2 (0 of 195) | 5 | 1 / 4 (Ridge, unverified) | 31.7% |
| gate, `--law lawfirst` | 1 (0 of 198) | 2 | 0 / 4 | 30.7% |
| gate, 5 escapes, body sphere only (before the wing check) | 0 (0 of 198) | 2 | 0 / 4 | 29.5% |
| **gate (default: wing check, 6 escapes)** | **0 (0 of 198)** | 2 | **0 / 5** (incl. Tower gap) | 28.9% |

Every row before the last checks and crashes on the body sphere only; the last checks and crashes on sphere
plus wing. Single-threaded check cost (`--threads 1`, 20 episodes + 5 kamikaze, thread CPU per 20 ms tick):
median 6.4 ms, mean 7.6 ms, p99 19.9 ms, at most 2,200 JSBSim frames. That was measured with the machine
loaded by other jobs (load average about 16 on 14 cores), where a JSBSim frame costs 7-9 µs instead of 6.7;
an A/B of the old sphere-only and the new airframe clearance inside rollouts showed no measurable
difference per checked frame.

### Tower gap (`5`, `--scenario 5`, `Y` / `--showcase`)

The 28 m street `x = -120 m`, flown north at 88 m above the street, 45 m/s. The spawn sits between the
261 m and 292 m towers of block row 9; past the avenue `y = 0` the street runs between the 235 m and 352 m
towers of row 10 (the 352 m one backs onto the 450 m tallest tower), then lower blocks and a park. The
street escape verifies along this street from the spawn on (`esclab gaps`, `esclab approach -120 -90 90
300`); the spawn is searched so the active filter verifies an escape there. The showcase pilot holds the
centreline through both gaps, banks hard right into the 352 m tower at `y = 45 m` for 5 s, then levels off
and climbs. The filter lets the threading through untouched, commits to the street escape at 15° of bank
(yellow path with `B`), rolls wings level and climbs out along the street; the second attempt is caught the
same way.

| Tower gap run (`crashes --scenario 5`) | Crashes | Verified starts | Ticks committed |
|---|---|---|---|
| 50 hostile + 50 kamikaze pilots | 0 / 100 | 100 / 100 | 31.3% |
| showcase pilot (60 s) | 0 | yes | 208 of 3,000 |

`adversary -- /tmp/a gate 200`: 0 crashes in 2,640 gap-guided flights from 200 verified starts. An
unlimited budget (`--budget 100000`) commits 29.5% of ticks too: the interventions are what the escapes
require, not budget starvation.

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
| M | model mismatch: wind + gusts (the filter knows the envelope), and a weaker, slower aircraft |
| C | camera: chase, cockpit, orbit, overhead, fly-by |
| 1–5 | scenarios: tower run (Salesforce run in SF), dive, ridge (Nob Hill in SF), slow and low, tower gap (grid only) |
| Y | tower gap with the scripted showcase pilot (grid only) |
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

**San Francisco** (`harness 200 --quick --map sf`, the 12.6 × 9.4 km map, about 133,000 obstacles):

| Config | Crashes | Invariant violations | Min true clearance | Filter active | ms / tick |
|---|---|---|---|---|---|
| **P1 filter ON** | **0 / 200** | **0** | 2.0 m | 66% | 2.52 |
| filter OFF | 200 / 200 | – | crash | – | – |
| P1 ON + gusty wind | 0 / 196 | 0 | 8.7 m | 70% | 2.66 |
| P1 ON + model error | 5 / 200 | 13 eps | crash | 68% | 2.44 |

- **Kamikaze:** survives all four SF scenarios (minimum clearance 2.2 to 2.4 m).
- **Street coverage:** 98.0% of street states have a verified escape, and
  82.5% of the 143 below rooftop height (73.4% with the nose 4° off the
  street). The grid city's are 98% and 93%. Most of the larger map is
  low-rise, so few street states lie below the rooftops at all.
- **Gusty wind passes acceptance on the larger map** (0 of 196 episodes lost
  their verified escape). On the old 6 km map two episodes did; a third of the
  random starts now spread over the larger map, so this is not the same test,
  and that earlier failure is not shown fixed.
- **Flying under the Golden Gate:** the filter lets you pass under the deck
  low (about 12–16 m above the water) and turns you away higher up (30 m):
  every escape starts climbing at once, and a climb begun under the deck hits
  it. An escape that holds its height before climbing would let higher
  passes verify.

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
