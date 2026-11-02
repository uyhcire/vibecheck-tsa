# Backup-CBF City Flight

Fly a light aircraft through a procedural city with the keyboard. A backup
control barrier function (bCBF) safety filter stays silent far from obstacles,
takes over near buildings and terrain, then hands control back. Space toggles
the filter, so you can fly the same crash attempt with and without it.

Native Rust: the simulation, filter and harness are a GUI-free library; the
demo renders with macroquad, with terrain and buildings held in static GPU
buffers through raw miniquad (about 120 fps at 2880×1800 with 4× MSAA on an M3 Max, classic renderer).

## Run

```sh
cd flight
cargo run --release                                   # the demo
cargo run --release --no-default-features --bin harness              # acceptance harness (200 episodes)
cargo run --release --no-default-features --bin harness -- --extended  # + Phase 2 / Phase 3 rows
cargo run --release --no-default-features --bin harness -- --coverage  # street coverage only
```

Harness flags: `[episodes] [--threads N] [--quick] [--extended] [--coverage]`. `--quick`
shortens the kamikaze endurance runs from 300 s to 60 s. The harness exits
non-zero if any acceptance check fails.

Demo flags (handy for screenshots): `--scenario 1..5`, `--off`, `--kamikaze`, `--showcase`,
`--paths`, `--cam 0..4`, `--shot out.png --frames N`.

Recording: `--record DIR` writes rendered frames as `DIR/frame_NNNNN.png` and exits after `--frames N`
(default 1800). Like `--shot`, it steps a fixed 1/60 s of simulated time per rendered frame and runs animations
off that clock, so the frames do not depend on how fast the machine renders (two runs give identical frames apart from the HUD's filter-time readout, which is measured wall-clock time). `--record-every K` keeps every
K-th frame (2 gives 30 fps footage), `--record-from F` skips the first F frames, `--record-scale K` shrinks
each frame K times (2 turns a Retina capture into its 1x size). `DIR/frames.csv` logs the flight at each kept
frame (time, simulated time, airframe clearance and its running minimum, filter mode, crash), and
`DIR/args.txt` the command line; the run ends by printing an `ffmpeg` command that encodes the frames.

`DIR/trace.jsonl` has one JSON object per kept frame, for drawing on the footage:

| key | meaning |
|---|---|
| `frame`, `png`, `t`, `sim_t` | rendered frame index, its PNG, time (frame / 60 s), simulated time (stops at a crash) |
| `clear`, `min_clear`, `crashed` | airframe clearance (m), its running minimum, contact |
| `mode` | `pilot`, `blend`, `escape` (the gate flying its escape) or `off` (filter off) |
| `escape`, `escape_verified` | name of the escape the gate is flying, else the one it holds as verified (`street`, `left`, `left40`, ...), or `null`; whether one is verified |
| `escape_path` | that escape's verified path (rollout plus terminal continuation, world metres), thinned to points at least 20 m apart, about 2 Hz at demo speeds. While the pilot flies it is the rollout that verified on the latest check; while the gate flies the escape it is the path verified before the takeover, from the takeover point on |
| `aircraft`, `camera` | aircraft centre of gravity as drawn, camera position (world metres) |
| `viewport` | the saved PNG's size in pixels `[w, h]` |
| `view_proj` | the camera's view-projection, column-major 16 floats, from world coordinates (x east, y north, z up, metres: the gate's frame). A point `p` lands at pixel `((c.x/c.w + 1)/2 * w, (1 - c.y/c.w)/2 * h)` with `c = view_proj * [p, 1]`, in front of the camera when `c.w > 0`. The photoreal renderer's depth is reversed and infinite |

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

**Fuel.** Every mode that flies the JSBSim aircraft (`--jsb`, `--safety-filter exact-rollout`, the `crashes`, `adversary`, `esclab`, `regimes`, `harness`, `drawstep` and `jsbtune` bins) flies with infinite fuel
by default: JSBSim's `propulsion/fuel_freeze` is on, mirroring the safety spec's assumption (`../docs/safety-objective.md`,
`CitySafety.specStep`). The flown aircraft and every rollout fork step the same setting; it is chosen in one place
(`jsb::fuel_freeze_default`, applied by `JsbPlant`'s constructors, carried by `fork` and `Seed`). `--fuel-drain` on any of
those bins restores fuel burning for both. `--fuel-drain` does not combine with `--safety-filter exact-rollout-lean`, whose
Lean gate always rolls out with fuel freeze. `cargo run --release --features jsb --bin fuelcheck` against
`lake exe fuelfreezecheck` (arguments printed by `fuelcheck`) compares the plant with `JsbExact.step` bit for bit in both settings.

```sh
(cd .. && lake build libcityjsb)
cargo run --release --features jsb -- --jsb                                        # the demo
cargo run --release --no-default-features --features jsb --bin harness -- --jsb    # harness
cargo run --release --no-default-features --features jsb --bin jsbtune             # fly-by-wire tracking
```

### Exact-rollout gatekeeper (`--safety-filter exact-rollout`)

Proof status (nothing about this filter is proved yet; what is exact and what is numerical): `../docs/gate-proof-status.md`.

`src/envfilter.rs` predicts with the plant itself: each check forks the JSBSim aircraft and flies an escape
law on the copy, frame by frame, so a committed escape flies exactly the frames that were checked.

- **Escape law.** A longitudinal law ported from a synthesised one (`Ci/cegis/Law.lean`, not in this
  repository; full throttle, flight-path loop over a load factor ≤ 3.5 and α ≤ 0.24, trim feedforward,
  pitch-rate feedforward), plus an α integral, load factor divided by cos φ in a bank, roll PI-D, a
  sideslip-nulling rudder and a heading hold. `--law lawfirst` flies the α-command law of `Ci/lawfirst`
  (also not in this repository) instead; `--law cegis1` the earlier cegis law. Once the pull-up ends (the
  terminal phase), the default law climbs at a constant equivalent airspeed: 35.2 m/s straight, 37.8 m/s in
  the 30° turns and 40.3 m/s in the 40° turns, the same α (about 0.08) in each, with a stiffer speed loop
  (0.06 rad per m/s, gradient 0 to 0.5) and α integral (6/s) (`docs/escape-law-terminal.md` on PR #46 for the
  straight escape). Every escape levels off at 1,000 m (gradient capped at `0.005·(1000 − h)`), 66 m above
  the map's top. The gate's earlier law locked into a post-stall descent (α ≈ 0.28, α integral at its
  clamp) at 32-37 m/s in the turns; the terminal law recovers from every such state found
  (`make termhunt ARGS=trim`).
- **Escapes.** A straight climb-out, and climbing turns left and right at 30° and 40° bank, after a pull-up
  of at least 1.5 s. A street escape captures the nearest street axis when the track is within 25° of one
  (bank ≤ 20° while capturing), climbs wings level along it, and every 0.25 s looks for a 40° helix whose
  predicted annulus is clear at its height (10 m margin, left side first); then it rolls in, but only before
  the first end test (6 s), so the kind of ending an end test accepts never changes afterwards. It never
  verifies through its ray ending from below the rooftops: a ray along a street axis must clear the
  ~900 m rim of the map. `--escapes 5` drops the street escape, `3` also the 40° turns.
- **Airframe.** Path samples and the crash check use `World::airframe_clearance`: the 4.5 m sphere plus the
  wing, a 0.8 m capsule around the line through both wingtips (11 m span, as `c172.rs` draws it), placed by
  the bank, heading, flight path and drawn angle of attack. Buildings are exact (segment to box); terrain
  under the wing is sampled every 0.25 m outboard of 4 m span. The tail trails inside the volume the
  sphere has just swept, so it is not checked. The point-mass filter and its crash check keep the sphere.
- **Terminal sets**, checked on the settled rollout (from 6 s on, within 16 s): the straight escape needs a
  settled climb (the two 2 s windows' mean climb rates agree within 1 m/s), then a climbing ray (80% of the
  settled gradient, at most 0.11 so the pull-up's zoom climb cannot set it, in a corridor widening 2% of
  distance) that clears every raw cell until it is above the map's top. A turn needs a steady helix: radius
  and centre within 10% of the radius across two 2 s windows, climbing ≥ 1 m/s, airspeed settled
  (the windows' means within 1 m/s) above the post-stall band (≥ 37.5 m/s at 30°, ≥ 39.5 m/s at 40°), and
  specific energy `z + v²/2g` not falling in either window. Its ground annulus must be clear at the current
  height and lie within the map: the fitted radius ± (5 m + 3 × the fit disagreement), widened outward by the
  growth of a constant-EAS turn's radius up to the map's top (radius ∝ 1/ρ) and on both sides by the
  airframe's 7 m half-size. Any escape in its terminal phase also ends when its whole 4 s window is above
  980 m at ≥ 30 m/s: from there the level-off keeps it above the map's top (`make termhunt ARGS=high`). Beyond the map edge the terrain continues
  the edge profile (731-927 m), so the ray (at most 12.5 km) and the crash test are checked against it. Every path
  sample (every 8th frame) keeps 4 m of true clearance. `--swept` checks every frame instead, including the
  frames of the pilot's candidate tick, each keeping `--margin M` (default 4 m) plus half a frame of travel
  of any airframe point, so no contact can occur between frames; `--handback-extra M` overrides the 3 m
  hand-back spare clearance for measurements.
- **Scheduling.** Each 20 ms tick checks the pilot's next tick followed by the last escape that verified;
  the pilot keeps control if it verifies. Otherwise the filter commits to the escape verified on the
  previous tick, and committed ticks try the escapes round robin. A deterministic budget of 2,200 JSBSim
  frames per tick (15 ms at the measured 6.7 µs per checked frame) caps the work. The GUI also stops checks
  at a 15 ms wall-clock deadline (`--time-cap MS`, 0 = off): a check cut short fails, so the filter keeps
  its verified escape. Headless runs stay deterministic unless given `--time-cap`.

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout                                    # fly it (B: escapes); from the repo root: make fly
cargo run --release --features jsb -- --safety-filter exact-rollout --episode 59                       # replay an episode
cargo run --release --features jsb -- --safety-filter exact-rollout --showcase --paths                # Tower gap showcase
cargo run --release --no-default-features --features jsb --bin crashes -- /tmp/s 100 --safety-filter exact-rollout --scenario 5
cargo run --release --no-default-features --features jsb --bin crashes -- /tmp/c 200 --safety-filter exact-rollout
cargo run --release --no-default-features --features jsb --bin adversary -- /tmp/a exact-rollout 200
cargo run --release --no-default-features --features jsb --bin esclab -- trace     # escape-law traces
```

With `B`, the latest rollout is drawn green (verified) or red, and the committed escape yellow; turning
escapes end in their terminal helix.

Boundary regimes (`docs/boundary-regimes`, `--bin regimes`): where the gate's safe set ends near each kind of
obstacle, with markers drawn at actual contact and one-line demos. Demo flags: `--start x,y,z,v,γ°,heading°,bank°,thr`
(a given start, flown with the sticks released), `--lead S` (moved back S seconds along its velocity), `--margin M`
and `--check-every N` (the gate's clearance margin and check spacing in frames; defaults 4 m and 8), `--label TEXT`.
The HUD shows the minimum clearance so far.

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

`adversary -- /tmp/a exact-rollout 200`: 0 crashes in 2,640 gap-guided flights from 200 verified starts. An
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
| G | Phase 3 robust margins on/off (works with any filter) |
| B | escape paths (green valid, red invalid, yellow = committed plan) |
| M | model mismatch: wind + gusts, weaker and slower aircraft |
| 7 | wingtip strobes on/off (off by default; `--strobes` to start with them on) |
| C | camera: chase, cockpit, orbit, overhead, fly-by |
| 1–5 | scenarios: tower run, dive, ridge, slow and low, tower gap |
| Y | tower gap with the scripted showcase pilot |
| K | kamikaze autopilot |
| T | run the 200-episode harness in the background |
| R / H | reset / help |

The trail is coloured by what the filter was doing: blue = pilot in control,
orange = blending, red = committed escape, white = filter off.

## How it works

**Clearance checks** (`world.rs`). **Buildings are checked exactly:** each
predicted path segment's distance to every nearby box (exact segment-to-box
distance, found through a bucket grid) must exceed the aircraft's 4.5 m
radius plus 1 m. New plans need another 0.5 m plus 0.5 m of overall slack, so
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

**Escapes** (`escape.rs`). Ten Auto-GCAS-style maneuvers, all at full power:
a pull-up of 0, 3, 6, 10 or 15 s (up and out of a street canyon), then a
climbing turn left or right at up to 45° bank. During the pull-up the escape
steers onto the nearest street direction if the nose is within 25° of it.
That direction is fixed by the heading when the escape begins, so the
predictor and the aircraft fly the same path. Each escape gets 40 s after its
pull-up to reach the terminal helix. The climb angle comes from a speed-hold through pitch, so
a slow aircraft trades less energy. Bank is limited so load factor stays under
85% of the stall limit. Each escape is valid only once it reaches a *steady
climbing helix after 360° of turn* whose ground circle is clear at the current
height. From then on it only gains height over the same ground.
`h_i(x)` is the worst clearance along escape `i` (−∞ if it never reaches the
helix in time); `h(x) = max_i h_i(x)`.

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

**Phase 3 robustness**. The predictor uses the worst-case (mismatch)
aircraft and an estimated mean wind. The required clearance grows along the
prediction: 1 m/s laterally (via wider maps) and 0.25 m/s vertically.

The filter only ever changes the commands sent to the aircraft. Collisions are
always checked against the true geometry (an aircraft sphere of radius 4.5 m
against boxes and terrain), never against the inflated map.

## Results (`harness 200 --extended`, M3 Max)

| Config | Crashes / 200 | Invariant violations | Min true clearance | Filter active | Commit | ms / tick |
|---|---|---|---|---|---|---|
| **P1 filter ON** | **0** | **0** | 2.0 m | 64% | 0.3% | 1.72 |
| filter OFF | 199 | – | crash | – | – | – |
| P1 + mismatch | 106 | 151 eps | crash | 64% | 5.0% | 1.68 |
| OFF + mismatch | 200 | – | crash | – | – | – |
| P2 closed-form | 0 | 0 | 2.8 m | 51% | 0.1% | 1.85 |
| Permissive | 0 | 0 | 2.0 m | 32% | 32% | 0.63 |
| P1+P3 robust + mismatch | 10 | 73 eps | crash | 68% | 5.1% | 2.23 |
| P2+P3 robust + mismatch | 1 | 51 eps | crash | 54% | 3.4% | 2.15 |

Minimum true clearance is the gap between the aircraft's 4.5 m sphere and
the nearest building or terrain surface. The 2.0 m floor is exactly the
margin new plans must keep (1 m + 0.5 m + 0.5 m slack), which shows the
predictor and the aircraft agree.

**Flying between buildings.** Of 2,000 random states on street centrelines
20–90 m above the ground, 92% of those below rooftop height have a verified
escape, even with the nose 4° off the street axis. (It was 5.9% with the
original margins and four escapes.) A street-following autopilot holding
40 m on six streets spends this share of its time below rooftops:

| Filter | Below rooftops | Mean intervention |
|---|---|---|
| off | 44.4% | – |
| P1 (time margin) | 41.0% | 0.04 |
| Permissive | 43.2% | 0.03 |
| P2 | 17.7% | 0.23 |

P2 keeps the barrier above a 12 m floor, which is conservative in streets.

Kamikaze autopilot with the filter on survives 300 s in all four scenarios
(minimum clearance 2.0 to 2.1 m). Straight flight well above obstacles shows
0 blended ticks out of 8,000. Episodes are 60 s from random starts inside the
safe set. Pilots are a nose-down-biased random stick, with a kamikaze
autopilot in a quarter of the episodes. Every configuration uses the same seeds.

Timing: the `ms max` column in the harness (~100 ms) comes from 16 threads
sharing the CPU. Single-threaded (`--threads 1`) P1 averages 1.3 ms and its
worst tick is 5.2 ms, well inside the 20 ms filter period.

## The trusted core

The safety claim rests only on:
1. **Every command sent to the aircraft is verified first:** the command for
   a moment, then an escape whose whole path clears the inflated map and
   reaches the terminal helix.
2. **If that check fails, the aircraft flies the last verified plan**
   (gatekeeper), so a verified escape always exists.
3. **The clearance checks are conservative:** exact segment-to-box distance
   for buildings; a dilated, swept height map for terrain.
4. **The predictor uses the same equations as the aircraft.**

The blending rules (P1, P2, permissive), the GUI and the autopilots only
choose which candidate command to try. They sit outside the trusted core, so
they can be tuned for feel without touching what needs certifying.

## What is assumed / trusted

- **The guarantee holds only under the nominal model with full state
  knowledge.** It rests on the predictor matching the plant. Here they share
  equations; RK4 at 0.1 s vs 0.01 s differs by millimetres, and by about 1 m on
  the pull-up escapes. The 1 m acceptance margin and the one-cell (2.5 m)
  wider acceptance map absorb that and the sampling-phase effects.
- With mismatch on, the guarantee no longer strictly holds. The harness
  measures it: 106/200 crashes with P1, and 10/200 (P1) or 1/200 (P2) with
  Phase 3 margins (G). A 1 m building margin leaves no room for model error,
  so turn on G whenever mismatch (M) is on.
- The Phase 3 terminal check under wind clears one drifting lap, not "forever".
- The safety argument is engineering-level and tested, not machine-checked.
  The trusted core above is the part to prove formally.
