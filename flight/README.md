# Backup-CBF City Flight

Fly a light aircraft through a procedural city with the keyboard. A backup
control barrier function (bCBF) safety filter stays silent far from obstacles,
takes over near buildings and terrain, then hands control back. Space toggles
the filter, so you can fly the same crash attempt with and without it.

Native Rust: the simulation, filter and harness are a GUI-free library; the
demo renders with macroquad, with terrain and buildings held in static GPU
buffers through raw miniquad (about 120 fps at 2880×1800 with 4× MSAA on an M3 Max).

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

Demo flags (handy for screenshots): `--scenario 1..4`, `--off`, `--kamikaze`,
`--paths`, `--cam 0..3`, `--shot out.png --frames N`.

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
| C | camera: chase, cockpit, orbit, overhead |
| 1–4 | scenarios: tower run, dive, ridge, slow and low |
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
