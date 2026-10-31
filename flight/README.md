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
```

Harness flags: `[episodes] [--threads N] [--quick] [--extended]`. `--quick`
shortens the kamikaze endurance runs from 300 s to 60 s. The harness exits
non-zero if any acceptance check fails.

Demo flags (handy for screenshots): `--scenario 1..4`, `--off`, `--kamikaze`,
`--paths`, `--cam 0..3`, `--shot out.png --frames N`.

## Controls

| Key | Action |
|---|---|
| W/S or ↑/↓ | pitch (stick forward = nose down; `I` inverts) |
| A/D or ←/→ | roll. Release to hold flight path and bank (fly-by-wire) |
| Q / E | throttle down / up |
| Space | safety filter on/off |
| F | filter: P1 blend+commit → P2 closed-form → P1+P3 robust → P2+P3 |
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

**Clearance map** (`world.rs`). Terrain (piecewise-linear over a 20 m grid,
the same triangles the renderer draws) and ~2,100 building boxes are rasterised
into one 5 m max-height grid. It is dilated sideways by 3 cells (15 m) and
raised by 10 m. Off-map counts as a wall. Path segments are checked against
every cell they cross (`swept_max`), so the check covers the continuous path,
not just samples. Cost doesn't depend on the number of buildings.

**Aircraft** (`model.rs`). A point-mass 3D Dubins-style model with speed
dynamics: thrust and drag, lift limited by airspeed (so stall emerges on its
own), and first-order lags on load factor, roll rate and throttle. The numbers
are light-sport: stall 25 m/s, cruise 50 m/s. Physics runs at 100 Hz with RK4
and the filter at 50 Hz. The predictor uses the same equations.

**Escapes** (`escape.rs`). Four Auto-GCAS-style maneuvers, all at full power:
climbing turn L/R at up to 45° bank, and a 6 s wings-level pull-up followed by
a climbing turn L/R. The climb angle comes from a speed-hold through pitch, so
a slow aircraft trades less energy. Bank is limited so load factor stays under
85% of the stall limit. Each escape is valid only once it reaches a *steady
climbing helix after 360° of turn* whose ground circle is clear at the current
height. From then on it only gains height over the same ground.
`h_i(x)` is the worst clearance along escape `i` (−∞ if it never reaches the
helix within 40 s); `h(x) = max_i h_i(x)`.

**Phase 1 filter** (`filter.rs`, default). Each tick it predicts the pilot's
command held for 0.5 s, then each escape. As that margin drops from 40 m to
5 m it blends toward the best escape. It checks the blended command the same
way; if that passes, it becomes the new committed plan. Otherwise it keeps
flying the plan committed at the last tick that passed (gatekeeper). New plans
must clear a map one cell wider (20 m) by 3 m. Every tick it re-checks the
committed plan against the 15 m map and asserts that a verified escape exists.

**Phase 2 filter** (after van Wijk et al.). It interpolates
`u = (1−β) u_pilot + β u_backup` with the smallest β satisfying
`ḣ ≥ −α (h − 12 m)`, a scalar inequality solved in closed form. ḣ comes from
finite differences of a bilinear (smooth) version of `h`. The Phase 1 check
and committed fallback still run underneath as a safety net.

**Phase 3 robustness**. The predictor uses the worst-case (mismatch)
aircraft and an estimated mean wind. The required clearance grows along the
prediction: 1 m/s laterally (via wider maps) and 0.25 m/s vertically.

The filter only ever changes the commands sent to the aircraft. Collisions are
always checked against the true geometry (an aircraft sphere of radius 4.5 m
against boxes and terrain), never against the inflated map.

## Results (`harness 200 --extended`, M3 Max)

| Config | Crashes / 200 | Invariant violations | Min true clearance | Filter active | Commit | ms / tick |
|---|---|---|---|---|---|---|
| **P1 filter ON** | **0** | **0** | 15.0 m | 80% | 0.0% | 0.72 |
| filter OFF | 199 | – | crash | – | – | – |
| P1 + mismatch | 9 | 29 eps | crash | 81% | 1.3% | 0.72 |
| OFF + mismatch | 200 | – | crash | – | – | – |
| P2 closed-form | 0 | 0 | 13.7 m | 55% | 2.2% | 0.80 |
| P1+P3 robust + mismatch | 2 | 25 eps | crash | 83% | 2.4% | 0.80 |
| P2+P3 robust + mismatch | 2 | 51 eps | crash | 60% | 5.3% | 0.83 |

Kamikaze autopilot with the filter on survives 300 s in all four scenarios
(minimum clearance 19.7 to 26.4 m). Straight flight well above obstacles shows
0 blended ticks out of 8,000. Episodes are 60 s from random starts inside the
safe set. Pilots are a nose-down-biased random stick, with a kamikaze
autopilot in a quarter of the episodes. Every configuration uses the same seeds.

Phase 1 vs Phase 2: P2 intervenes less often (55% vs 80% of ticks) but much
less smoothly (command change per active tick 0.28 vs 0.07), and its fallback
fires more.

Timing: the `ms max` column in the harness (~100 ms) comes from 16 threads
sharing the CPU. Single-threaded (`--threads 1`) the mean is 0.58 ms and the
worst tick 3.1 ms.

## What is assumed / trusted

- **The guarantee holds only under the nominal model with full state
  knowledge.** It rests on the predictor matching the plant. Here they share
  equations; RK4 at 0.1 s vs 0.01 s differs by millimetres, and by about 1 m on
  the pull-up escapes. The 3 m acceptance margin and the one-cell-wider
  acceptance map absorb that and the sampling-phase effects.
- With mismatch on, the guarantee no longer strictly holds. The harness
  measures it: 9/200 crashes with P1, 2/200 with Phase 3 margins.
- The Phase 3 terminal check under wind clears one drifting lap, not "forever".
- The safety argument is engineering-level and tested, not machine-checked.
