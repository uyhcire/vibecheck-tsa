# Entering the Tower gap from open air

The Tower gap scenario (`flight/README.md`, `--scenario 5`) spawns inside the gap because the gate filter
(`--safety-filter exact-rollout`) verifies no escape on the approach: a pilot flying up the street from open air is taken over
before reaching it. This page settles whether that is physics or the filter's conservatism. It is
conservatism, entirely: every state on the approach is proven safe by the gate's own street escape, and what
rejects them is the 16 s rollout horizon. A 24 s horizon for the street escape alone (`--street-horizon 24`)
makes the gate accept the whole approach.

## The slice

The street `x = −120` (28 m wide), on its centreline, 88 m above the street, 45 m/s, level, wings level,
heading north, throttle 0.7: the scenario's spawn state, moved along the street. `y` runs from −1100 (open
air: roofs below 25 m) to +100, every 5 m (241 states). North of `y ≈ −470` the street is lined by towers
taller than the aircraft's height (103 m at `y = −460`, 153 to 160 m at −300, 252/283 m at −80, the 261 m and
292 m towers at the spawn, then the avenue `y = 0` and the 235 m and 352 m towers of row 10).

## Verdicts

- **Proven safe (contact)**: an explicit program, flown exactly on JsbExact from the state, with the airframe
  clearance (`World::airframe_clearance`, the 4.5 m sphere plus wing capsule) positive at **every** JSBSim
  frame, until the terminal condition below.
- **Terminal condition**: the airframe's centre is more than 10 m above the highest point anywhere (926.7 m,
  `world.raw_top`: every terrain and roof cell of the map; the terrain beyond ±3000 m continues the edge
  profile, which is on the map, so it is no higher) and the aircraft is climbing. Sound because nothing exists
  above that height: the body sphere reaches 4.5 m below the centre and the banked wing about 4.3 m, so no
  contact is possible at any later time while the aircraft stays at or above that height, and a c172 can hold
  its altitude there (it is still climbing at full power when the flight stops). Fuel: the spec's plant
  (`CitySafety.specStep`, #31) freezes fuel, so holding altitude is possible forever there; the witnesses
  here are flown on `libcityjsb` (`cityjsb_step`), which burns fuel as the gate's rollouts do, so they are not
  bit-exact replays on the spec's plant (the difference is the mass of the fuel burnt in about 400 s). No helix or ray extrapolation is used: the climbing helix the program ends in is
  flown out, frame by frame, all the way to that height (about 400 s).
- **Proven unsafe**: none can exist on this slice, since every state is proven safe. (`regimes::outer_bound`
  was run at every state anyway and proves nothing: the street is open ahead.)
- **Gate accepts**: the deployed gate's own verdict (`Gate::new`'s search: six escapes, 4 m margin, clearance
  every 8 frames, 16 s horizon).

The program is the same at every state: **the gate's own street escape** (`Law::new(STREET)`), from the first
frame: full power, wings level, track locked onto the street axis, climbing at its reference speed, and
rolling into a 40° climbing helix as soon as one fits at its height (the annulus clear by 10 m). From the
rejection bands it rolls in, always to the left (over the park blocks west of the street), at `y = 160` to
`330` and 190 to 222 m: for example from `y = −480` it climbs along the street past both gaps and rolls in at
(−122, 160, 222) at 17.3 s; its closest pass is 10.7 m, at 13.4 s, beside the row-9 towers.

| y (m) | Gate accepts (16 s) | Gate, `--street-horizon 24` | Proven safe: min clearance | Street escape reaches its terminal set (contact / 4 m) | Helix roll-in |
|---|---|---|---|---|---|
| −1100 to −720 | yes (straight, then left turn) | yes | > 45 m | 7.5 s / 7.5 s | 1.5 s |
| −700 | yes (left) | yes | 37.5 m | 8.5 s / 8.5 s | 2.5 s |
| −600 | yes (left) | yes | 18.1 m | 17.5 s / 17.5 s | 11.8 s |
| −540 | yes (left 40°) | yes | 14.9 m | 18.0 s / 18.0 s | 10.5 s |
| −500 | yes (left 40°) | yes | 12.3 m | 23.5 s / 23.5 s | 17.8 s |
| **−480** | **no** | yes | 10.7 m | 23.0 s / 23.0 s | 17.3 s |
| −400 | no | yes | 9.8 m | 22.0 s / 22.5 s | 15.0 s |
| −300 | no | yes | 9.6 m | 20.0 s / 20.0 s | 12.5 s |
| −240 | no | yes | 9.4 m | 18.5 s / 18.5 s | 11.0 s |
| −220 to −170 (but −210) | yes (street) | yes | 9.3 m | 15.5 to 16.0 s | 9.8 to 10.3 s |
| −160 | no | yes | 9.2 m | 19.0 s / 19.0 s | 13.0 s |
| −100 | no | yes | 9.1 m | 17.0 s / 17.0 s | 11.3 s |
| −80 | no | yes | 9.0 m | 16.5 s / 16.5 s | 10.8 s |
| **−65** | **yes (street)** | yes | 8.9 m | 16.0 s / 16.0 s | 10.3 s |
| −60 (the spawn) to +100 | yes (street) | yes | 8.1 to 8.8 m | 12.0 to 16.0 s | 6.0 to 10.3 s |

All 241 states are proven safe; the gate rejects 73 of them, in two bands: −480 to −225 (plus −210) and −165
to −70, 410 m of street, about 9 s of flight. Full grid: `gapentry verdict` (below).

## The gap

**Proven safe starts at the far end of the slice (open air) and never stops; the gate stops accepting at
−480 and resumes for good at −65.** The safe continuation through the bands is not a different manoeuvre: it
is the street escape the gate already has, climbing wings-level along the street at full power past the row-9
towers and rolling into its 40° climbing helix once the helix fits at its height, 10 to 17 s in. Its
closest pass is 9.4 to 10.7 m in the bands, at the walls beside the street (with wings level the airframe
envelope has 9.5 m to each kerb), so the 4 m margin costs nothing here: the time it needs is the same at
contact and at 4 m (to 0.5 s).

**What blocks the gate: the 16 s horizon.** In the bands the street escape needs 16.5 to 23 s to settle into
its helix and pass the terminal test (roll-in at 10.8 to 17.3 s plus about 5.7 s to settle over two 2 s
windows), so at 16 s it ends `unsettled`. The other five escapes fail for real: the 30° and 40° turns hit the
street's walls within 2 to 7 s (`wall-side`, `wall-ahead`), and the straight escape's climbing ray is blocked
by the hills beyond the city (`ray-terrain`). The 4 m margin matters only at −485 and −480, where the left
40° turn passes at contact but not at 4 m. The terminal sets are not what binds: the helix terminal set fits
once the escape has climbed far enough, it just needs more than 16 s to get there.

## The prototype: `--street-horizon S`

`RollCfg::street_horizon`: the street escape's rollout runs to the longer of `horizon` and `street_horizon`.
`--street-horizon S` (GUI, `crashes`, `adversary`) sets it for the filters; default 16 s, so nothing changes
without the flag. The escape, the terminal sets, the margin and the gate's logic are unchanged: a verified
rollout is the same exact, every-frame-checked flight ending in the same helix, only allowed to take longer.

- **No reliance on the two terminal-set bugs found by the crash hunt** (leaving the map counted as terminal;
  the straight escape's climbing ray fitted during the zoom): every one of the 241 prototype acceptances ends
  in the street escape's helix terminal set, none by leaving the map and none through the straight escape
  (`gapentry ends`), and the proven-safe witnesses count leaving the map as contact and use no ray. The
  deployed gate's acceptances at `y ≤ −1060` do go through the straight escape's ray; they are not used here.
- **Acceptance on the slice**: with `--street-horizon 24`, the gate accepts **all 241 states**, from open air
  through both gaps (`gapentry verdict`, column `gate24`). 23 s would do on the centreline; 24 s matches the
  richer search's horizon in the boundary-regimes study.
- **Around the slice** (`gapentry grid`: `y` from −700 to −60 every 20 m, offsets of 0, ±3 and ±6 m from the
  centreline, 70, 88 and 105 m above the street, headings 0 and ±3° off the axis; 1485 states): the gate
  accepts 674, the prototype 1213. Inside the bands (`y ≥ −480`, 990 states) 201 against 733. Of the 272 the
  prototype still rejects, 249 are states 3 to 6 m off the centreline and heading toward the nearer wall: the
  street escape's capture swings the airframe within 4 m of that wall, so there the 4 m margin binds (205 of
  the 272 are proven safe at contact by the same escape; 67, mostly 6 m east and 3° toward the east wall,
  touch it). The other 23 need a 24.5 to 26.5 s horizon.
- **In flight.** On main the GUI checks every escape to its full horizon in parallel (#23, `CHECK_THREADS`),
  so the longer street rollout is never cut short. Flying in with the sticks released from `y = −700`, the
  first takeover is at `y = 334`, 22 s in, past both gaps, when the fly-by-wire's slow drift has carried the
  aircraft 7.6 m west of the centreline (filter off, the same drift puts the wing into the west wall at
  23.8 s). With the budgeted sequential check (`--check-threads 0`, the default of the headless `crashes` and
  `adversary`), the 2200-frame budget also binds: after the left-turn witness of open air fails, the street
  escape's 24 s rollout no longer fits in the tick, and the gate commits to the left turn at `−485`.
  `--budget 4400` removes that. Cost on the demo flight, all escapes summed (`gapentry trace`, one check
  thread): median 1472 JSBSim frames per tick, p99 4172, max 6464; the deployed gate on the same flight:
  median 1152, p99 12868 (its takeover flies the gate's left turn, where every escape is checked).
- **Safety** (measured on the pre-#23 base, `d29b484`, budgeted sequential checks): `crashes --scenario 5` (50 hostile and 50 kamikaze pilots from the Tower gap spawn, plus the
  showcase pilot), with `--street-horizon 24 --budget 4400`: **0 / 100 crashes**, showcase no crash, 30.9% of
  ticks committed (deployed gate: 31.3%), 0 ticks committed with no witness.
  `crashes` on 40 hostile-pilot episodes plus the 5 kamikaze scenarios, same flags: **0 / 40** and **0 / 5**,
  all from verified starts, 29.8% of ticks committed (fewer episodes than the usual 200 because the machine was
  heavily shared; at load 110 to 150 the 100 Tower gap flights took 36 min).
  `adversary` with the same flags, 6 verified starts (the usual run uses 200): **0 crashes in 252** gap-guided
  flights.
  Per-tick cost in those runs: median 896 to 960 JSBSim frames, p99 4400 (the raised budget), thread CPU median
  9 to 10 ms, p99 45 ms on the loaded machine.

## GUI demos (run from `flight/`)

The same start, open air on the centreline at `y = −700`, flown with the sticks released (the fly-by-wire holds
flight path and bank). Measured headless with full-horizon checks (`gapentry demo -700 40 --check-threads 1`,
`gapentry trace`), which give the GUI's verdicts.

The deployed gate takes over at `y = −485` (4.7 s), where nothing verifies any more, and flies its left 40°
witness out of the street and round over the blocks to the west (5 takeovers, 360 of 2000 ticks committed):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --start -120.00,-700.00,94.40,45.00,0.000,90.000,0.000,0.70 --cinematic --cam 0 --paths --label "gap entry: deployed gate (16 s horizon)"
```

With the prototype the aircraft flies in untouched, through both gaps; the one takeover is at `y = 334`
(22.0 s), where the drift has carried it 7.6 m west of the centreline (115 of 2000 ticks committed):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --street-horizon 24 --start -120.00,-700.00,94.40,45.00,0.000,90.000,0.000,0.70 --cinematic --cam 0 --paths --label "gap entry: street escape horizon 24 s"
```

Add `--off` to see the drift put the wing into the west wall at 23.8 s. Press `B` to see the street escape's
verified path during the approach.

## Reproduce

From `flight/` (after `(cd .. && lake build libcityjsb)`):

```sh
cargo run --release --no-default-features --features jsb --bin gapentry -- verdict      # the verdict map, every 5 m
cargo run --release --no-default-features --features jsb --bin gapentry -- witness -480 # one proven-safe flight
cargo run --release --no-default-features --features jsb --bin gapentry -- grid         # acceptance off the centreline
cargo run --release --no-default-features --features jsb --bin gapentry -- demo -700 40 --check-threads 1  # the GUI demos, headless
cargo run --release --no-default-features --features jsb --bin gapentry -- trace -700 30 24 2200 --check-threads 1  # each takeover and why
```

`--threads N` (default 3) for `verdict` and `grid`.
