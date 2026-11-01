### Beside the park-side tower (02a-wall-beside-park)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 0.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -230.10,265.00,56.98,45.00,0.000,80.000,0.000,0.70 --lead 0 --cinematic --cam 0 --paths --label "02a-wall-beside-park: closest safe call, zero-margin gate, 12.0 m"
```

- filter on: no crash; closest pass during the save **0.00 m** at t = 1.6 s; minimum over 25 s 0.00 m (filter takes over at t = 0.1 s, hands back at 0.1 s, 12 takeovers in all)
- filter off (`--off`): **crashes** at t = 0.7 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 0.5 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -229.60,265.00,56.98,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --label "02a-wall-beside-park: unverified twin, 11.5 m"
```

- filter on: **crashes** at t = 1.4 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 1.50 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -234.10,265.00,57.00,45.00,0.000,80.000,0.000,0.70 --lead 1.5 --cinematic --cam 0 --paths --label "02a-wall-beside-park: closest call, deployed gate, 16.0 m"
```

- filter on: no crash; closest pass during the save **3.99 m** at t = 3.2 s; minimum over 25 s 3.99 m (filter takes over at t = 1.0 s, hands back at 1.5 s, 7 takeovers in all)
- filter off: **crashes** at t = 2.7 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -218.10,265.00,56.92,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --label "02a-wall-beside-park: proven unsafe, 0.0 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -218.10,265.00,56.92,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --off --label "02a-wall-beside-park: proven unsafe, 0.0 m"
```

- filter on: **crashes** at t = 0.0 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.0 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.0 s, left hits at 0.0 s, right hits at 0.0 s, left40 hits at 0.0 s, right40 hits at 0.0 s, street hits at 0.0 s)

