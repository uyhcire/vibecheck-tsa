### Wall ahead across the park (04a-wall-ahead)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 2.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -399.19,295.00,57.49,45.00,0.000,0.000,0.000,0.70 --lead 2 --cinematic --cam 0 --paths --label "04a-wall-ahead: closest safe call, zero-margin gate, 181.1 m"
```

- filter on: no crash; closest pass during the save **0.25 m** at t = 7.7 s; minimum over 25 s 0.25 m (filter takes over at t = 2.0 s, hands back at 9.8 s)
- filter off (`--off`): **crashes** at t = 5.8 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 0.5 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -398.69,295.00,57.49,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --label "04a-wall-ahead: unverified twin, 180.6 m"
```

- filter on: **crashes** at t = 5.8 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 1.75 s):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -406.08,295.00,57.50,45.00,0.000,0.000,0.000,0.70 --lead 1.75 --cinematic --cam 0 --paths --label "04a-wall-ahead: closest call, deployed gate, 188.0 m"
```

- filter on: no crash; closest pass during the save **4.37 m** at t = 7.7 s; minimum over 25 s 4.37 m (filter takes over at t = 1.7 s, hands back at 7.9 s, 4 takeovers in all)
- filter off: **crashes** at t = 5.7 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -243.39,295.00,56.83,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --label "04a-wall-ahead: proven unsafe, 25.3 m"
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -243.39,295.00,56.83,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --off --label "04a-wall-ahead: proven unsafe, 25.3 m"
```

- filter on: **crashes** at t = 0.5 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.5 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.5 s, left hits at 0.5 s, right hits at 0.5 s, left40 hits at 0.5 s, right40 hits at 0.5 s, street hits at 0.5 s)

