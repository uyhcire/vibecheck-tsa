### Level run at the ridge (05-ridge)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 3.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start 150.00,-1692.19,66.71,45.00,0.000,-90.000,0.000,0.70 --lead 3 --cinematic --cam 0 --paths --label "05-ridge: closest safe call, zero-margin gate, 357.8 m"
```

- filter on: no crash; closest pass during the save **28.56 m** at t = 8.5 s; minimum over 25 s 26.45 m (filter takes over at t = 0.5 s, hands back at 0.5 s, 12 takeovers in all)
- filter off (`--off`): **crashes** at t = 6.4 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 8.0 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start 150.00,-1700.19,66.71,45.00,0.000,-90.000,0.000,0.70 --cinematic --cam 0 --paths --label "05-ridge: unverified twin, 349.8 m"
```

- filter on: **crashes** at t = 6.0 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 3.00 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start 150.00,-1689.59,66.71,45.00,0.000,-90.000,0.000,0.70 --lead 3 --cinematic --cam 0 --paths --label "05-ridge: closest call, deployed gate, 360.4 m"
```

- filter on: no crash; closest pass during the save **32.33 m** at t = 8.5 s; minimum over 25 s 30.46 m (filter takes over at t = 0.5 s, hands back at 0.5 s, 10 takeovers in all)
- filter off: **crashes** at t = 6.5 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start 150.00,-1855.84,66.71,45.00,0.000,-90.000,0.000,0.70 --cinematic --cam 0 --paths --label "05-ridge: proven unsafe, 194.2 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start 150.00,-1855.84,66.71,45.00,0.000,-90.000,0.000,0.70 --cinematic --cam 0 --paths --off --label "05-ridge: proven unsafe, 194.2 m"
```

- filter on: **crashes** at t = 0.0 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.0 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.0 s, left hits at 0.0 s, right hits at 0.0 s, left40 hits at 0.0 s, right40 hits at 0.0 s, street hits at 0.0 s)

