### Dive at the Tower gap street floor (01a-street-dive)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 3.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -120.00,-150.00,37.11,50.00,-30.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01a-street-dive: closest safe call, zero-margin gate, 28.7 m"
```

- filter on: no crash; closest pass during the save **0.01 m** at t = 4.2 s; minimum over 25 s 0.01 m (filter takes over at t = 2.7 s, hands back at 2.7 s, 17 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.5 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 8.0 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -120.00,-150.00,29.11,50.00,-30.000,90.000,0.000,0.60 --cinematic --paths --label "01a-street-dive: unverified twin, 20.7 m"
```

- filter on: **crashes** at t = 0.8 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 3.00 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -120.00,-150.00,40.98,50.00,-30.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01a-street-dive: closest call, deployed gate, 32.6 m"
```

- filter on: no crash; closest pass during the save **4.00 m** at t = 4.2 s; minimum over 25 s 3.88 m (filter takes over at t = 2.7 s, hands back at 2.7 s, 13 takeovers in all)
- filter off: **crashes** at t = 3.6 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -120.00,-150.00,13.08,50.00,-30.000,90.000,0.000,0.60 --cinematic --paths --label "01a-street-dive: proven unsafe, 4.7 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -120.00,-150.00,13.08,50.00,-30.000,90.000,0.000,0.60 --cinematic --paths --off --label "01a-street-dive: proven unsafe, 4.7 m"
```

- filter on: **crashes** at t = 0.0 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.0 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.0 s, left hits at 0.0 s, right hits at 0.0 s, left40 hits at 0.0 s, right40 hits at 0.0 s, street hits at 0.0 s)

