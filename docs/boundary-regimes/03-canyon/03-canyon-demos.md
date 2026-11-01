### Canyon run east along y = 120 (03-canyon)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 3.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -470.00,120.00,117.20,45.00,0.000,0.000,0.000,0.70 --lead 3 --cinematic --cam 0 --paths --label "03-canyon: closest safe call, zero-margin gate, 109.9 m"
```

- filter on: no crash; closest pass during the save **13.31 m** at t = 3.5 s; minimum over 25 s 0.10 m (filter takes over at t = 1.2 s, hands back at 1.2 s, 31 takeovers in all)
- filter off (`--off`): no crash; minimum airframe clearance 5.3 m (filter never takes over)

**Just-barely-unsafe twin**: 64.0 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -470.00,120.00,53.20,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --label "03-canyon: unverified twin, 45.9 m"
```

- filter on: **crashes** at t = 16.9 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 3.00 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -470.00,120.00,128.34,45.00,0.000,0.000,0.000,0.70 --lead 3 --cinematic --cam 0 --paths --label "03-canyon: closest call, deployed gate, 121.1 m"
```

- filter on: no crash; closest pass during the save **15.90 m** at t = 8.4 s; minimum over 25 s 3.93 m (filter takes over at t = 1.6 s, hands back at 1.6 s, 48 takeovers in all)
- filter off: no crash; minimum airframe clearance 6.1 m (filter never takes over)

