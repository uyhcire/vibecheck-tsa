### Closing on the park-side tower at an angle (02b-wall-beside-angle)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 1.50 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -243.10,265.00,57.05,45.00,0.000,69.190,0.000,0.70 --lead 1.5 --cinematic --cam 0 --paths --label "02b-wall-beside-angle: closest safe call, zero-margin gate, 20.8 deg"
```

- filter on: no crash; closest pass during the save **0.08 m** at t = 3.2 s; minimum over 25 s 0.08 m (filter takes over at t = 1.5 s, hands back at 4.8 s, 8 takeovers in all)
- filter off (`--off`): **crashes** at t = 2.7 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 0.5 deg closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -243.10,265.00,57.05,45.00,0.000,68.690,0.000,0.70 --cinematic --cam 0 --paths --label "02b-wall-beside-angle: unverified twin, 21.3 deg"
```

- filter on: **crashes** at t = 1.7 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 1.50 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -243.10,265.00,57.05,45.00,0.000,72.280,0.000,0.70 --lead 1.5 --cinematic --cam 0 --paths --label "02b-wall-beside-angle: closest call, deployed gate, 17.7 deg"
```

- filter on: no crash; closest pass during the save **3.97 m** at t = 3.2 s; minimum over 25 s 3.97 m (filter takes over at t = 1.5 s, hands back at 3.4 s, 6 takeovers in all)
- filter off: **crashes** at t = 2.8 s (filter never takes over; start not verified)

