### Fast dive at the park (01d-fast-dive)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 3.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -360.00,260.00,52.40,66.88,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01d-fast-dive: closest safe call, zero-margin gate, 66.9 m/s"
```

- filter on: no crash; closest pass during the save **0.01 m** at t = 5.0 s; minimum over 25 s 0.01 m (filter takes over at t = 1.5 s, hands back at 1.6 s, 13 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.8 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 0.5 m/s closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --margin 0 --check-every 1 --start -360.00,260.00,52.40,67.38,-35.000,90.000,0.000,0.60 --cinematic --paths --label "01d-fast-dive: unverified twin, 67.4 m/s"
```

- filter on: **crashes** at t = 1.7 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 3.00 s):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,52.40,63.12,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01d-fast-dive: closest call, deployed gate, 63.1 m/s"
```

- filter on: no crash; closest pass during the save **4.00 m** at t = 5.0 s; minimum over 25 s 4.00 m (filter takes over at t = 1.4 s, hands back at 1.4 s, 16 takeovers in all)
- filter off: **crashes** at t = 3.8 s (filter never takes over; start not verified)

