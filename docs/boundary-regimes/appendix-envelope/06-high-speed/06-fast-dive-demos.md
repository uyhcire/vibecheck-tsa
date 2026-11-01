### Fast dive at the park (06-fast-dive)

**Closest proven-safe call** (pilot lead-in 3.00 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,52.40,63.12,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "Fast dive at the park: closest proven-safe call, airspeed = 63.1 m/s"
```

- filter on: no crash; closest pass during the save **4.0 m** at t = 5.0 s; minimum over 25 s 4.0 m (filter takes over at t = 1.4 s, hands back at 1.4 s, 16 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.8 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 4.0 m/s closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,52.40,67.12,-35.000,90.000,0.000,0.60 --cinematic --paths --label "Fast dive at the park: just inside, airspeed = 67.1 m/s: no verified escape"
```

- filter on: **crashes** at t = 1.8 s (filter takes over at t = 0.0 s; start not verified)

