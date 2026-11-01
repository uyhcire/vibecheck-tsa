### Closing on the park-side tower at an angle (02b-wall-beside-angle)

**Closest proven-safe call** (pilot lead-in 1.50 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -243.10,265.00,57.05,45.00,0.000,72.280,0.000,0.70 --lead 1.5 --cinematic --cam 0 --paths --label "Closing on the park-side tower at an angle: closest proven-safe call, heading angle into the face = 17.7 deg"
```

- filter on: no crash; closest pass during the save **3.9 m** at t = 3.3 s; minimum over 25 s 3.9 m (filter takes over at t = 1.1 s, hands back at 1.8 s, 7 takeovers in all)
- filter off (`--off`): **crashes** at t = 2.8 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 4.0 deg closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -243.10,265.00,57.05,45.00,0.000,68.280,0.000,0.70 --cinematic --cam 0 --paths --label "Closing on the park-side tower at an angle: just inside, heading angle into the face = 21.7 deg: no verified escape"
```

- filter on: **crashes** at t = 1.6 s (filter takes over at t = 0.0 s; start not verified)

