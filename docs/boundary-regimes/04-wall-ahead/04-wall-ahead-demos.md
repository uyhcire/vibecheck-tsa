### Wall ahead across the park (04-wall-ahead)

**Closest proven-safe call** (pilot lead-in 1.75 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -406.08,295.00,57.50,45.00,0.000,0.000,0.000,0.70 --lead 1.75 --cinematic --cam 0 --paths --label "Wall ahead across the park: closest proven-safe call, distance to the face = 188.0 m"
```

- filter on: no crash; closest pass during the save **14.4 m** at t = 7.6 s; minimum over 25 s 6.6 m (filter takes over at t = 1.7 s, hands back at 1.8 s, 19 takeovers in all)
- filter off (`--off`): **crashes** at t = 5.7 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 4.0 m closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -402.08,295.00,57.50,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --label "Wall ahead across the park: just inside, distance to the face = 184.0 m: no verified escape"
```

- filter on: **crashes** at t = 5.8 s (filter takes over at t = 0.0 s; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -246.07,295.00,56.84,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --label "Wall ahead across the park: proven unsafe, distance to the face = 28.0 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -246.07,295.00,56.84,45.00,0.000,0.000,0.000,0.70 --cinematic --cam 0 --paths --off --label "Wall ahead across the park: proven unsafe, distance to the face = 28.0 m"
```

- filter on: **crashes** at t = 0.5 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.5 s (filter never takes over; start not verified)
- the filter's escapes flown with no margin: 6 of 6 touch (straight hits at 0.6 s, left hits at 0.6 s, right hits at 0.6 s, left40 hits at 0.6 s, right40 hits at 0.6 s, street hits at 0.6 s)

