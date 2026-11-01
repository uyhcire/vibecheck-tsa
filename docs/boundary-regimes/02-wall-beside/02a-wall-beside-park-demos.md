### Beside the park-side tower (02a-wall-beside-park)

**Closest proven-safe call** (pilot lead-in 1.50 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -234.10,265.00,57.00,45.00,0.000,80.000,0.000,0.70 --lead 1.5 --cinematic --cam 0 --paths --label "Beside the park-side tower: closest proven-safe call, distance to the face = 16.0 m"
```

- filter on: no crash; closest pass during the save **4.0 m** at t = 3.2 s; minimum over 25 s 4.0 m (filter takes over at t = 1.0 s, hands back at 1.5 s, 7 takeovers in all)
- filter off (`--off`): **crashes** at t = 2.7 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 4.0 m closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -230.10,265.00,56.98,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --label "Beside the park-side tower: just inside, distance to the face = 12.0 m: no verified escape"
```

- filter on: **crashes** at t = 0.8 s (filter takes over at t = 0.0 s; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -218.60,265.00,56.92,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --label "Beside the park-side tower: proven unsafe, distance to the face = 0.5 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -218.60,265.00,56.92,45.00,0.000,80.000,0.000,0.70 --cinematic --cam 0 --paths --off --label "Beside the park-side tower: proven unsafe, distance to the face = 0.5 m"
```

- filter on: **crashes** at t = 0.0 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.0 s (filter never takes over; start not verified)
- the filter's escapes flown with no margin: 6 of 6 touch (straight hits at 0.0 s, left hits at 0.0 s, right hits at 0.0 s, left40 hits at 0.0 s, right40 hits at 0.0 s, street hits at 0.0 s)

