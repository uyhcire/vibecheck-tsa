### Slow wallow toward the park-side tower (05b-slow-wallow)

**Closest proven-safe call** (pilot lead-in 2.50 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -412.21,295.00,47.51,27.00,6.000,0.000,0.000,0.25 --lead 2.5 --cinematic --cam 0 --paths --label "Slow wallow toward the park-side tower: closest proven-safe call, distance to the face = 194.1 m"
```

- filter on: no crash; closest pass during the save **15.6 m** at t = 0.0 s; minimum over 25 s 4.0 m (filter takes over at t = 0.0 s, hands back at 9.2 s, 41 takeovers in all)
- filter off (`--off`): **crashes** at t = 10.6 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 128.0 m closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -284.21,295.00,47.07,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --label "Slow wallow toward the park-side tower: just inside, distance to the face = 66.1 m: no verified escape"
```

- filter on: **crashes** at t = 2.3 s (filter takes over at t = 0.0 s; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -231.90,295.00,46.75,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --label "Slow wallow toward the park-side tower: proven unsafe, distance to the face = 13.8 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -231.90,295.00,46.75,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --off --label "Slow wallow toward the park-side tower: proven unsafe, distance to the face = 13.8 m"
```

- filter on: **crashes** at t = 0.3 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.3 s (filter never takes over; start not verified)
- the filter's escapes flown with no margin: 6 of 6 touch (straight hits at 0.4 s, left hits at 0.4 s, right hits at 0.4 s, left40 hits at 0.4 s, right40 hits at 0.4 s, street hits at 0.4 s)

