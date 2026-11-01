### Dive at the park (01b-park-dive)

**Closest proven-safe call** (pilot lead-in 3.00 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,40.40,50.00,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "Dive at the park: closest proven-safe call, height above the park = 33.0 m"
```

- filter on: no crash; closest pass during the save **3.8 m** at t = 8.5 s; minimum over 25 s 3.8 m (filter takes over at t = 2.4 s, hands back at 2.4 s, 13 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.5 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 8.0 m closer than the proven-safe marker, no lead-in. The filter has no verified escape at the start, so it commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,32.40,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --label "Dive at the park: just inside, height above the park = 25.0 m: no verified escape"
```

- filter on: **crashes** at t = 0.9 s (filter takes over at t = 0.0 s; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,18.70,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --label "Dive at the park: proven unsafe, height above the park = 11.3 m"
cargo run --release --features jsb -- --env gate --time-cap 0 --start -360.00,260.00,18.70,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --off --label "Dive at the park: proven unsafe, height above the park = 11.3 m"
```

- filter on: **crashes** at t = 0.2 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.2 s (filter never takes over; start not verified)
- the filter's escapes flown with no margin: 6 of 6 touch (straight hits at 0.2 s, left hits at 0.2 s, right hits at 0.2 s, left40 hits at 0.2 s, right40 hits at 0.2 s, street hits at 0.2 s)

