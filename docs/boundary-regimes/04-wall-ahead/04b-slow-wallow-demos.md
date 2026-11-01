### Slow wallow toward the park-side tower (04b-slow-wallow)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 2.50 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -412.21,295.00,47.51,27.00,6.000,0.000,0.000,0.25 --lead 2.5 --cinematic --cam 0 --paths --label "04b-slow-wallow: closest safe call, zero-margin gate, 194.1 m"
```

- filter on: no crash; closest pass during the save **15.63 m** at t = 0.0 s; minimum over 25 s 0.00 m (filter takes over at t = 0.0 s, hands back at 9.6 s, 9 takeovers in all)
- filter off (`--off`): **crashes** at t = 10.6 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 128.0 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -284.21,295.00,47.07,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --label "04b-slow-wallow: unverified twin, 66.1 m"
```

- filter on: **crashes** at t = 2.3 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 2.50 s):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -412.21,295.00,47.51,27.00,6.000,0.000,0.000,0.25 --lead 2.5 --cinematic --cam 0 --paths --label "04b-slow-wallow: closest call, deployed gate, 194.1 m"
```

- filter on: no crash; closest pass during the save **15.63 m** at t = 0.0 s; minimum over 25 s 4.09 m (filter takes over at t = 0.0 s, hands back at 9.6 s, 9 takeovers in all)
- filter off: **crashes** at t = 10.6 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -231.90,295.00,46.75,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --label "04b-slow-wallow: proven unsafe, 13.8 m"
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -231.90,295.00,46.75,27.00,6.000,0.000,0.000,0.25 --cinematic --cam 0 --paths --off --label "04b-slow-wallow: proven unsafe, 13.8 m"
```

- filter on: **crashes** at t = 0.3 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.3 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.3 s, left hits at 0.3 s, right hits at 0.3 s, left40 hits at 0.3 s, right40 hits at 0.3 s, street hits at 0.3 s)

