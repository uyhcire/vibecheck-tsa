### Dive at the park (01b-park-dive)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 3.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -360.00,260.00,36.14,50.00,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01b-park-dive: closest safe call, zero-margin gate, 28.7 m"
```

- filter on: no crash; closest pass during the save **0.04 m** at t = 6.6 s; minimum over 25 s 0.04 m (filter takes over at t = 2.4 s, hands back at 4.9 s, 2 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.4 s (filter never takes over; start not verified)

**Just-barely-unsafe twin**: 0.5 m closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start -360.00,260.00,35.64,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --label "01b-park-dive: unverified twin, 28.2 m"
```

- filter on: **crashes** at t = 1.3 s (filter takes over at t = 0.0 s; start not verified)

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 3.00 s):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -360.00,260.00,40.40,50.00,-35.000,90.000,0.000,0.60 --lead 3 --cinematic --paths --label "01b-park-dive: closest call, deployed gate, 33.0 m"
```

- filter on: no crash; closest pass during the save **3.87 m** at t = 6.5 s; minimum over 25 s 3.87 m (filter takes over at t = 2.4 s, hands back at 4.6 s, 4 takeovers in all)
- filter off: **crashes** at t = 3.5 s (filter never takes over; start not verified)

**Closest proven-unsafe call**:

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -360.00,260.00,13.28,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --label "01b-park-dive: proven unsafe, 5.9 m"
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start -360.00,260.00,13.28,50.00,-35.000,90.000,0.000,0.60 --cinematic --paths --off --label "01b-park-dive: proven unsafe, 5.9 m"
```

- filter on: **crashes** at t = 0.0 s (filter takes over at t = 0.0 s; start not verified)
- filter off: **crashes** at t = 0.0 s (filter never takes over; start not verified)
- the gate's escapes flown with no margin: 6 of 6 touch (straight hits at 0.0 s, left hits at 0.0 s, right hits at 0.0 s, left40 hits at 0.0 s, right40 hits at 0.0 s, street hits at 0.0 s)

