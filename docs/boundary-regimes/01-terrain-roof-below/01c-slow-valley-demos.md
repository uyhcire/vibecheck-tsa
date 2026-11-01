### Slow and low over the valley (01c-slow-valley)

**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `--margin 0 --check-every 1`; pilot lead-in 0.00 s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --margin 0 --check-every 1 --start 0.00,-1600.00,21.85,20.40,8.000,0.000,0.000,0.00 --lead 0 --cinematic --cam 0 --paths --label "01c-slow-valley: closest safe call, zero-margin gate, 20.4 m/s"
```

- filter on: no crash; closest pass during the save **0.16 m** at t = 5.6 s; minimum over 25 s 0.09 m (filter takes over at t = 0.1 s, hands back at 11.9 s, 2 takeovers in all)
- filter off (`--off`): **crashes** at t = 3.6 s (filter never takes over; start not verified)

**Twin**: no start between the proven-safe marker and the outer bound (or the slice's end) crashed under the zero-margin gate: its blind fallback escape survived every one tried.

**The deployed gate (4 m margin)** from its own acceptance marker (lead-in 0.00 s):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start 0.00,-1600.00,21.85,24.80,8.000,0.000,0.000,0.00 --lead 0 --cinematic --cam 0 --paths --label "01c-slow-valley: closest call, deployed gate, 24.8 m/s"
```

- filter on: no crash; closest pass during the save **7.74 m** at t = 0.1 s; minimum over 25 s 4.01 m (filter takes over at t = 0.1 s, hands back at 0.8 s, 12 takeovers in all)
- filter off: **crashes** at t = 5.8 s (filter never takes over; start not verified)

