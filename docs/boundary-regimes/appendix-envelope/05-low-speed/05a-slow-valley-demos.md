### Slow and low over the valley (05a-slow-valley)

**Closest proven-safe call** (pilot lead-in 0.00 s, sticks released: the fly-by-wire holds flight path and bank):

```sh
cargo run --release --features jsb -- --safety-filter exact-rollout --time-cap 0 --start 0.00,-1600.00,21.85,24.80,8.000,0.000,0.000,0.00 --lead 0 --cinematic --cam 0 --paths --label "Slow and low over the valley: closest proven-safe call, airspeed = 24.8 m/s"
```

- filter on: no crash; closest pass during the save **7.7 m** at t = 0.1 s; minimum over 25 s 4.0 m (filter takes over at t = 0.1 s, hands back at 0.1 s, 175 takeovers in all)
- filter off (`--off`): **crashes** at t = 5.8 s (filter never takes over; start not verified)

**Twin**: no start between the proven-safe marker and the outer bound crashed with the filter on (its blind fallback escape survived every one tried).

