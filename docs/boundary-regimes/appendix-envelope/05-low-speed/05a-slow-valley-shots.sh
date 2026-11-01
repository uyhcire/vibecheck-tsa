mkdir -p docs/boundary-regimes/05-low-speed/shots
flight/target/release/cityflight --safety-filter exact-rollout --time-cap 0 --start 0.00,-1600.00,21.85,24.80,8.000,0.000,0.000,0.00 --lead 0 --cinematic --cam 0 --paths --label "Slow and low over the valley: closest proven-safe call, airspeed = 24.8 m/s" --shot docs/boundary-regimes/05-low-speed/shots/05a-slow-valley-safe.png --frames 12
