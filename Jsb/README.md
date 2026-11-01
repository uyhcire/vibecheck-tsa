# Jsb: a fixed-point Lean port of JSBSim's Cessna 172 longitudinal model

An executable Lean model of the longitudinal (pitch plane) dynamics of JSBSim's `c172p`, written in the same `Fx` fixed point as `Vibecheck/`. It serves as a measurement baseline and a candidate proof target for swappable safety filters. It is **not part of the verified core**: nothing in `Vibecheck/` imports it and no theorem depends on it yet.

## What it contains

| File | Content |
| --- | --- |
| `C172Aero.lean` | Generated: aircraft constants, aero function tables and the DRAG, LIFT and PITCH axes from `c172p.xml`, the IO-320 engine and the 75-inch propeller |
| `Math.lean` | Deterministic helpers: floor division, table interpolation, square root, arctangent |
| `Model.lean` | `State`, `Input`, and `tickAB`, one 1/16 s tick as JSBSim runs it: 8 steps of 1/128 s with JSBSim's integrators (Adams-Bashforth 3 for altitude, Adams-Bashforth 2 for velocity, rectangular Euler for attitude), the piston engine and the fixed-pitch propeller. `tickEuler` is a coarser variant (4 forward-Euler steps of 1/64 s) |

`Jsb.State` carries every value JSBSim holds between steps (manifold pressure lag, stall hysteresis, previous accelerations), so one Lean tick from a logged state is directly comparable with JSBSim's next logged state.

## What it omits

- Lateral dynamics: bank (`phi`) and sideslip (`beta`) are not state; they are optional inputs of `Jsb.Input` (default 0).
- Fuel burn and mass changes, flaps, gear, ground contact, wind and turbulence.
- Mixture control: the mixture is fixed at the value `sysid/collect.py` sets.
- JSBSim's atmosphere model: density, pressure, temperature and speed of sound are read from 50 m spaced tables of the standard atmosphere, clamped at 0 m and 7950 m.
- Trigonometry: `cosSmall` and `sinSmall` are series valid for small angles; attitude is a unit vector `(dx, dz)`, not an angle.

## Regenerate

`C172Aero.lean` is generated from the XML files shipped with the `jsbsim` Python package; do not edit it by hand.

```
python3 -m venv .venv && .venv/bin/pip install -r sysid/requirements.txt
.venv/bin/python -I sysid/xml2lean.py          # rewrites Jsb/C172Aero.lean
lake build Jsb jsbresid jsbbench
```

The generator raises on any function element or property it does not know, so nothing is dropped silently.

## Measure residuals

```
.venv/bin/python -I sysid/collect.py /tmp/t.csv 10 600 2 rud0
.lake/build/bin/jsbresid /tmp/t.csv            # wings level, sideslip 0
.lake/build/bin/jsbresid /tmp/t.csv --lat      # measured bank and sideslip fed in as inputs
.lake/build/bin/jsbresid /tmp/t.csv --dump /tmp/res.csv && .venv/bin/python -I sysid/breach.py /tmp/res.csv /tmp/t.csv
```

`collect.py` flies the real `c172p` with random stick and throttle, a wings-leveler and (with `rud0`) the rudder centred, and logs every 1/16 s tick. `jsbresid` runs one Lean tick from each logged state and prints quantiles of the absolute error against JSBSim's next logged state. `--diag` compares intermediate aerodynamic and propeller quantities instead; `jsbbench` times the main pieces. `sysid/breach.py` calibrates a per-tick residual bound on half the episodes and counts breaches on the other half.

## Measured residuals

Worst case (max of `|Lean - JSBSim|`) over one tick, rudder centred, `jsbresid` defaults (first 4 ticks of each flight skipped):

| Data | Run | vx (m/s) | vz (m/s) | q (rad/s) |
| --- | --- | --- | --- | --- |
| 10 flights, 3441 tick pairs | default | 0.0138 | 0.0180 | 0.0028 |
| 10 flights, 3441 tick pairs | `--lat` | 0.0028 | 0.0011 | 0.0013 |
| 200 flights, 76419 tick pairs | default | 0.0209 | 0.0197 | 0.0060 |
| 200 flights, 76419 tick pairs | `--lat` | 0.0084 | 0.0028 | 0.0028 |

(`collect.py ... 200 1200 2 rud0` for the larger set.) Position residuals are below 1e-3 m per tick. Without the measured bank and sideslip, the residual is dominated by the lateral state the model omits; with it, vz stays under 0.003 m/s. The maximum grows slowly with the number of flights, so the larger set is the better estimate of a worst case.
