# sysid: JSBSim residual and tube experiments

Unverified research scripts behind the numbers in `problems/robust-safety/README.md`. They are not part of the Lean build.

```
python3 -m venv .venv && .venv/bin/pip install -r sysid/requirements.txt
.venv/bin/python -I sysid/collect.py sysid/train.csv 120 1200 1   # JSBSim c172p, 16 Hz ticks
.venv/bin/python -I sysid/collect.py sysid/test.csv 60 1200 2
.venv/bin/python -I sysid/fit.py sysid/train.csv sysid/test.csv sysid/resid_ext1.npy 1
.venv/bin/python -I sysid/tvlqr_tube.py                          # tube widths vs D (float port of the 2D model)
```

| Script | Measures |
| --- | --- |
| `collect.py` | flies c172p with random elevator/throttle and a wings-leveler (`rud0`: rudder centred); logs ticks, hidden state and aero diagnostics |
| `fit.py` | fits the 2D model's parameters; residual quantiles per component |
| `regress.py`, `engine.py` | how small residuals can get with flexible regressions; engine thrust predictability |
| `euler_floor.py`, `substep_floor.py` | integration-only error with JSBSim's exact forces |
| `diag.py`, `resid_rate.py` | residual vs bank angle and pitch rate; residual autocorrelation |
| `xml2lean.py` | generates `Jsb/C172Aero.lean` from JSBSim's c172p XML (see `Jsb/README.md`) |
| `breach.py` | held-out breach rate of a residual bound, from `jsbresid --dump` output |
| `tube.py`, `tvlqr_tube.py`, `lowpass_tube.py` | zonotope tube widths for the autoland and a TV-LQR controller under per-tick or bandwidth-limited disturbances |

`tube.py` contains a float copy of the 2D model's flying branch for speed; the Lean model in `Vibecheck/Model.lean` is the reference.
