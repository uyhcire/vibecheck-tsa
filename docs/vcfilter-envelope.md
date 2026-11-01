# The envelope filter behind the C ABI

The first implementation of `docs/filter-interface.md`: `c/vcfilter.h` (ABI), `c/filter_abi.c` (shim), `VcFilter/` (Lean adapter), `host/` (Python host, tests).

```
make filter-lib    # .lake/build/lib/libvcfilter.dylib (self-contained, exports only vc_*) and libvcfilter.a
make filter-test   # host/conformance.py, then host/lockstep.py --episodes 100 (needs .venv with jsbsim)
```

`libvcfilter.a` holds the shim and the filter's Lean code; a static host also links `-lInit -lStd -lleanrt -lgmp -luv -lc++` from the Lean toolchain. The library defines no `main`; the first `vc_filter_new` initialises the Lean runtime under `pthread_once`, and the shim calls `lean_initialize_thread` on any other thread that ticks a handle.

## Observation → `Envelope.State`

Exact: each double is decoded from its IEEE-754 bit pattern into the rational it denotes (`VcFilter.ratOfFloat`), so no rounding argument is needed. Non-finite values, or a `valid_mask` missing a required bit (`POS | VEL | AIRSPEED`), give `VC_ERR_BAD_OBS`.

| `State` | `vc_obs` |
| --- | --- |
| `x` | `pos[0]` (m along the track; the terrain grid's axis) |
| `h` | `pos[2]` (m above the terrain grid's datum) |
| `vx` | `vel[0]` (ground speed along the track) |
| `vz` | `vel[2]` (up) |
| `V` | `airspeed` (true airspeed; a field appended to the design's `vc_obs`) |

## Pilot command → envelope input

The filter consumes `VC_CMD_SURFACES`. `Envelope` is generic in the pilot input `ι`; the adapter uses `Envelope.Checks.Stick`: an elevator command at or below `holdElevatorMax` (default 0; elevator + is nose down, JSBSim's sign) is `hold`, anything else is `dive`. The class only selects which free-flight bound (`P.free`) the escape check and the monitor use; the applied command is the pilot's command itself.

## Applied command and verdict

- Mode `free` after `Envelope.filter`: `applied` is the pilot command, copied bit for bit; verdict `PASS`. This includes the hand-back from an escape, which happens as soon as `escapeClear` certifies the pilot's input.
- Mode `escape k`: `applied.kind = VC_CMD_ESCAPE`, `throttle = 1`, every other field 0; verdict `ESCAPE`. This is a high-level demand: the host's escape autopilot flies wings level, pulls and climbs at full throttle. `info.escape_pull`, `escape_climb`, `escape_vmin` state what the theorem assumes the escape achieves at the current airspeed (`P.perf V`, `P.vMin`); the monitor checks it.
- `ADJUSTED` is never produced (the envelope filter passes or overrides).
- Error fallback: the escape (committed if not already). There is no other safe fixed command for this filter.

## Monitor

Each tick checks the previous transition `(applied mode, state, pilot class) → state` with `Envelope.monitor` (`monitor_iff`: exactly `Allowed`). On failure the verdict is `MONITOR_FAIL` (the applied command is still the filter's choice), and `monitor_flags` names the failing `Allowed` clauses (`VC_MON_*`, bits 0-6; `VcFilter.clauseFlags_zero_iff_monitor` ties them to `monitor`). Bit 7: the first state after reset is outside `Init`. Bit 8: bad observation. Bit 9: a substep state passed to `vc_filter_tick_substeps` fails `Envelope.substepOK` (left the tick's swept box; `never_hit_substeps` covers substeps only while this holds). `vc_filter_tick` checks no substeps. The same bits shifted by 16 are latched until `vc_filter_reset`: once set, `never_hit` no longer covers the flight.

`margin` (m, ≥ 0) is the smallest worst-case terrain slack, beyond `margin + sag`, along the escape the filter relies on now (reporting only).

## Parameters

Default `Envelope.Checks.P0` (illustrative numbers, not fitted). `params_path` names a JSON object overriding any field of `Params` by name, numbers as JSON numbers (read as exact decimals) or `"p/q"` strings, plus `holdElevatorMax` (`null`: every input is `dive`); parameters that are not `WellFormed` are rejected (`VC_ERR_BAD_CONFIG`). Example: `{"margin": 15, "free": {"hold": {"vzDrop": "1/2"}}, "terrain": {"w": 25, "cells": [0, 40, 120]}}`.
