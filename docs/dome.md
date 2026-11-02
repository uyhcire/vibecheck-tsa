# The circle-safe dome

The dome is the terminal set of the city gate drawn as a surface over the city. `make dome` computes it.

**Definition.** `helix_check` in `flight/src/envfilter.rs` accepts a steady climbing circle with centre `c`, radius `r` and drift margin `m` at altitude `z` when every raw raster cell under the annulus `r ± (m + R_BODY)` is at least `R_BODY + MARGIN` (4.5 m + 4 m) below `z`, or `z` is that far above the map's top; the annulus must also stay on the map. The dome height `D_r(c)` is the least `z` at which it passes:

`D_r(c) = min(zTop, max raw cell under the annulus + R_BODY + MARGIN)`, and `zTop` wherever the annulus leaves the map.

The ceiling is `zTop = map top + R_BODY + MARGIN = 926.70 + 4.5 + 4 = 935.20 m`. The map is `World::new(1337)` with its 2.5 m raw raster (terrain and roofs, the raster the gate reads). Any circle of radius `r` centred at `c` that the gate's terminal test would certify is at or above `D_r(c)`.

**Exactness.** The centres are on a 10 m grid, four raster cells, so the annulus covers the same set of cell offsets for every centre and the maximum is exact, not a bound. `make dome` checks it against the real `helix_check` at 300 random centres per radius (`D + 1 mm` passes, `D - 1 cm` fails unless the value is the ceiling); there were no disagreements, and the run asserts none.

**The drift margin `m`.** The terminal test sets `m = 5 + 3 (d_r + d_c)`, where `d_r` and `d_c` are the differences in radius and in centre between the circle fits of the two halves of the settled escape; it rejects the circle unless both are at most 10% of the radius. The dome uses `d_r + d_c = 0.1 r`, so **`m = 5 + 0.3 r`: 47.9 m at r = 143 m, 80.0 m at r = 250 m.** This is a chosen value (the test does not fix one): half the loosest agreement the test accepts. The tables below the main ones show the two ends (`m = 5`, perfect agreement; `m = 5 + 0.6 r`, the loosest accepted). The dome rises with `m`.

**Radii.** r = 143 m (a typical 40 degree circle at about 35 m/s, observed in a real takeover) and r = 250 m (40 degrees at about 45 m/s).

## Files

`make dome` (default `OUT=/tmp/dome`; `OUT=dir` to choose) writes, deterministically, in about a minute:

| File | Contents |
|---|---|
| `dome_r143.f32`, `dome_r250.f32` | `D_r` in metres, 601 x 601 little-endian float32, row-major |
| `dome_r143.json`, `dome_r250.json` | The header for each grid (origin, spacing, nx, ny, r, m, units, `z_top`) |
| `dome_r{143,250}_map.png`, `_city.png` | Heat-map of `D_r` (metres above the world's datum), whole map and the city square (+-1300 m) with building outlines |
| `dome_r{143,250}_agl_map.png`, `_agl_city.png` | The same showing height above the local terrain, `D_r - terrain`, colour scale 0 to 500 m; cells at the ceiling are grey |
| `dome_stats.md` | The stats below, including the sensitivity tables |

The grids are not committed (1.4 MB each); the PNGs are, in `docs/dome/`. The PNGs label the colour bar in metres; grey is the ceiling (`zTop`). Axes: north is up, the map is 6000 m across and the city square 2400 m.

**Reading the grid** (the header is a sidecar JSON, so the `.f32` is raw floats; no header bytes to skip). Node `(i, j)` is the centre `x = -3000 + 10 i`, `y = -3000 + 10 j` (world metres, the frame of the recorded footage; `y` is north, `z` is up), `i, j = 0..600`, stored at index `j * 601 + i`. `D` is the altitude `z` in the same frame.

```python
import json, numpy as np
h = json.load(open("dome_r143.json"))
D = np.fromfile("dome_r143.f32", "<f4").reshape(h["ny"], h["nx"])   # D[j, i]
x = h["origin"][0] + h["spacing"] * np.arange(h["nx"]); y = h["origin"][1] + h["spacing"] * np.arange(h["ny"])
```

```js
const h = await (await fetch("dome_r143.json")).json();
const D = new Float32Array(await (await fetch("dome_r143.f32")).arrayBuffer());   // D[j * h.nx + i]
```

To overlay on a frame, draw the surface `z = D(x, y)` (a 601 x 601 vertex grid, two triangles per cell) through the frame's `view_proj`; bilinear interpolation between nodes is what the PNGs use. `dome_r143.f32` is the dome for circles centred at `(x, y)`, so the surface is the height a circle centred over that point must clear, not an envelope around the aircraft.

## Results

Fractions are over the 601 x 601 centre nodes (equal area per node), AGL = `D_r - terrain` (the true terrain, not the roofs). Regions: the downtown core is within 430 m of the tallest tower's block; the city blocks and streets are the rest of the city square (`|x|, |y| <= 1200 m`) outside the parks; the outskirts are everything outside the city square (hills, the ridge at y = -2050 m, the rim). The map has no water.

### r = 143 m, m = 47.9 m (primary)

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 0.0% | 43.1% | 0.0% | 317 |
| rest of the city blocks and streets | 14.3% | 80.8% | 94.3% | 100.0% | 0.0% | 26 |
| parks | 0.2% | 59.8% | 86.3% | 100.0% | 0.0% | 80 |
| outskirts (outside the city square) | 83.9% | 46.8% | 69.4% | 82.2% | 15.3% | 113 |
| whole map | 100.0% | 50.9% | 71.9% | 84.2% | 12.9% | 96 |

### r = 250 m, m = 80.0 m (primary)

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 0.0% | 2.0% | 0.0% | 459 |
| rest of the city blocks and streets | 14.3% | 67.1% | 83.8% | 97.9% | 0.0% | 45 |
| parks | 0.2% | 44.0% | 57.1% | 90.4% | 0.0% | 108 |
| outskirts (outside the city square) | 83.9% | 36.6% | 55.9% | 68.6% | 25.4% | 163 |
| whole map | 100.0% | 40.4% | 59.0% | 71.8% | 21.3% | 145 |

### The street at the Tower gap and the canyon slice

Height of the dome above the street (`D_r - terrain` at the street centreline, nodes every 10 m):

r = 143 m:

- Tower gap street x = -120, y from -150 to 100: min 352 m, median 459 m, max 459 m; at (-120, -60) (the showcase start): min 377 m, median 377 m, max 377 m
- Canyon slice y = 120, x from -470 to 600: min 174 m, median 353 m, max 460 m; at (-470, 120): min 174 m, median 174 m, max 174 m
- check: 300 random centres against helix_check, 255 below the ceiling, 0 disagreements

r = 250 m:

- Tower gap street x = -120, y from -150 to 100: min 458 m, median 459 m, max 459 m; at (-120, -60) (the showcase start): min 458 m, median 458 m, max 458 m
- Canyon slice y = 120, x from -470 to 600: min 258 m, median 365 m, max 461 m; at (-470, 120): min 262 m, median 262 m, max 262 m
- check: 300 random centres against helix_check, 249 below the ceiling, 0 disagreements

The Tower gap street is `x = -120` (`docs/boundary-regimes/01-terrain-roof-below/`; its 28 m width is between towers 261 m and 292 m tall), sampled from `y = -150` (the dive start) to `y = 100`; `(-120, -60)` is where the showcase starts. The canyon slice `03-canyon` is the street `y = 120`, flown east from `x = -470` (where the slice starts) toward downtown; sampled to `x = 600`. At r = 250 m the 450 m tower at block (10, 10) lies inside the annulus for every centre along both streets that reaches it (for example `(-120, -60)`, 216 m away, where the annulus spans 165.5 m to 334.5 m), which is why the dome there is 458 to 459 m above the street: the tower's top plus `R_BODY + MARGIN` (8.5 m).

### Sensitivity to `m`

**r = 143 m, m = 5 (perfect agreement): m = 5.0 m**

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 7.8% | 65.1% | 0.0% | 283 |
| rest of the city blocks and streets | 14.3% | 85.3% | 97.5% | 100.0% | 0.0% | 25 |
| parks | 0.2% | 66.7% | 93.3% | 100.0% | 0.0% | 60 |
| outskirts (outside the city square) | 83.9% | 52.2% | 74.9% | 96.0% | 12.4% | 91 |
| whole map | 100.0% | 56.1% | 77.1% | 96.1% | 10.4% | 74 |

**r = 143 m, m = 5 + 0.6 r (loosest agreement the test accepts): m = 90.8 m**

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 0.0% | 26.4% | 0.0% | 352 |
| rest of the city blocks and streets | 14.3% | 77.0% | 91.3% | 100.0% | 0.0% | 33 |
| parks | 0.2% | 49.0% | 74.5% | 100.0% | 0.0% | 101 |
| outskirts (outside the city square) | 83.9% | 42.5% | 65.6% | 77.0% | 18.3% | 132 |
| whole map | 100.0% | 46.7% | 68.2% | 79.5% | 15.3% | 114 |

**r = 250 m, m = 5 (perfect agreement): m = 5.0 m**

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 0.6% | 36.0% | 0.0% | 318 |
| rest of the city blocks and streets | 14.3% | 75.7% | 91.1% | 100.0% | 0.0% | 36 |
| parks | 0.2% | 46.4% | 71.2% | 99.6% | 0.0% | 104 |
| outskirts (outside the city square) | 83.9% | 40.9% | 63.4% | 75.2% | 19.7% | 140 |
| whole map | 100.0% | 45.3% | 66.4% | 78.2% | 16.6% | 121 |

**r = 250 m, m = 5 + 0.6 r (loosest agreement the test accepts): m = 155.0 m**

| Region | Share of map | < 100 m | < 200 m | < 300 m | at ceiling | median AGL (m) |
|---|---|---|---|---|---|---|
| downtown core (within 430 m of the tower) | 1.6% | 0.0% | 0.0% | 0.0% | 0.0% | 460 |
| rest of the city blocks and streets | 14.3% | 58.8% | 77.1% | 93.7% | 0.0% | 67 |
| parks | 0.2% | 35.0% | 48.1% | 73.4% | 0.0% | 213 |
| outskirts (outside the city square) | 83.9% | 32.5% | 51.2% | 62.5% | 30.3% | 190 |
| whole map | 100.0% | 35.7% | 54.1% | 66.0% | 25.4% | 170 |

## Reproduce

`make dome` (needs the `libcityjsb` Lean build the other `flight` targets use). `ARGS="--check N"` sets the number of random `helix_check` comparisons (default 300).
