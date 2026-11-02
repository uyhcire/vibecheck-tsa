"""Climb-to-level handover under the new law: from settled-climb states perturbed within the climb's settled box,
crossing zTop, the minimum altitude reached after first passing zTop (numerical evidence, not a proof)."""
import numpy as np
from tsmap import TsMap
from terminal import NEW
from design import reference, c_at
from trim import SCALE

ZTOP = 934.0
m = TsMap(); m.smooth(True)
m.cand(**dict(NEW, hLevel=float("nan")))
ref = reference(m, 10.0, 1000.0)
m.cand(**NEW)
rng = np.random.default_rng(5)
worst = 1e9; n = 0
idx = {"v_al": 3, "v_dn": 5, "phi": 0, "dpsi": 2}
for h0 in (900.0, 930.0, 960.0):
    for k in range(10):
        y = c_at(ref, h0).copy()
        y[3] += rng.uniform(-0.5, 0.5); y[5] += rng.uniform(-0.5, 0.5)
        y[0] += rng.uniform(-0.02, 0.02); y[2] += rng.uniform(-0.02, 0.02)
        rows = m.sim(h0, y, 128 * 120, 16)
        h = rows[:, 3]
        above = np.where(h >= ZTOP)[0]
        if len(above):
            worst = min(worst, h[above[0]:].min()); n += 1
print(f"{n} runs crossing zTop = {ZTOP} m: lowest altitude after first reaching it {worst:.2f} m; final altitude ~{h[-1]:.2f} m")
