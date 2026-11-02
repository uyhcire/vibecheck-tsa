"""Reference trajectories for the proposed speed-scheduled heading hold (docs/escape-law-terminal.md, proposal):
the terminal law with KPSI scaled by max(1, V/35.2), from start B (the level-off) and start C (level-off with a
0.3 rad bank), surfaces and position bit patterns every 512 frames and the FNV-1a hash of all frames."""
import numpy as np
from tsmap import TsMap
from terminal import NEW

STARTS = [("B", (0.0, 0.0, 950.0, 40.0, 0.1, np.pi / 2, 0.0, 1.0, 1.0), 5120),
          ("C", (0.0, 0.0, 950.0, 40.0, 0.1, np.pi / 2, 0.3, 1.0, 1.0), 6400)]
m = TsMap()
m.cand(**dict(NEW, kpsiV=35.2))
for name, a, n in STARTS:
    print(f"## start {name}, proposed law, {n} frames: startPlane{tuple(round(float(v), 6) for v in a)}")
    for ln in m.reftraj(*a, n, 512):
        print(ln)
