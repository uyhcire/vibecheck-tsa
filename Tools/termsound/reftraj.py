"""Reference trajectories for docs/escape-law-terminal.md: the straight escape under the gate's law and under the
new terminal phase, from two starts, with surfaces and position bit patterns every 256 frames and an FNV-1a hash."""
import numpy as np
from tsmap import TsMap
from terminal import NEW

STARTS = [("A", (0.0, 0.0, 150.0, 30.0, -0.1, np.pi / 2, 0.4, 1.0, 1.0), 2048),
          ("B", (0.0, 0.0, 950.0, 40.0, 0.1, np.pi / 2, 0.0, 1.0, 1.0), 5120)]
m = TsMap()
for law in ("gate", "new"):
    if law == "gate":
        m.gate()
    else:
        m.cand(**NEW)
    for name, a, n in STARTS:
        print(f"## start {name}, {law} law, {n} frames: startPlane{tuple(round(float(v), 6) for v in a)}")
        for ln in m.reftraj(*a, n, 256):
            print(ln)
