import numpy as np, sys, subprocess, boxes3
from boxes3 import *
w = float(sys.argv[1]); depth = sys.argv[2]
cells = [(a, min(a + w, 2640)) for a in np.arange(10, 2640, w)]
lines = []
for ha, hb in cells:
    lo, hi, d = cellbox(ha, hb)
    lines.append(" ".join(str(int(v)) for v in list(lo) + list(hi) + [d[4], d[5]]))
import time; t = time.time()
out = subprocess.run([EXE, "safecheck", depth], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.strip().split("\n")
for (ha, hb), r in zip(cells, out):
    print(f"{ha:.0f}-{hb:.0f}: {r}")
print("time", round(time.time() - t, 1))
