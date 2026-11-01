import numpy as np, sample as sm
from sample import *
import os; sm.GsN = np.load(os.environ.get("GFILE", "GsN_fit.npy"))
import sys; h = float(sys.argv[1]); c = center(h)
rng = np.random.default_rng(5)
U = rng.normal(size=(6, 7))
for u in U:
    out = []
    for a in [-2, -1, 1, 2]:
        y = u / np.sqrt(u @ Pat(h) @ u) * a
        x = c.copy(); x[0] = 0; x[1] = h*65536; x[11] = 0
        x[yidx] = c[yidx] + y*Sy; x[gidx] = c[gidx] + (Gat(h) @ y)*Sg; x[20] = c[20]
        img, *_ = ticks(np.array([np.round(x).astype(np.int64)]))
        h1, y1, e1 = coords(img[0])
        out.append(f"{a}: wdot {e1[2]:+.3f} au {e1[4]:+.3f} au1 {e1[7]:+.3f}")
    print(" | ".join(out))
