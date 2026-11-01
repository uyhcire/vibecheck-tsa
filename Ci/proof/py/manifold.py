"""Slow manifold of the lawfirst climb: the state as a function of h, read off long trajectories."""
import numpy as np
from pf import *
tr, _ = bench_traj(0, 600)
x0 = tr[500].copy(); x0[0] = 0
F = lambda r: r / 65536
for h0 in [5, 30, 3600]:
    x = x0.copy(); x[1] = h0 * 65536
    t = traj(x, 30000)
    print("start h0", h0)
    for k in [0, 50, 100, 200, 300, 400, 600, 1000, 3000, 10000, 30000]:
        r = t[k]
        print(f"  k {k:5d} h {F(r[1]):8.2f} vx {F(r[2]):.4f} vz {F(r[3]):.4f} dz {F(r[5]):.5f} q {r[6]} rpm {F(r[7]):.1f} tmap {F(r[8]):.3f} eI {r[19]} ac {r[20]}")
    np.save(f"traj_{h0}.npy", t)
