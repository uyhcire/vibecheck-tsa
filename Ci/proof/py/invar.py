"""Empirical invariance of the Lean terminal set: sample states in T, tick once, test T again."""
import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
base = np.array([0.094,0.189,2.378,0.331,2.366,0.088,0.355,2.477,0.019,0.039,0.022]) / 3
tolu = 2.0 * base * 6 + np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02])
tot = 0; bad = 0; hb = []
for rfrac, egfrac in [(1.0, 0.0), (0.98, 0.5), (0.9, 0.9), (0.5, 0.99), (1.0, 0.99)]:
    X = sm.sample(3000, 6.0 * rfrac, tolu * egfrac)
    img, safe, cl, t0, t1 = ticks_T(X)
    m = t0
    print(f"r {6*rfrac:.2f} eg {egfrac}: in T {m.sum()}/{len(X)}; image leaves T {(m & ~t1).sum()}; unsafe {(m & ~safe).sum()}; noclimb {(m & ~cl).sum()}")
    for x, xi, a, b in zip(X, img, t0, t1):
        if a and not b: hb.append(x[1] / 65536)
print("altitudes of exits (m):", np.round(np.quantile(hb, [0, 0.25, 0.5, 0.75, 1]), 0) if hb else None)
