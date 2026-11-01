"""Exact (Lean inT) one-tick invariance test of T v3 from kink-aware corner samples."""
import numpy as np, sys, kinv
from kinv import *
n = int(sys.argv[1]); tot = bad = un = nc = 0; hb = []
for r, fl, fp in [(6.0*0.999, 1.05, 1.05), (6.0*0.99, 1.0, 1.0), (6.0, 1.08, 0.5), (5.0, 1.08, 1.08), (6.0*0.995, 0.5, 1.08)]:
    X = ksample(n, r=r, fl=fl, fp=fp)
    img, safe, cl, t0, t1 = ticks_T(X)
    m = t0; tot += m.sum(); bad += (m & ~t1).sum(); un += (m & ~safe).sum(); nc += (m & ~cl).sum()
    hb += list(X[m & ~t1][:,1] / 65536)
    print(f"r {r:.3f} fl {fl} fp {fp}: in T {m.sum()}/{n}; leaves {(m & ~t1).sum()}; unsafe {(m & ~safe).sum()}; noclimb {(m & ~cl).sum()}", flush=True)
print("total in T", tot, "exits", bad, "unsafe", un, "noclimb", nc, "exit h", np.round(sorted(hb))[:20])
