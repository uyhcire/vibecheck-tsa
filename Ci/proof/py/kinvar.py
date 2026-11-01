"""Exact (Lean inT) one-tick invariance test of T v3 from kink-aware corner samples."""
import numpy as np, sys, kinv
from kinv import *
n = int(sys.argv[1]); tot = bad = un = nc = 0; hb = []
for r, fl, fp in [(R*0.999, 0.999, 0.999), (R*0.99, 0.99, 0.5), (R*0.9, 0.5, 0.99), (R*0.6, 0.99, 0.99), (R*0.995, 0.3, 0.3)]:
    X = ksample(n, r=r, fl=fl * float(os.environ.get("SAFE", "1.25")), fp=fp * float(os.environ.get("SAFE", "1.25")))
    img, safe, cl, t0, t1 = ticks_T(X)
    m = t0; tot += m.sum(); bad += (m & ~t1).sum(); un += (m & ~safe).sum(); nc += (m & ~cl).sum()
    hb += list(X[m & ~t1][:,1] / 65536)
    print(f"r {r:.3f} fl {fl} fp {fp}: in T {m.sum()}/{n}; leaves {(m & ~t1).sum()}; unsafe {(m & ~safe).sum()}; noclimb {(m & ~cl).sum()}", flush=True)
print("total in T", tot, "exits", bad, "unsafe", un, "noclimb", nc, "exit h", np.round(sorted(hb))[:20])
