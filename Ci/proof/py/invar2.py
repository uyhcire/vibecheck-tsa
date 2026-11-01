"""Empirical invariance of the Lean terminal set (exact Int inT): sample, tick, re-test."""
import numpy as np, sys, os, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy"); tolN = np.load("tolN.npy")
def tolat(h): return sm.interpN(tolN, h)
n = int(sys.argv[1])
tot = 0; bad = 0; un = 0; nc = 0; hb = []
for rf, ef in [(1.0, 1.0), (0.995, 0.995), (0.98, 0.98), (0.9, 0.99), (0.6, 0.99)]:
    X = sm.sample(n, 6.0 * rf, None, tolfun=lambda h: tolat(h) * ef)
    img, safe, cl, t0, t1 = ticks_T(X)
    m = t0; tot += m.sum(); bad += (m & ~t1).sum(); un += (m & ~safe).sum(); nc += (m & ~cl).sum()
    hb += list(X[m & ~t1][:,1] / 65536)
    print(f"r {6*rf:.2f} fast {ef}: in T {m.sum()}/{n}; leaves T {(m & ~t1).sum()}; unsafe {(m & ~safe).sum()}; noclimb {(m & ~cl).sum()}", flush=True)
print("total in T", tot, "exits", bad, "unsafe", un, "noclimb", nc, "exit altitudes", np.round(sorted(hb))[:20])
