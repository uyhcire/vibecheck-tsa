"""Altitude-dependent fast tolerances: kink residual max per 100 m node (neighbour max), x1.3 + floor."""
import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
r = float(sys.argv[1])
X = sm.sample(12000, r, 0.0); img, _, _ = ticks(X)
H = X[:,1]/65536; E = np.array([np.abs(coords(xi)[2]) for xi in img])
floor = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02])
N = len(HN); base = np.zeros((N, len(GI)))
for i, hn in enumerate(HN):
    m = (H >= hn - 150) & (H <= hn + 150)
    base[i] = E[m].max(axis=0) if m.any() else E.max(axis=0)
tolN = 1.3 * base + floor
np.save("tolN.npy", tolN)
print("wdot/au tol by node:", [(int(h), round(t[2],2)) for h, t in zip(HN, tolN)][::3])
