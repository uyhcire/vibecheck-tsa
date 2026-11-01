"""Fixed-point iteration of the fast tolerances: tol <- 1.15 x (fast residual after one tick from T, fast at corners) + floor."""
import numpy as np, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy"); tolN = np.load("tolN.npy")
floor = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02]) * 0.5
for it in range(4):
    tolat = lambda h: sm.interpN(tolN, h)
    X = sm.sample(8000, 6.0, None, tolfun=tolat); img, *_ = ticks(X)
    H = img[:,1]/65536; E = np.array([np.abs(coords(xi)[2]) for xi in img])
    new = np.zeros_like(tolN)
    for i, hn in enumerate(HN):
        m = (H >= hn - 150) & (H <= hn + 150)
        new[i] = 1.15 * (E[m].max(axis=0) if m.any() else E.max(axis=0)) + floor
    print(it, "wdot tol by node (old->new):", [(int(h), round(a[2],2), round(b[2],2)) for h, a, b in zip(HN, tolN, new)][::4])
    tolN = np.maximum(new, 0.6 * tolN)   # shrink at most 40% per step
np.save("tolN.npy", tolN)
