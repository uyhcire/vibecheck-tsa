import numpy as np, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
rng = np.random.default_rng(5); U = rng.normal(size=(4, 7))
pts=[]; meta=[]
for h in np.arange(15, 2640, 37.0):
    c = center(h)
    for u in U:
        y = u / np.sqrt(u @ Pat(h) @ u) * 4
        x = c.copy(); x[0] = 0; x[1] = h*65536; x[11] = 0
        x[yidx] = c[yidx] + y*Sy; x[gidx] = c[gidx] + (Gat(h) @ y)*Sg; x[20] = c[20]
        pts.append(np.round(x).astype(np.int64)); meta.append(h)
img, *_ = ticks(np.array(pts))
res = {}
for hh, xi in zip(meta, img):
    e1 = coords(xi)[2]; res.setdefault(hh, []).append(np.abs(e1[[2,4,7]]).max())
for hh in res: print(f"{hh:.0f}: {max(res[hh]):.3f}")
