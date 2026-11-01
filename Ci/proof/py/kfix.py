import numpy as np, kinv
from kinv import *
floor = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02]) * 0.5
for it in range(5):
    X = np.concatenate([ksample(3000, fl=1, fp=1), ksample(3000, fl=0, fp=1), ksample(2000, fl=1, fp=0)])
    img, *_ = ticks(X)
    H = img[:,1]/65536; L = []; Pp = []
    for xi in img:
        h, y, e = coords(xi); e = e.copy(); e[10] = 0; k = kat(h); lam = e @ k; L.append(abs(lam)); Pp.append(np.abs(e - lam*k))
    L = np.array(L); Pp = np.array(Pp)
    nk = np.zeros_like(kinv.tkN); npp = np.zeros_like(kinv.tpN)
    for i, hn in enumerate(HN):
        m = (H >= hn - 150) & (H <= hn + 150)
        nk[i] = 1.15 * L[m].max() + 0.3; npp[i] = 1.15 * Pp[m].max(axis=0) + floor
    worst = max(np.max(L / np.array([tkat(h) for h in H])), np.max(Pp[:, :10] / np.array([tpat(h)[:10] for h in H])))
    print(it, "fast'/tol max", round(worst, 3), "tau_k@300", round(nk[3],2), "tau_perp@300", np.round(npp[3][:10],2), flush=True)
    kinv.tkN = np.maximum(nk, kinv.tkN * 0.0 + nk); kinv.tpN = np.maximum(npp, 0.5 * kinv.tpN) if it == 0 else npp
np.save("tkN.npy", kinv.tkN); np.save("tpN.npy", kinv.tpN)
