import numpy as np, sample as sm
from sample import *
for it in range(3):
    X = sm.sample(6000, 3.0, 0.0)
    img, _, _ = ticks(X)
    H=[]; Ys=[]; Gs_=[]
    for xi in img:
        h = xi[1]/65536; c = center(h)
        H.append(h); Ys.append((xi[yidx]-c[yidx])/Sy); Gs_.append((xi[gidx]-c[gidx])/Sg)
    H=np.array(H); Ys=np.array(Ys); Gm=np.array(Gs_)
    newG = np.array(sm.GsN)  # copy
    for i, hn in enumerate(HN):
        w = np.exp(-((H-hn)/100.0)**2)
        Wm = np.sqrt(w)[:,None]
        sol, *_ = np.linalg.lstsq(Ys*Wm, Gm*Wm, rcond=None)
        newG[i,0] = sol.T; newG[i,1] = sol.T
    res = np.abs(Gm - np.einsum('nij,nj->ni', np.array([sm.interpN(newG[:,0], h) for h in H]), Ys)).max(axis=0)
    print(it, "residual after refit:", res.round(3))
    sm.GsN = newG
np.save("GsN_fit.npy", sm.GsN)
