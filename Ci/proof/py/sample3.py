import numpy as np, sys
from sample import *
eg0 = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02])
for which in range(len(GI)):
    eg = np.zeros(len(GI)); eg[which] = 2.0
    X = sample(200, 1e-9, eg)
    img, safe, cl = ticks(X)
    e1s = []; ys = []
    for x, xi in zip(X, img):
        h0, y0, e0 = coords(x); h1, y1, e1 = coords(xi); e1s.append(np.abs(e1)); ys.append(np.sqrt(V(h1,y1)))
    e1s = np.array(e1s)
    print(ZN[GI[which]], "-> fast max", dict(zip([ZN[i] for i in GI], e1s.max(axis=0).round(2))), "y' norm max", round(max(ys),3))
