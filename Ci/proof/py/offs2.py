import numpy as np, kinv
from kinv import *
M = np.load("man_raw.npy"); hs = M[:, 1] / 65536
for h in [2400, 2540, 2582, 2596, 2620, 2666]:
    k = np.argmin(abs(hs - h)); x = M[k].copy(); x[0] = 0
    h0, y0, e0 = coords(x)
    img, *_ = ticks(np.array([x])); h1, y1, e1 = coords(img[0])
    print(f"{h0:.1f}: y0 {np.round(y0,3)} |y0|/r {np.sqrt(V(h0,y0))/rat(h0):.4f} -> y1 {np.round(y1,3)} |y1|/r {np.sqrt(V(h1,y1))/rat(h1):.4f}; e0max {np.abs(e0[:10]).max():.3f}")
