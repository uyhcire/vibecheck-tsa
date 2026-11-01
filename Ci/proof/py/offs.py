import numpy as np, kinv
from kinv import *
def xof(h, y):
    c = center(h); g = Gat(h) @ y
    x = c.copy(); x[0] = 0; x[1] = int(round(h * 65536)); x[11] = 0
    x[yidx] = np.round(c[yidx] + y * Sy); x[gidx] = np.round(c[gidx] + g * Sg); x[20] = int(c[20])
    return x.astype(np.int64)
hs = np.arange(2400, 2690, 7.0)
X = np.array([xof(h, np.zeros(7)) for h in hs]); img, *_ = ticks(X)
for h, xi in zip(hs, img):
    h1, y1, e1 = coords(xi)
    print(f"{h:.0f}: |y'(0)|_P / r = {np.sqrt(V(h1, y1)) / rat(h1):.4f}  y'={np.round(y1, 3)}")
