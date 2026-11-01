import numpy as np, sys
from sample import *
r = float(sys.argv[1]); k = float(sys.argv[2])
base = np.array([0.094,0.189,2.378,0.331,2.366,0.088,0.355,2.477,0.019,0.039,0.022]) / 3   # residual per unit r
eg = k * base * r + np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02])
X = sample(4000, r, eg)
img, safe, cl = ticks(X)
rows = []
for x, xi in zip(X, img):
    h0, y0, e0 = coords(x); h1, y1, e1 = coords(xi)
    rows.append((h0, V(h1, y1) / (r*r), V(h0,y0)/(r*r), np.max(np.abs(e1) / eg)))
rows = np.array(rows)
print(f"r {r} k {k}: V'/r^2 max {rows[:,1].max():.4f} at h {rows[rows[:,1].argmax(),0]:.0f}; fast-ratio max {rows[:,3].max():.3f}; unsafe {(~safe).sum()} noclimb {(~cl).sum()}")
for lo, hi in [(0,200),(200,1000),(1000,2400),(2400,2560),(2560,2640)]:
    m = (rows[:,0] >= lo) & (rows[:,0] < hi)
    print(f"   h {lo}-{hi}: max V'/r^2 {rows[m,1].max():.4f}  fast {rows[m,3].max():.3f}")
