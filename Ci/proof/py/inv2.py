"""V'/r^2 and fast residuals with fast coordinates at the tolerance edge (Python-side T)."""
import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
r = float(sys.argv[1])
X = sm.sample(4000, r, 0.0); img, safe, cl = ticks(X)
E = np.array([np.abs(coords(xi)[2]) for xi in img]); base = E.max(axis=0)
print("fast residual max at eg=0:", dict(zip([ZN[i] for i in GI], base.round(3))))
floor = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02])
tol = 1.3 * base + floor
for frac in [0.0, 0.5, 1.0]:
    X = sm.sample(4000, r, tol * frac); img, safe, cl = ticks(X)
    rows = []
    for x, xi in zip(X, img):
        h0, y0, e0 = coords(x); h1, y1, e1 = coords(xi)
        rows.append((h0, V(h1, y1)/(r*r), np.max(np.abs(e1)/tol)))
    rows = np.array(rows)
    print(f"eg {frac}: V'/r^2 max {rows[:,1].max():.4f} (h {rows[rows[:,1].argmax(),0]:.0f}), p99 {np.quantile(rows[:,1],0.99):.4f}; fast'/tol max {rows[:,2].max():.3f}; unsafe {(~safe).sum()} noclimb {(~cl).sum()}")
np.save("tol.npy", tol)
