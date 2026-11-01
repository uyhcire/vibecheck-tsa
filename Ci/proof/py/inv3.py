import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy"); tolN = np.load("tolN.npy")
def tolat(h): return sm.interpN(tolN, h)
r = float(sys.argv[1]); n = int(sys.argv[2])
X = sm.sample(n, r, None, tolfun=tolat); img, safe, cl = ticks(X)
rows = np.array([(coords(x)[0], V(*coords(xi)[:2])/(r*r), np.max(np.abs(coords(xi)[2])/tolat(xi[1]/65536))) for x, xi in zip(X, img)])
print(f"n {n}: V'/r^2 max {rows[:,1].max():.4f} (h {rows[rows[:,1].argmax(),0]:.0f}); fast'/tol max {rows[:,2].max():.3f}; unsafe {(~safe).sum()} noclimb {(~cl).sum()}")
for lo, hi in [(0,300),(300,1000),(1000,2000),(2000,2500),(2500,2640)]:
    m = (rows[:,0]>=lo)&(rows[:,0]<hi); print(f"   {lo}-{hi}: V' {rows[m,1].max():.4f} fast {rows[m,2].max():.3f}")
