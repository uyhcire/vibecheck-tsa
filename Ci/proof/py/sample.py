import numpy as np, sys
from pf import *
from lin import ZI, STEP
from reduce import Y as YI, G_ as GI
Mall = np.load("man2.npy"); hsM = Mall[:,1]/65536
import os; PN = np.load(os.environ.get("PFILE", "PN.npy")); GsN = np.load("GsN.npy"); HN = np.load("HN.npy")
S = np.array([STEP[i] for i in ZI], dtype=float)
ZN = [NAMES[i] for i in ZI]
yidx = [ZI[i] for i in YI]; gidx = [ZI[i] for i in GI]          # raw state indices
Sy = S[YI]; Sg = S[GI]
def center(h): return np.array([np.interp(h, hsM, Mall[:,j]) for j in range(21)])
def interpN(arr, h):
    t = np.clip(h / 100, 0, len(HN) - 1 - 1e-9); i = int(t); f = t - i
    return (1-f) * arr[i] + f * arr[i+1]
def Pat(h): return interpN(PN, h)
def Gat(h): return interpN(GsN[:,0], h)       # scale-1 G
def coords(x):
    h = x[1] / 65536; c = center(h)
    y = (x[yidx] - c[yidx]) / Sy
    g = (x[gidx] - c[gidx]) / Sg
    return h, y, g - Gat(h) @ y
def V(h, y): return y @ Pat(h) @ y
CORNER = os.environ.get('CORNER') == '1'
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
def sample(n, r, eg, hlo=10, hhi=2635, tolfun=None):
    pts = []
    for _ in range(n):
        h = rng.uniform(hlo, hhi); c = center(h); P = Pat(h)
        u = rng.normal(size=7); u /= np.sqrt(u @ P @ u); y = u * r * rng.uniform(0.9, 1.0) ** 0
        if tolfun is not None: eg = tolfun(h)
        g = Gat(h) @ y + eg * (rng.choice([-1.0, 1.0], size=len(GI)) if CORNER else rng.uniform(-1, 1, size=len(GI)))
        x = c.copy(); x[0] = 0; x[1] = h * 65536; x[11] = 0
        x[yidx] = c[yidx] + y * Sy; x[gidx] = c[gidx] + g * Sg
        x[20] = c[20]
        pts.append(np.round(x).astype(np.int64))
    return np.array(pts)
if __name__ == "__main__":
    r = float(sys.argv[1]); eg = np.array(eval(sys.argv[2])) if len(sys.argv) > 2 else 0.0
    X = sample(3000, r, eg)
    img, safe, cl = ticks(X)
    ratios = []; gres = []
    for x, xi in zip(X, img):
        h0, y0, e0 = coords(x); h1, y1, e1 = coords(xi)
        ratios.append(V(h1, y1) / V(h0, y0)); gres.append(np.abs(e1))
    ratios = np.array(ratios); gres = np.array(gres)
    print(f"r {r}: V'/V max {ratios.max():.4f} p99 {np.quantile(ratios,0.99):.4f} median {np.median(ratios):.4f}; unsafe {(~safe).sum()} noclimb {(~cl).sum()}")
    print("  fast residual max (STEP units):", dict(zip([ZN[i] for i in GI], gres.max(axis=0).round(3))))
