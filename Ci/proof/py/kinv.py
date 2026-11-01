"""T with kink-aware fast tolerance: sample at the corners, tick, measure V' and the fast constraints."""
import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy")
kN = np.load("kN.npy"); tkN = np.load("tkN.npy"); tpN = np.load("tpN.npy")
def kat(h): k = sm.interpN(kN, h).copy(); k[10] = 0; return k / np.linalg.norm(k)
def tkat(h): return sm.interpN(tkN, h)
def tpat(h): return sm.interpN(tpN, h)
R = float(os.environ.get("RR", "6.0")); RTOP = float(os.environ.get("RTOP", str(R)))
RSCHED = os.environ.get("RSCHED")   # e.g. "2300:4.5,2400:3.8,2500:4.2,2600:4.5"
def _rnode(h):
    if RSCHED:
        pts = sorted((float(a), float(b)) for a, b in (kv.split(":") for kv in RSCHED.split(",")))
        return float(np.interp(h, [p[0] for p in pts], [p[1] for p in pts]))
    return R if h <= 2200 else RTOP if h >= 2400 else R + (RTOP - R) * (h - 2200) / 200
r2N = np.array([_rnode(h) ** 2 for h in HN])
def rat(h): return float(np.sqrt(sm.interpN(r2N, h)))
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
def ksample(n, r=R, fl=1.0, fp=1.0, hlo=10, hhi=2685):
    pts = []
    for _ in range(n):
        h = rng.uniform(hlo, hhi); c = center(h); P = Pat(h)
        u = rng.normal(size=7); y = u / np.sqrt(u @ P @ u) * r / R * rat(h)
        k = kat(h); lam = tkat(h) * fl * rng.choice([-1, 1]); ep = tpat(h) * fp * rng.choice([-1, 1], size=len(GI))
        ep[10] = 0; ep = ep - (ep @ k) * k
        sc = np.max(np.abs(ep[:10]) / tpat(h)[:10]); ep = ep * (fp / sc if sc > 0 else 0)
        e = lam * k + ep
        g = Gat(h) @ y + e
        x = c.copy(); x[0] = 0; x[1] = h * 65536; x[11] = 0
        x[yidx] = c[yidx] + y * Sy; x[gidx] = c[gidx] + g * Sg; x[20] = c[20]
        pts.append(np.round(x).astype(np.int64))
    return np.array(pts)
def fastcheck(x):
    h, y, e = coords(x); e = e.copy(); e[10] = 0; k = kat(h); lam = e @ k; perp = e - lam * k
    return max(abs(lam) / tkat(h), np.max(np.abs(perp[:10]) / tpat(h)[:10]))
if __name__ == "__main__":
    n = int(sys.argv[1])
    for fl, fp in [(1, 1), (1, 0), (0, 1), (0.5, 0.5)]:
        X = ksample(n, fl=fl, fp=fp); img, safe, cl = ticks(X)
        rows = np.array([(coords(x)[0], V(*coords(xi)[:2]) / rat(coords(xi)[0])**2, fastcheck(xi), fastcheck(x)) for x, xi in zip(X, img)])
        print(f"fl {fl} fp {fp}: start fast {rows[:,3].max():.3f}; V'/r^2 max {rows[:,1].max():.4f} (h {rows[rows[:,1].argmax(),0]:.0f}); fast' max {rows[:,2].max():.3f}; unsafe {(~safe).sum()} noclimb {(~cl).sum()}", flush=True)
