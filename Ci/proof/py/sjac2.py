"""Sampled Jacobians of the one-tick map in T's own coordinates (y at h -> y' at h', recentred on the manifold
table at the new altitude), then the scheduled LMI. Captures the recentring term dc/dh * dh'/dy, which is large
above 2500 m where the throttle schedule moves the equilibrium quickly with h."""
import numpy as np, sys, os, cvxpy as cp, kinv
from kinv import *
K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
rngj = np.random.default_rng(17)
def xof(h, y):
    c = center(h); g = Gat(h) @ y
    x = c.copy(); x[0] = 0; x[1] = int(round(h * 65536)); x[11] = 0
    x[yidx] = np.round(c[yidx] + y * Sy); x[gidx] = np.round(c[gidx] + g * Sg); x[20] = int(c[20])
    return x.astype(np.int64)
samples = []   # (interval index, t, A)
for i in range(len(HN) - 1):
    pts = []; meta = []
    for k in range(K):
        h = float(np.clip(HN[i] + (k + 0.5) / K * 100 + rngj.uniform(-5, 5), 10, 2685))
        y0 = np.zeros(7) if k == 0 else (lambda u: u / np.sqrt(u @ Pat(h) @ u) * rat(h) * rngj.uniform(0.3, 1.0))(rngj.normal(size=7))
        meta.append(h)
        for a in range(7):
            for sg in (1, -1):
                y = y0.copy(); y[a] += sg * 0.5; pts.append(xof(h, y))
    img, *_ = ticks(np.array(pts))
    Y1 = np.array([coords(xi)[1] for xi in img])
    for k, h in enumerate(meta):
        A = np.zeros((7, 7))
        for a in range(7):
            A[:, a] = (Y1[k*14 + 2*a] - Y1[k*14 + 2*a + 1]) / 1.0
        samples.append((i, min(max((h - HN[i]) / 100, 0), 1), A))
import pickle; pickle.dump(samples, open("samplesC.pkl", "wb"))
N = len(HN); n = 7
def feas(rho, kappa=200.0):
    P = [cp.Variable((n, n), symmetric=True) for _ in range(N)]
    cons = []
    for i in range(N):
        cons += [P[i] >> np.eye(n), P[i] << kappa*np.eye(n)]
    for (i, t, A) in samples:
        Pt = (1 - t) * P[i] + t * P[i + 1]
        M = rho**2 * Pt - A.T @ Pt @ A
        cons.append((M + M.T) / 2 >> 0)
    pr = cp.Problem(cp.Minimize(sum(cp.trace(p) for p in P)), cons)
    try: pr.solve(solver=cp.CLARABEL)
    except Exception: return False, None
    return pr.status.startswith("optimal"), [p.value for p in P]
lo, hi = 0.95, 1.0; best = None
for _ in range(9):
    mid = (lo + hi) / 2; ok, Ps = feas(mid)
    if ok: hi = mid; best = Ps
    else: lo = mid
print("recentred sampled-Jacobian rho", hi)
if best is not None: np.save("PN_c.npy", np.array(best))
