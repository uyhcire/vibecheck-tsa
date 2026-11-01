"""Robust-invariance LMI: how large a per-tick disturbance (the Fx rounding floor measured by the affine prototype,
times a scale s) can the slow-coordinate ellipsoid absorb?  For each sampled one-tick Jacobian A (interval-sampled,
recentred) with the form P(t) interpolated across the 100 m interval, require (S-lemma, fixed multiplier lam):
  [lam P - Aᵀ P A, -Aᵀ P; -P A, (1 - lam) M - P] ⪰ 0,   M = diag(1 / (7 (s σ_i / r)²)),
which makes (A u + v)ᵀ P (A u + v) ≤ 1 for all uᵀ P u ≤ 1 and v in the ellipsoid bounding the box |v_i| ≤ s σ_i / r."""
import numpy as np, cvxpy as cp, pickle, sys, os
samples = pickle.load(open("samplesC.pkl", "rb"))
HN = np.load("HN.npy"); N = len(HN); n = 7
R0 = 4.5; RT = 3.6
def rnode(h): return R0 if h <= 2200 else RT if h >= 2400 else R0 + (RT - R0) * (h - 2200) / 200
sigma = np.array([float(x) for x in os.environ.get("SIGMA", "0.008,0.0176,0.07,0.052,0.0233,0.0177,0.004").split(",")])
def feas(s, lam, kappa=float(os.environ.get("KAPPA", "200"))):
    P = [cp.Variable((n, n), symmetric=True) for _ in range(N)]
    cons = []
    for i in range(N):
        cons += [P[i] >> np.eye(n), P[i] << kappa * np.eye(n)]
    for (i, t, A) in samples:
        r = rnode(HN[i] + 100 * t)
        M = np.diag(1.0 / (7 * (s * sigma / r) ** 2))
        Pt = (1 - t) * P[i] + t * P[i + 1]
        blk = cp.bmat([[lam * Pt - A.T @ Pt @ A, -A.T @ Pt], [-Pt @ A, (1 - lam) * M - Pt]])
        cons.append((blk + blk.T) / 2 >> 0)
    pr = cp.Problem(cp.Minimize(0), cons)
    try: pr.solve(solver=cp.CLARABEL)
    except Exception: return False
    return pr.status.startswith("optimal")
for lam in [float(x) for x in sys.argv[1:]]:
    lo, hi = 0.0, 4.0
    if not feas(1e-3, lam): print(f"lam {lam}: infeasible even with no disturbance"); continue
    for _ in range(8):
        mid = (lo + hi) / 2
        if feas(mid, lam): lo = mid
        else: hi = mid
    print(f"lam {lam}: largest disturbance scale s = {lo:.3f} x the rounding floor", flush=True)
