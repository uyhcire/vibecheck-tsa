"""Synthesise the node forms with the robust LMI (disturbance = SCALE x the measured Fx-vs-real per-tick gap),
minimising the trace for a well-conditioned set; writes PN_r.npy."""
import numpy as np, cvxpy as cp, pickle, os
samples = pickle.load(open("samplesC.pkl", "rb"))
HN = np.load("HN.npy"); N = len(HN); n = 7
R0 = 4.5; RT = 3.6
def rnode(h): return R0 if h <= 2200 else RT if h >= 2400 else R0 + (RT - R0) * (h - 2200) / 200
sigma = np.array([0.00083, 0.00329, 0.00914, 0.00655, 0.00421, 0.00481, 0.0005])
s = float(os.environ.get("SCALE", "1.5")); lam = float(os.environ.get("LAM", "0.985"))
P = [cp.Variable((n, n), symmetric=True) for _ in range(N)]
cons = []
for i in range(N):
    cons += [P[i] >> np.eye(n), P[i] << 200 * np.eye(n)]
for (i, t, A) in samples:
    r = rnode(HN[i] + 100 * t)
    M = np.diag(1.0 / (7 * (s * sigma / r) ** 2))
    Pt = (1 - t) * P[i] + t * P[i + 1]
    blk = cp.bmat([[lam * Pt - A.T @ Pt @ A, -A.T @ Pt], [-Pt @ A, (1 - lam) * M - Pt]])
    cons.append((blk + blk.T) / 2 >> 0)
pr = cp.Problem(cp.Minimize(sum(cp.trace(p) for p in P)), cons)
pr.solve(solver=cp.CLARABEL)
print(pr.status)
Ps = np.array([p.value for p in P]); np.save("PN_r.npy", Ps)
print("eig ranges:", [(round(np.linalg.eigvalsh(p).min(), 2), round(np.linalg.eigvalsh(p).max(), 1)) for p in Ps[::6]])
