import numpy as np, pickle, os
samples = pickle.load(open("samplesC.pkl", "rb")); HN = np.load("HN.npy")
P = np.load(os.environ.get("PF", "PN_r.npy"))
R0 = 4.5; RT = 3.6
def rnode(h): return R0 if h <= 2200 else RT if h >= 2400 else R0 + (RT - R0) * (h - 2200) / 200
sigma = np.array([0.00083, 0.00329, 0.00914, 0.00655, 0.00421, 0.00481, 0.0005])
for s in [1.0, 1.25, 1.5]:
  worst = 1e9; worstn = 1e9
  for lam in [0.985]:
    for (i, t, A) in samples:
        r = rnode(HN[i] + 100 * t); M = np.diag(1.0 / (7 * (s * sigma / r) ** 2))
        Pt = (1 - t) * P[i] + t * P[i + 1]
        blk = np.block([[lam * Pt - A.T @ Pt @ A, -A.T @ Pt], [-Pt @ A, (1 - lam) * M - Pt]])
        worst = min(worst, np.linalg.eigvalsh((blk + blk.T) / 2).min())
        L = np.linalg.cholesky(Pt); worstn = min(worstn, 1 - np.linalg.norm(L.T @ A @ np.linalg.inv(L.T), 2))
  print(f"s {s}: min eig of robust block {worst:.2e}; nominal contraction margin 1-|A|_P = {worstn:.4f}")
