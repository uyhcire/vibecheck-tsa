"""Centre table from the climbing manifold (trajectories), not frozen-h equilibria: above 2500 m the throttle
schedule moves the equilibrium quickly with h and the climbing state lags the frozen equilibrium by far more than
the set's radius (manifold pressure is a first-order lag)."""
import numpy as np
from pf import *
F = np.load("frozen.npy")
x0 = F[100].copy(); x0[0] = 0      # frozen equilibrium at 1000 m as a starting point
x = x0.copy()
for it in range(5):
    x[1] = 5 * 65536 + 32768; t = traj(x, 600)
    k = np.argmin(abs(t[:, 1] / 65536 - 60)); x = t[k].copy(); x[0] = 0
x[1] = 5 * 65536 + 32768
up = traj(x, 16000)
above = F[200].copy(); above[0] = 0; above[1] = 2800 * 65536
dn = traj(above, 14000)
hf = up[-1, 1]
dn_ok = dn[700:]; dn_ok = dn_ok[dn_ok[:, 1] > hf + 1]
M = np.concatenate([up, dn_ok]); M = M[np.argsort(M[:, 1], kind="stable")]
hs = M[:, 1] / 65536
print("fixed point", hf / 65536, "range", hs.min(), hs.max(), "down part starts at", dn_ok[0, 1] / 65536 if len(dn_ok) else None)
HT = np.arange(0, 2710, 10)
tab = np.array([[np.interp(h, hs, M[:, j]) for j in range(21)] for h in HT])
tab[:, 1] = HT * 65536
np.save("man2.npy", np.round(tab).astype(np.int64))
for h in [10, 500, 1000, 2000, 2400, 2500, 2540, 2600, 2640]:
    i = h // 10; print(h, "climb vs frozen: vz", round(tab[i, 3] / 65536, 3), round(F[min(i, len(F)-1), 3] / 65536, 3), " tmap", round(tab[i, 8] / 65536, 2), round(F[min(i, len(F)-1), 8] / 65536, 2))
