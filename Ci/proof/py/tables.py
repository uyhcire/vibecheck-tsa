import numpy as np, lin
from pf import *
from lin import ZI, STEP, jac
from reduce import reduced, Y, G_
M = np.load("manifold.npy"); tl = np.load("traj_low.npy")
Mall = np.concatenate([tl[tl[:,1] < 85*65536], M[M[:,1] >= 85*65536]])
Mall = Mall[np.argsort(Mall[:,1], kind="stable")]
np.save("manifold_all.npy", Mall)
hs = Mall[:,1] / 65536
HT = np.arange(0, 2710, 10)            # table altitudes (m); below 5.5 m extrapolated flat
tab = np.array([[np.interp(h, hs, Mall[:,j]) for j in range(21)] for h in HT])
np.save("ytab.npy", tab)
def nearest(h):
    k = np.argmin(abs(hs - h)); return Mall[k].copy()
S = np.array([STEP[i] for i in ZI], dtype=float)
HN = np.arange(0, 2800, 100)           # Jacobian nodes; node 0 uses the 20 m state
As = []; Gs = []
for h in HN:
    row = []
    for scale in [1, 4]:
        lin.STEP = {k: v*scale for k, v in STEP.items()}
        J, _ = jac(nearest(max(h, 20)))
        Jy = np.diag(1/S) @ J @ np.diag(S)
        A, G = reduced(Jy); row.append((A, G))
    lin.STEP = dict(STEP)
    As.append([row[0][0], row[1][0]]); Gs.append([row[0][1], row[1][1]])
    print(h, " ".join(f"{abs(e):.4f}" for e in sorted(np.linalg.eigvals(row[0][0]), key=lambda e: -abs(e))[:4]))
np.save("AsN.npy", np.array(As)); np.save("GsN.npy", np.array(Gs)); np.save("HN.npy", HN)
