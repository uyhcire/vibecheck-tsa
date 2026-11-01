"""Rebuild the slow manifold and node Jacobians for the current pfprobe law."""
import numpy as np, lin
from pf import *
from lin import ZI, STEP, jac
from reduce import reduced
tr, _ = bench_traj(0, 600); x0 = tr[600].copy(); x0[0] = 0
# low part: reset-to-5.5 m iteration
x = x0.copy()
for it in range(4):
    x[1] = 5*65536 + 32768; t = traj(x, 400)
    k = np.argmin(abs(t[:,1]/65536 - 40)); x = t[k].copy(); x[0] = 0
x[1] = 5*65536 + 32768
up = traj(x, 16000)               # 5.5 m -> fixed point
above = x0.copy(); above[1] = 2800*65536
dn = traj(above, 12000)
print("up end", up[-1,1]/65536, up[-1,3]/65536, " dn end", dn[-1,1]/65536, dn[-1,3]/65536)
hf = up[-1,1]
dn_ok = dn[1500:]; dn_ok = dn_ok[dn_ok[:,1] > hf + 1]
Mall = np.concatenate([up, dn_ok]); Mall = Mall[np.argsort(Mall[:,1], kind="stable")]
np.save("man2.npy", Mall)
hs = Mall[:,1]/65536
print("manifold h range", hs.min(), hs.max(), "dn starts on manifold at h", dn_ok[0,1]/65536)
def nearest(h): return Mall[np.argmin(abs(hs-h))].copy()
S = np.array([STEP[i] for i in ZI], dtype=float)
HN = np.arange(0, 2800, 100); As=[]; Gs=[]
for h in HN:
    row = []
    for scale in [1, 4]:
        lin.STEP = {k: v*scale for k, v in STEP.items()}
        J, _ = jac(nearest(max(h, 20))); A, G = reduced(np.diag(1/S) @ J @ np.diag(S)); row.append((A, G))
    lin.STEP = dict(STEP)
    As.append([r[0] for r in row]); Gs.append([r[1] for r in row])
    print(h, " | ".join(" ".join(f"{abs(e):.4f}" for e in sorted(np.linalg.eigvals(r[0]), key=lambda e: -abs(e))[:4]) for r in row))
np.save("AsN.npy", np.array(As)); np.save("GsN.npy", np.array(Gs)); np.save("HN.npy", HN)
