"""Frozen-altitude design: centre = frozen-h equilibria; node Jacobians there; scheduled LMI; G fit."""
import numpy as np, lin, cvxpy as cp
from pf import *
from lin import ZI, STEP, jac
from reduce import reduced
E = np.load("frozen.npy"); HT = np.arange(0, 2660, 10)
np.save("man2.npy", E)   # sample.py's centre table: frozen equilibria
S = np.array([STEP[i] for i in ZI], dtype=float)
HN = np.arange(0, 2800, 100); As=[]; Gs=[]
for h in HN:
    x = E[np.argmin(abs(HT - min(max(h, 10), 2650)))].copy()
    row = []
    for scale in [1, 2]:
        lin.STEP = {k: v*scale for k, v in STEP.items()}
        J, _ = jac(x); A, G = reduced(np.diag(1/S) @ J @ np.diag(S)); row.append((A, G))
    lin.STEP = dict(STEP)
    As.append([r[0] for r in row]); Gs.append([r[1] for r in row])
As = np.array(As); np.save("AsN.npy", As); np.save("GsN.npy", np.array(Gs)); np.save("HN.npy", HN)
N = len(HN); n = 7
def feas(rho, kappa=200.0):
    P = [cp.Variable((n, n), symmetric=True) for _ in range(N)]
    cons = []
    for i in range(N):
        cons += [P[i] >> np.eye(n), P[i] << kappa*np.eye(n)]
        for A in As[i]:
            for j in {max(0,i-1), i, min(N-1,i+1)}:
                cons.append(rho**2 * P[i] - A.T @ P[j] @ A >> 0)
    pr = cp.Problem(cp.Minimize(sum(cp.trace(p) for p in P)), cons)
    try: pr.solve(solver=cp.CLARABEL)
    except Exception: return False, None
    return pr.status.startswith("optimal"), [p.value for p in P]
lo, hi = 0.96, 1.0; best=None
for _ in range(9):
    mid=(lo+hi)/2; ok, Ps = feas(mid)
    if ok: hi=mid; best=Ps
    else: lo=mid
print("scheduled rho", hi); np.save("PN.npy", np.array(best))
