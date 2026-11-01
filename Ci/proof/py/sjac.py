"""Sampled-Jacobian design: local Jacobians at points spread over T (the lift curve is piecewise linear with
breakpoints every 0.01-0.02 rad, so one linearisation per altitude is not enough)."""
import numpy as np, lin, cvxpy as cp, sys, sample as sm
from pf import *
from lin import ZI, STEP, jac
from reduce import reduced
sm.GsN = np.load("GsN_fit.npy")
R = float(sys.argv[1]) if len(sys.argv) > 1 else 6.0
K = int(sys.argv[2]) if len(sys.argv) > 2 else 6
S = np.array([STEP[i] for i in ZI], dtype=float)
HN = np.load("HN.npy"); As = []
rng = np.random.default_rng(11)
lin.STEP = {k: max(1, v // 4) for k, v in STEP.items()}
for h in HN:
    hh = min(max(h, 10), 2635)
    c = sm.center(hh); Ah = []
    for k in range(K + 1):
        if k == 0: x = c.copy(); x[0] = 0; x[1] = int(hh*65536); x = np.round(x).astype(np.int64)
        else:
            u = rng.normal(size=7); P = sm.Pat(hh); y = u / np.sqrt(u @ P @ u) * R * rng.uniform(0.3, 1.0)
            x = c.copy(); x[0] = 0; x[1] = hh*65536; x[11] = 0
            x[sm.yidx] = c[sm.yidx] + y*sm.Sy; x[sm.gidx] = c[sm.gidx] + (sm.Gat(hh) @ y)*sm.Sg; x[20] = c[20]
            x = np.round(x).astype(np.int64)
        J, _ = jac(x); A, _ = reduced(np.diag(1/S) @ J @ np.diag(S)); Ah.append(A)
    As.append(Ah)
lin.STEP = dict(STEP)
As = np.array(As); np.save("AsS.npy", As)
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
print("sampled-Jacobian scheduled rho", hi)
if best is not None: np.save("PN_s.npy", np.array(best))
# per-node rho with only own node (diagnostic)
