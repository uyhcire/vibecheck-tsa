import numpy as np, cvxpy as cp, lin
from lin import ZI, STEP, jac
from design import nearest
S = np.array([STEP[i] for i in ZI], dtype=float)
Js = []
hs = [100, 300, 500, 800, 1000, 1300, 1500, 1800, 2000, 2200, 2400, 2450, 2500, 2550, 2600, 2619, 2650, 2700]
for scale in [1, 4]:
    lin.STEP = {k: v*scale for k, v in STEP.items()}
    for h in hs:
        J, _ = jac(nearest(h)); Js.append(np.diag(1/S) @ J @ np.diag(S))
    lin.STEP = dict(STEP)
np.save("Jys.npy", np.array(Js))
n = len(ZI)
def feas(rho):
    P = cp.Variable((n, n), symmetric=True)
    cons = [P >> np.eye(n)]
    for Jy in Js:
        cons.append(cp.bmat([[rho**2 * P, Jy.T @ P], [P @ Jy, P]]) >> 0)
    prob = cp.Problem(cp.Minimize(cp.lambda_max(P)), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.status, (P.value if P.value is not None else None)
lo, hi = 0.97, 1.0
best = None
for _ in range(9):
    mid = (lo + hi) / 2
    st, P = feas(mid)
    ok = st in ("optimal", "optimal_inaccurate")
    print(f"rho {mid:.5f} {st}", f"cond {np.linalg.cond(P):.1f}" if ok else "")
    if ok: hi = mid; best = (mid, P)
    else: lo = mid
np.save("P.npy", best[1]); print("best rho", best[0])
