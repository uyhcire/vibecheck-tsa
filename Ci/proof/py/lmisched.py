import numpy as np, cvxpy as cp
As = np.load("AsN.npy"); N = As.shape[0]; n = 7
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
lo, hi = 0.97, 1.0; best = None
for _ in range(9):
    mid = (lo+hi)/2; ok, Ps = feas(mid)
    print(f"{mid:.5f} {ok}")
    if ok: hi = mid; best = Ps
    else: lo = mid
np.save("PN.npy", np.array(best)); print("rho", hi)
