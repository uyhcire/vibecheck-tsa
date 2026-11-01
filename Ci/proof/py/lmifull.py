import numpy as np, cvxpy as cp, sys
Js = np.load("JfN.npy"); N = Js.shape[0]; n = Js.shape[-1]
# drop the 'ac' coordinate (last): it has no effect on the dynamics inside T
keep = list(range(n - 1)); Js = Js[:, :, keep][:, :, :, keep]; n = len(keep)
def feas(rho, kappa=1e4):
    P = [cp.Variable((n, n), symmetric=True) for _ in range(N)]
    cons = []
    for i in range(N):
        cons += [P[i] >> np.eye(n), P[i] << kappa*np.eye(n)]
        for A in Js[i]:
            for j in {max(0,i-1), i, min(N-1,i+1)}:
                M = cp.bmat([[rho**2 * P[i], A.T @ P[j]], [P[j] @ A, P[j]]])
                cons.append((M + M.T)/2 >> 0)
    pr = cp.Problem(cp.Minimize(sum(cp.trace(p) for p in P)), cons)
    try: pr.solve(solver=cp.CLARABEL)
    except Exception as e: print("err", e); return False, None
    return pr.status.startswith("optimal"), [p.value for p in P]
for rho in [float(a) for a in sys.argv[1:]]:
    ok, Ps = feas(rho); print(rho, ok, flush=True)
    if ok: np.save(f"PF_{rho}.npy", np.array(Ps))
