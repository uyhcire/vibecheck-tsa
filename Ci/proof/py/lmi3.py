import numpy as np, cvxpy as cp, sys
As = list(np.load("As.npy")); n = As[0].shape[0]
def feas(rho):
    P = cp.Variable((n, n), symmetric=True)
    cons = [P >> np.eye(n), P << 1e5 * np.eye(n)]
    for A in As:
        cons.append(rho**2 * P - A.T @ P @ A >> 0)
    prob = cp.Problem(cp.Minimize(cp.lambda_max(P)), cons)
    try: prob.solve(solver=cp.CLARABEL)
    except Exception as e: return "error", None
    return prob.status, P.value
def worst(P): 
    L = np.linalg.cholesky(P)
    return max(np.linalg.norm(L.T @ A @ np.linalg.inv(L.T), 2) for A in As)
lo, hi = 0.97, 1.0; best=None
for _ in range(10):
    mid = (lo+hi)/2; st, P = feas(mid)
    ok = st.startswith("optimal") and P is not None and worst(P) < 1
    print(f"{mid:.5f} {st}", f"worst {worst(P):.5f} cond {np.linalg.cond(P):.1f}" if P is not None else "")
    if ok: hi = mid; best = P
    else: lo = mid
np.save("P7.npy", best)
