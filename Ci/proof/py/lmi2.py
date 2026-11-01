import numpy as np, cvxpy as cp, sys
Js = list(np.load("Jys.npy"))
n = Js[0].shape[0]
def feas(rho, solver):
    P = cp.Variable((n, n), symmetric=True)
    cons = [P >> np.eye(n), P << 1e4 * np.eye(n)]
    for Jy in Js:
        M = cp.bmat([[rho**2 * P, Jy.T @ P], [P @ Jy, P]])
        cons.append((M + M.T) / 2 >> 0)
    prob = cp.Problem(cp.Minimize(cp.trace(P)), cons)
    try:
        prob.solve(solver=solver)
    except Exception as e:
        return "error", None
    return prob.status, P.value
for rho in [float(r) for r in sys.argv[1:]]:
    st, P = feas(rho, cp.SCS)
    print(rho, st, None if P is None else (np.linalg.eigvalsh(P).min(), np.linalg.eigvalsh(P).max()))
    if P is not None and st.startswith("optimal"):
        worst = max(np.sqrt(np.linalg.eigvals(np.linalg.solve(P, Jy.T @ P @ Jy)).real.max()) for Jy in Js)
        print("  achieved rho", worst); np.save(f"P_{rho}.npy", P)
