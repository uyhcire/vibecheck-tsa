import numpy as np, cvxpy as cp
AsAll = np.load("As.npy"); n = 7
def best_rho(As):
    def feas(rho):
        P = cp.Variable((n, n), symmetric=True)
        cons = [P >> np.eye(n), P << 1e5*np.eye(n)] + [rho**2*P - A.T@P@A >> 0 for A in As]
        pr = cp.Problem(cp.Minimize(cp.lambda_max(P)), cons)
        try: pr.solve(solver=cp.CLARABEL)
        except Exception: return False
        return pr.status.startswith("optimal")
    lo, hi = 0.9, 1.0
    for _ in range(12):
        mid=(lo+hi)/2
        if feas(mid): hi=mid
        else: lo=mid
    return hi
hs = [100, 300, 500, 800, 1000, 1300, 1500, 1800, 2000, 2200, 2400, 2450, 2500, 2550, 2600, 2619, 2650, 2700]
print("scale1 all h:", best_rho(AsAll[:18]))
print("scale4 all h:", best_rho(AsAll[18:]))
for i, h in enumerate(hs):
    print(h, "both scales:", round(best_rho([AsAll[i], AsAll[18+i]]), 5), " spectral:", round(max(abs(np.linalg.eigvals(AsAll[i]))),5))
