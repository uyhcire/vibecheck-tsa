import numpy as np
from scipy.linalg import solve_discrete_lyapunov, sqrtm
Js = list(np.load("Jys.npy")); n = Js[0].shape[0]
def rho_of(P, J):
    L = np.linalg.cholesky(P); Li = np.linalg.inv(L)
    return np.linalg.norm(L.T @ J @ np.linalg.inv(L.T), 2)
# Lyapunov for the average J, scaled-up dynamics (J/r) to get a margin
Jm = sum(Js) / len(Js)
for r in [1.0, 0.995, 0.99]:
    for Q in [np.eye(n)]:
        P = solve_discrete_lyapunov((Jm / r).T, Q)
        rs = [rho_of(P, J) for J in Js]
        print(r, "max rho", max(rs), "cond", np.linalg.cond(P))
