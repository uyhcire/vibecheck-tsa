"""Linearisation at the frozen trim: eigenvalues, the Q of the discrete Lyapunov inequality, lambda_lin."""
import numpy as np
import scipy.linalg as sl

from tsmap import TsMap, NY, NAMES
from trim import trim, jacobian, SCALE


def lyap_q(A, mu, W=None):
    """Q solving (A/mu)^T Q (A/mu) - Q = -W, so A^T Q A = mu^2 (Q - W) < mu^2 Q."""
    n = A.shape[0]
    W = np.eye(n) if W is None else W
    return sl.solve_discrete_lyapunov((A / mu).T, W)


def qnorm(A, Q):
    """Induced norm of A in ||x||_Q = sqrt(x^T Q x): sqrt(lambda_max(Q^{-1/2} A^T Q A Q^{-1/2}))."""
    L = np.linalg.cholesky(Q)          # Q = L L^T, ||x||_Q = ||L^T x||
    M = L.T @ A @ np.linalg.inv(L.T)
    return np.linalg.norm(M, 2)


if __name__ == "__main__":
    np.set_printoptions(linewidth=200, precision=6)
    m = TsMap()
    r = m.run(0, 0, 300, 40, 0, 0, 0, 1, 1, 128 * 60, 128 * 60)
    h0, y0 = r[-1][4], r[-1][5:]
    ys, _ = trim(m, h0, y0)
    D = np.diag(SCALE)
    Jref = np.linalg.inv(D) @ jacobian(m, h0, ys, 1e-5) @ D
    for rel in (1e-4, 1e-6, 1e-7):
        J = jacobian(m, h0, ys, rel)
        Js = np.linalg.inv(D) @ J @ D
        print("rel", rel, "max scaled diff vs rel=1e-5", np.max(np.abs(Js - Jref)))
    J = jacobian(m, h0, ys, 1e-5)
    ev = np.linalg.eigvals(J)
    idx = np.argsort(-np.abs(ev))
    print("eigs |.| top 12", np.abs(ev[idx[:12]]))
    print("eigs top 12", ev[idx[:12]])
    print("continuous rates (1/s)", (np.log(ev[idx[:12]]) * 128))
    print("spectral radius", np.max(np.abs(ev)))
