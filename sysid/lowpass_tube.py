"""Tube widths when the residual is bandwidth-limited (r' = rho r + (1-rho) w, |w| <= D)
instead of an arbitrary per-tick box, with and without compensating the measured residual."""
import sys
import numpy as np
sys.path.insert(0, 'sysid')
import tube as T
import tvlqr_tube as V

FLOOR = np.array([0.03, 0.03, 0.027, 0.034, 0.001, 0.014])

def widths(name, X0, rho, scale, known_r0, comp):
    rw = T.RUNWAYS[name]
    xs, us = V.nominal(X0, rw); N = len(xs)
    AB = [V.lin(xs[k], us[k]) for k in range(N)]
    Q = np.diag([1e-4, 1, 1, 4, 400, 25, 1e-3]); R = np.diag([1 / 0.03**2, 1 / 0.3**2])
    P = Q.copy(); Ks = [None] * N
    for k in reversed(range(N)):
        A, B = AB[k]; Ks[k] = np.linalg.solve(R + B.T @ P @ B, B.T @ P @ A); P = Q + A.T @ P @ (A - B @ Ks[k])
    D = np.diag(list(FLOOR * scale) + [0])
    # augmented state [e (7), r (7)]; r enters the plant additively
    n = 14
    G = np.zeros((n, 7)); G[7:, :] = D * (0.1 if known_r0 else 1.0)
    W = np.zeros((n, 7)); W[7:, :] = (1 - rho) * D
    rads = []
    for k in range(N):
        A, B = AB[k]; Acl = A - B @ Ks[k]
        M = np.zeros((n, n)); M[:7, :7] = Acl; M[7:, 7:] = rho * np.eye(7)
        M[:7, 7:] = np.eye(7) - (rho * np.eye(7) if comp else 0)   # comp: cancel last measured r
        G = T.reduce(np.hstack([M @ G, W]), 80)
        rads.append(np.abs(G[:7]).sum(1))
    r = np.array(rads)
    return r[:, 1].max(), r[-1, 3], r[:, 4].max()

def widths_ff(name, X0, rho, scale, Rd=(1 / 0.03**2, 1 / 0.3**2)):
    """Realizable compensation: LQR on [e; r] uses the measured residual only through the actuators."""
    rw = T.RUNWAYS[name]
    xs, us = V.nominal(X0, rw); N = len(xs)
    AB = [V.lin(xs[k], us[k]) for k in range(N)]
    n = 14
    Q = np.diag([1e-4, 1, 1, 4, 400, 25, 1e-3] + [0] * 7); R = np.diag(Rd)
    Aa, Ba = [], []
    for A, B in AB:
        M = np.zeros((n, n)); M[:7, :7] = A; M[:7, 7:] = np.eye(7); M[7:, 7:] = rho * np.eye(7)
        Bm = np.zeros((n, 2)); Bm[:7] = B
        Aa.append(M); Ba.append(Bm)
    P = Q.copy(); Ks = [None] * N
    for k in reversed(range(N)):
        A, B = Aa[k], Ba[k]; Ks[k] = np.linalg.solve(R + B.T @ P @ B, B.T @ P @ A); P = Q + A.T @ P @ (A - B @ Ks[k])
    D = np.diag(list(FLOOR * scale) + [0])
    G = np.zeros((n, 7)); G[7:, :] = 0.1 * D
    W = np.zeros((n, 7)); W[7:, :] = (1 - rho) * D
    rads, umax = [], np.zeros(2)
    for k in range(N):
        Acl = Aa[k] - Ba[k] @ Ks[k]
        umax = np.maximum(umax, np.abs(Ks[k] @ G).sum(1))
        G = T.reduce(np.hstack([Acl @ G, W]), 80)
        rads.append(np.abs(G[:7]).sum(1))
    r = np.array(rads)
    return r[:, 1].max(), r[-1, 3], r[:, 4].max(), umax

for rho in [0.9, 0.97]:
    h, vz, th, um = widths_ff('MESA', [2300, 300, 40, 0, 0.06, 0, 0.2], rho, 1.0)
    print(f'rho={rho} realizable feedforward: h±{h:.2f} m  touchdown vz±{vz:.2f}  th±{th:.3f}  input dev elev-rate±{um[0]:.3f} thr±{um[1]:.2f}')

for rho in [0.9, 0.97]:
    for known, comp in [(False, False), (True, False), (True, True)]:
        h, vz, th = widths('MESA', [2300, 300, 40, 0, 0.06, 0, 0.2], rho, 1.0, known, comp)
        print(f'rho={rho} r0 known={known!s:5s} compensate={comp!s:5s}: h±{h:.2f} m  touchdown vz±{vz:.2f} m/s  th±{th:.3f}')
