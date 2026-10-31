"""Linear tube widths for a time-varying LQR tracking controller around a nominal approach."""
import math, sys
import numpy as np
sys.path.insert(0, 'sysid')
import tube as T

def plant(X, de, thr):
    x, h, vx, vz, th, q, el = X
    dx, dz = math.cos(th), math.sin(th)
    u = vx * dx + vz * dz; a = vx * dz - vz * dx; up = max(u, 0.0)
    aN = T.kN * up * T.lift_shape(a, T.TAU * up); drag = T.kD * up
    ax = T.TMAX * thr * dx - aN * dz - drag * vx
    az = T.TMAX * thr * dz + aN * dx - drag * vz - T.G
    qdot = T.kE * up * up * el - T.kA * up * a - T.kQ * up * q
    return np.array([x + T.DT * vx, h + T.DT * vz, vx + T.DT * ax, vz + T.DT * az,
                     th + T.DT * q, q + T.DT * qdot, el + de])

def lin(X, U, eps=1e-5):
    f0 = plant(X, *U); A = np.zeros((7, 7)); B = np.zeros((7, 2))
    for i in range(7):
        Xp = X.copy(); Xp[i] += eps; A[:, i] = (plant(Xp, *U) - f0) / eps
    for j in range(2):
        Up = list(U); Up[j] += eps; B[:, j] = (plant(X, *Up) - f0) / eps
    return A, B

def nominal(X0, rw):
    X = np.array(list(X0) + [0, 0], float); xs, us = [], []
    for _ in range(4000):
        stick, thr, iv, iz = T.control(X, rw)
        de = T.clamp(stick - X[6], -T.ELEV_STEP, T.ELEV_STEP)
        xs.append(X[:7].copy()); us.append((de, thr))
        X = T.F(X, rw)
        if X[1] <= rw[2]: break
    return xs, us

def run(name, X0, D, Qd, Rd, dvec):
    rw = T.RUNWAYS[name]
    xs, us = nominal(X0, rw)
    N = len(xs)
    AB = [lin(xs[k], us[k]) for k in range(N)]
    Q, R = np.diag(Qd), np.diag(Rd)
    P = Q.copy(); Ks = [None] * N
    for k in reversed(range(N)):
        A, B = AB[k]
        K = np.linalg.solve(R + B.T @ P @ B, B.T @ P @ A)
        Ks[k] = K
        P = Q + A.T @ P @ (A - B @ K)
    dbox = np.diag(list(np.array(dvec) * D) + [0])
    Gm = dbox.copy(); rads = []; umax = np.zeros(2)
    for k in range(N):
        A, B = AB[k]; K = Ks[k]
        Acl = A - B @ K
        umax = np.maximum(umax, np.abs(K @ Gm).sum(1))
        Gm = T.reduce(np.hstack([Acl @ Gm, dbox]), 60) if Gm.shape[1] > 0 else dbox
        rads.append(np.abs(Gm).sum(1))
    r = np.array(rads)
    if '--horizon' in sys.argv:
        print('  h/vz halfwidth at 5,10,20,40 s:', [(round(r[min(k,N-1),1],2), round(r[min(k,N-1),3],2)) for k in (80,160,320,640)])
    last = r[-1]
    print(f's={D:.2f} R={Rd[0]**-0.5:.3f},{Rd[1]**-0.5:.2f} {name:6s} N={N}: max h±{r[:,1].max():.2f} vz±{r[:,3].max():.2f} vx±{r[:,2].max():.2f} '
          f'th±{r[:,4].max():.3f} x±{r[:,0].max():.1f} | touchdown h±{last[1]:.2f} vz±{last[3]:.2f} '
          f'th±{last[4]:.3f} | input dev elev-rate±{umax[0]:.3f}/tick thr±{umax[1]:.2f}')

if __name__ == '__main__':
    FLOOR = [0.03, 0.03, 0.027, 0.034, 0.001, 0.014]   # measured max residual floor (4 substeps)
    Qd = [1e-4, 1 / 1.0**2, 1 / 1.0**2, 1 / 0.5**2, 1 / 0.05**2, 1 / 0.2**2, 1e-3]
    for Rd in ([1 / 0.03**2, 1 / 0.3**2], [1 / 0.01**2, 1 / 0.1**2]):
        for scale in [0.5, 1.0, 2.0]:
            for name, x, h, v in T.STARTS[1:4]:
                run(name, [x, h, v, 0, 0.06, 0, 0.2], scale, Qd, Rd, FLOOR)
