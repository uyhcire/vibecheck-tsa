"""Fit the Lean 2D model's parameters to JSBSim c172p ticks; report one-tick residuals."""
import csv, math, sys
import numpy as np
from scipy.optimize import least_squares

DT = 1 / 16
G = 9.81
FLOOR = 0.5
# Defaults from Vibecheck/Model.lean (P.*).
BASE0 = dict(kN=0.056, tau=0.268, kD=0.0006, T0=5.0, kE=0.00131, kA=0.0036, kQ=0.084)
EXT0 = dict(BASE0, a0=0.0, T1=0.0, m0=0.0)

def load(path):
    rows = list(csv.DictReader(open(path)))
    cols = ['x', 'h', 'vx', 'vz', 'theta', 'q', 'elev', 'thr', 'alpha']
    A = np.array([[float(r[c]) for c in cols] for r in rows])
    ep = np.array([int(r['ep']) for r in rows])
    same = ep[:-1] == ep[1:]
    return A[:-1][same], A[1:][same]

def lift_shape(a, t):
    hi = np.maximum(t - (a - t), FLOOR * t)
    lo = -np.maximum(t - (-a - t), FLOOR * t)
    return np.where(a > t, hi, np.where(a < -t, lo, a))

SUBSTEPS = 1

def step(S, p):
    for _ in range(SUBSTEPS):
        S = substep(S, p, DT / SUBSTEPS)
    return S

def substep(S, p, DT):
    """Vectorised float port of the flying branch of stepAir (plus optional extensions)."""
    x, h, vx, vz, th, q, elev, thr = S[:, 0], S[:, 1], S[:, 2], S[:, 3], S[:, 4], S[:, 5], S[:, 6], S[:, 7]
    dx, dz = np.cos(th), np.sin(th)
    u = vx * dx + vz * dz
    a = vx * dz - vz * dx
    up = np.maximum(u, 0)
    aN = p['kN'] * up * lift_shape(a + p.get('a0', 0) * up, p['tau'] * up)
    aT = thr * (p['T0'] - p.get('T1', 0) * up)
    drag = p['kD'] * up
    ax = aT * dx - aN * dz - drag * vx
    az = aT * dz + aN * dx - drag * vz - G
    qdot = p['kE'] * up * up * elev - p['kA'] * up * a - p['kQ'] * up * q + p.get('m0', 0) * up * up
    return np.concatenate([np.stack([x + DT * vx, h + DT * vz, vx + DT * ax, vz + DT * az, th + DT * q, q + DT * qdot], 1), S[:, 6:]], 1)

NAMES = ['x', 'h', 'vx', 'vz', 'theta', 'q']

def residuals(S, S1, p):
    pred = step(S, p)[:, :6]
    actual = S1[:, :6]
    r = actual - pred
    r[:, 4] = (r[:, 4] + math.pi) % (2 * math.pi) - math.pi
    return r

def report(label, r, mask=None):
    if mask is not None:
        r = r[mask]
    print(f'  {label}  (n={len(r)})')
    print('    comp      p50       p90       p99     p99.9       max')
    for i, n in enumerate(NAMES):
        a = np.abs(r[:, i])
        qs = np.quantile(a, [0.5, 0.9, 0.99, 0.999])
        print(f'    {n:6s}' + ''.join(f'{v:10.4f}' for v in qs) + f'{a.max():10.4f}')

def fit(S, S1, p0, keys):
    scale = np.array([0.05, 0.05, 0.01])          # vx, vz, q residual scales
    def f(v):
        p = dict(p0, **dict(zip(keys, v)))
        return (residuals(S, S1, p)[:, [2, 3, 5]] / scale).ravel()
    sol = least_squares(f, [p0[k] for k in keys], loss='soft_l1', f_scale=3.0)
    return dict(p0, **dict(zip(keys, sol.x)))

def main():
    global SUBSTEPS
    SUBSTEPS = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    S, S1 = load(sys.argv[1])
    T, T1 = load(sys.argv[2])
    print(f'train ticks {len(S)}, test ticks {len(T)}')
    stall = np.abs(T[:, 8]) > math.radians(14)
    print('\n== defaults from Model.lean, test set')
    report('all', residuals(T, T1, BASE0))
    pb = fit(S, S1, BASE0, list(BASE0))
    print('\n== base structure, fitted:', {k: round(v, 5) for k, v in pb.items()})
    rb = residuals(T, T1, pb)
    report('all', rb); report('alpha>14deg', rb, stall)
    pe = fit(S, S1, EXT0, list(EXT0))
    print('\n== extended (alpha offset, thrust slope, pitch-moment offset), fitted:',
          {k: round(v, 5) for k, v in pe.items()})
    re = residuals(T, T1, pe)
    report('all', re); report('alpha>14deg', re, stall)
    np.save(sys.argv[3], re)

if __name__ == '__main__':
    main()
