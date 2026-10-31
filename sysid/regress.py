"""How small can one-tick residuals get? Flexible linear regression of body-axis accelerations."""
import csv, math, sys, numpy as np
DT, G = 1 / 16, 9.81
def load(path):
    rows = list(csv.DictReader(open(path)))
    cols = ['vx', 'vz', 'theta', 'q', 'elev', 'thr', 'alpha', 'phi', 'rpm', 'beta']
    A = np.array([[float(r[c]) for c in cols] for r in rows])
    ep = np.array([int(r['ep']) for r in rows])
    ok = (ep[1:-1] == ep[:-2]) & (ep[2:] == ep[1:-1])
    return A[:-2][ok], A[1:-1][ok], A[2:][ok]
def feats(P, S, N, use):
    vx, vz, th, q, el, thr, al, phi, rpm, beta = S.T
    dx, dz = np.cos(th), np.sin(th)
    u = vx * dx + vz * dz; a = vx * dz - vz * dx; up = np.maximum(u, 1)
    ap = P[:, 0] * np.sin(P[:, 2]) - P[:, 1] * np.cos(P[:, 2])
    adot = (a - ap) / DT
    F = [np.ones_like(u), up, up * up, up * a, a * a, np.abs(a) * a, up * q, up * up * el, thr, thr * up]
    if 'bank' in use: F += [up * a * (np.cos(phi) - 1), np.cos(phi) - 1]
    if 'rpm' in use: F += [rpm / 1000, (rpm / 1000) ** 2, rpm / 1000 * up]
    if 'adot' in use: F += [adot, up * adot]
    if 'beta' in use: F += [beta * beta * up * up]
    return np.stack(F, 1), dx, dz
def targets(S, N):
    vx, vz, th, q = S[:, 0], S[:, 1], S[:, 2], S[:, 3]
    dx, dz = np.cos(th), np.sin(th)
    ax = (N[:, 0] - vx) / DT; az = (N[:, 1] - vz) / DT + G
    return ax * dx + az * dz, -ax * dz + az * dx, (N[:, 3] - q) / DT
def run(use, tr, te, mask_fn=None):
    Ftr, *_ = feats(*tr, use); Fte, dx, dz = feats(*te, use)
    ttr = targets(tr[1], tr[2]); tte = targets(te[1], te[2])
    preds = []
    for k in range(3):
        coef, *_ = np.linalg.lstsq(Ftr, ttr[k], rcond=None)
        preds.append(Fte @ coef)
    eu, en, eq = [(tte[k] - preds[k]) * DT for k in range(3)]
    evx = eu * dx - en * dz; evz = eu * dz + en * dx
    m = np.ones(len(evx), bool) if mask_fn is None else mask_fn(te[1])
    out = []
    for name, e in [('vx', evx), ('vz', evz), ('q', eq)]:
        a = np.abs(e[m]); out.append(f'{name} p50 {np.quantile(a,.5):.3f} p90 {np.quantile(a,.9):.3f} p99 {np.quantile(a,.99):.3f} max {a.max():.3f}')
    print(f'  {"+".join(use) or "base":22s} n={m.sum():6d} | ' + ' | '.join(out))
tr, te = load('sysid/train.csv'), load('sysid/test.csv')
level = lambda S: np.abs(S[:, 7]) < math.radians(3)
for use in [[], ['bank'], ['bank', 'rpm'], ['bank', 'rpm', 'adot'], ['bank', 'rpm', 'adot', 'beta']]:
    run(use, tr, te)
print('wings level (|phi|<3deg) only:')
for use in [[], ['rpm', 'adot']]:
    run(use, tr, te, level)
