"""Untrusted zonotope tubes for a climb-out escape on the 2D model under residual models."""
import csv, math, sys
import numpy as np
sys.path.insert(0, 'sysid')
import tube as T
import tvlqr_tube as V

CLEAR = 8.0
COMPS = ['rx', 'rh', 'rvx', 'rvz', 'rth', 'rq']

def residual_bounds(path):
    rows = list(csv.DictReader(open(path)))
    A = np.array([[float(r[c]) for c in COMPS] for r in rows])
    ep = np.array([float(r['ep']) for r in rows]); k = np.array([float(r['k']) for r in rows])
    same = (ep[1:] == ep[:-1]) & (k[1:] == k[:-1] + 1)
    return np.abs(A).max(0), np.abs(A[1:] - A[:-1])[same].max(0)

def climb_ctl(X):
    x, h, vx, vz, th, q, el = X
    dx, dz = math.cos(th), math.sin(th)
    u = max(vx * dx + vz * dz, 15.0)
    gam = math.atan2(vz, max(vx, 1.0))
    gam_c = T.clamp(0.15 + 0.03 * (u - 35), -0.05, 0.25)
    aNc = T.clamp(T.G * math.cos(gam) + u * 1.2 * (gam_c - gam), 2, 25)
    tanA = T.clamp(aNc / (T.kN * u * u), -0.1, 0.21)
    stick = T.clamp(2.75 * tanA - 0.3 * q, -1, 1)
    return T.clamp(0.5 * (stick - el), -0.06, 0.06), 1.0

def F(X):
    de, thr = climb_ctl(X)
    return V.plant(X, de, thr)

def jac(X, eps=1e-5):
    f0 = F(X); J = np.zeros((7, 7))
    for i in range(7):
        Xp = X.copy(); Xp[i] += eps; J[:, i] = (F(Xp) - f0) / eps
    return f0, J

def terminal(lo, hi):
    if lo[3] < 1.0 or max(abs(lo[5]), abs(hi[5])) > 0.05:
        return False
    slope = lo[3] / max(hi[2], 1.0)
    for X, Z in T.TERRAIN:
        if X > lo[0] and lo[1] + slope * (X - hi[0]) < Z + CLEAR:
            return False
    return True

def certify(X0, model, Dmag, Drate, max_ticks=960, samples=16, seed=0):
    rng = np.random.default_rng(seed)
    walk = model == 'walk'
    n = 13 if walk else 7
    c = np.concatenate([F(X0), np.zeros(6)]) if walk else F(X0)
    if model == 'box':
        W = np.zeros((n, 6)); W[:6, :6] = np.diag(Dmag)
    elif model == 'walk':
        W = np.zeros((n, 6)); W[7:, :] = np.diag(Drate)
    else:
        W = np.zeros((n, 0))
    Gm = W.copy()
    for k in range(max_ticks):
        rad = np.abs(Gm).sum(1) if Gm.shape[1] else np.zeros(n)
        lo, hi = c[:7] - rad[:7], c[:7] + rad[:7]
        if lo[1] - T.max_terrain(lo[0], hi[0]) < CLEAR or rad[1] > 200:
            return False, k, rad[1]
        if terminal(lo, hi):
            return True, k, rad[1]
        f0, J = jac(c[:7])
        if walk:
            M = np.zeros((n, n)); M[:7, :7] = J; M[:6, 7:] = np.eye(6); M[7:, 7:] = np.eye(6)
            cn = np.concatenate([f0 + np.concatenate([c[7:], [0]]), c[7:]])
        else:
            M, cn = J, f0
        lin = M @ Gm if Gm.shape[1] else Gm
        dev = np.zeros(n)
        for _ in range(samples if Gm.shape[1] else 0):
            p = c + Gm @ rng.choice([-1.0, 1.0], Gm.shape[1])
            fp = F(p[:7]) + (np.concatenate([p[7:], [0]]) if walk else 0)
            dev[:7] = np.maximum(dev[:7], np.abs(fp - cn[:7] - (M @ (p - c))[:7]))
        Gm = T.reduce(np.hstack([lin, np.diag(1.5 * dev), W]), 60) if Gm.shape[1] else W.copy()
        c = cn
    return False, max_ticks, 0.0

def main():
    Dmag, Drate = residual_bounds(sys.argv[1])
    print('residual max per tick (x,h,vx,vz,th,q):', np.round(Dmag, 4))
    print('residual change max per tick         :', np.round(Drate, 4))
    starts = []
    for x in range(600, 6001, 300):
        for dh in (25, 60, 120):
            for u in (30, 42, 55):
                for g in (-0.1, 0.05):
                    h = T.terrain(x) + dh
                    starts.append(np.array([x, h, u * math.cos(g), u * math.sin(g), g + 0.06, 0, 0.2]))
    models = [('nominal (D=0)', 'none'), ('box, D = max', 'box'), ('rate-bounded walk', 'walk')]
    if '--scale' in sys.argv:
        s = float(sys.argv[sys.argv.index('--scale') + 1]); Dmag = Dmag * s; Drate = Drate * s
    for label, model in models:
        res = [certify(X0, model, Dmag, Drate) for X0 in starts]
        ok = [r for r in res if r[0]]
        tk = np.median([r[1] for r in ok]) / 16 if ok else float('nan')
        hw = np.median([r[2] for r in ok]) if ok else float('nan')
        print(f'{label:20s}: certified {len(ok):3d}/{len(starts)}  median time to terminal {tk:5.1f} s  '
              f'median h half-width there {hw:.2f} m')

if __name__ == '__main__':
    main()
