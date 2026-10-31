"""Climb-out vs landing escapes under the Lean port's measured residuals, with TV-LQR (elevator
only) linear tubes. Untrusted estimate on the 2D model's float copy."""
import math, sys
import numpy as np
sys.path.insert(0, 'sysid')
import tube as T
import tvlqr_tube as V
import climbout_tube as C

def nominal_climb(X0, ticks=960):
    X = X0.copy(); xs, us = [], []
    for _ in range(ticks):
        de, thr = C.climb_ctl(X); xs.append(X.copy()); us.append((de, thr)); X = V.plant(X, de, thr)
    return xs, us

def nominal_land(X0, rw):
    xs, us = V.nominal(list(X0), rw)
    return xs, us

def tube_widths(xs, us, model, Dmag, Drate, nu=1):
    N = len(xs)
    AB = [V.lin(xs[k], us[k]) for k in range(N)]
    Q = np.diag([1e-4, 1, 1, 4, 400, 25, 1e-3]); R = np.diag([1 / 0.03**2, 1 / 0.3**2][:nu])
    P = Q.copy(); Ks = [None] * N
    for k in reversed(range(N)):
        A, B = AB[k]; B = B[:, :nu]
        Ks[k] = np.linalg.solve(R + B.T @ P @ B, B.T @ P @ A); P = Q + A.T @ P @ (A - B @ Ks[k])
    G = np.zeros((7, 0)); rads, dev = [], []
    for k in range(N):
        A, B = AB[k]; Acl = A - B[:, :nu] @ Ks[k]
        dev.append(np.abs(Ks[k] @ G).sum(1) if G.shape[1] else np.zeros(nu))
        w = Dmag if model == 'box' else np.minimum((k + 1) * Drate, Dmag)
        W = np.zeros((7, 6)); W[:6, :] = np.diag(w)
        G = T.reduce(np.hstack([Acl @ G, W]) if G.shape[1] else W, 60)
        rads.append(np.abs(G).sum(1))
    return np.array(rads), np.array(dev)

def check_climb(xs, us, rads, de_dev):
    for k in range(len(xs) - 1):
        c, r = xs[k + 1], rads[k]
        lo, hi = c - r, c + r
        if abs(us[k][0]) + de_dev[k][0] > T.ELEV_STEP:
            return False, k, 'elevator rate'
        if lo[1] - T.max_terrain(lo[0], hi[0]) < C.CLEAR:
            return False, k, 'clearance'
        if C.terminal(lo, hi):
            return True, k, 'ok'
    return False, len(xs), 'no terminal'

def check_land(xs, us, rads, de_dev, rw):
    start, stop, elev = rw
    for k in range(len(xs) - 1):
        c, r = xs[k + 1], rads[k]
        lo, hi = c - r, c + r
        if abs(us[k][0]) + de_dev[k][0] > T.ELEV_STEP:
            return False, k, 'elevator rate'
        if us[k][1] - de_dev[k][1] < 0 or us[k][1] + de_dev[k][1] > 1:
            return False, k, 'throttle range'
        over = lo[0] >= start and hi[0] <= stop
        if not over and lo[1] - T.max_terrain(lo[0], hi[0]) < C.CLEAR and lo[1] > elev:
            return False, k, 'clearance'
        if lo[1] <= elev + 0.5 and (lo[3] < -3 or lo[4] < -0.05 or hi[4] > 0.26 or not over):
            return False, k, 'touchdown limits'
    return True, len(xs), 'ok'

def main():
    Dmag, Drate = C.residual_bounds(sys.argv[1])
    scale = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
    Dmag, Drate = Dmag * scale, Drate * scale
    print('D (x,h,vx,vz,th,q) =', np.round(Dmag, 4), ' rate =', np.round(Drate, 4))
    starts = []
    for x in range(600, 6001, 300):
        for dh in (25, 60, 120):
            for u in (30, 42, 55):
                for g in (-0.1, 0.05):
                    starts.append(np.array([x, T.terrain(x) + dh, u * math.cos(g), u * math.sin(g), g + 0.06, 0, 0.2]))
    for model in ['box', 'rate']:
        nom_ok = cert = 0; why = {}
        for X0 in starts:
            xs, us = nominal_climb(X0)
            z = np.zeros(7)
            if not check_climb(xs, us, np.zeros((len(xs), 7)), np.zeros((len(xs), 1)))[0]:
                continue
            nom_ok += 1
            rads, dd = tube_widths(xs, us, model, Dmag, Drate, 1)
            ok, k, reason = check_climb(xs, us, rads, dd)
            cert += ok; why[reason] = why.get(reason, 0) + 1
        print(f'climb-out, {model:4s}: nominal escape works from {nom_ok}/{len(starts)}; robust tube certifies {cert}/{nom_ok}  {why}')
    for name, x, h, v in T.STARTS:
        rw = T.RUNWAYS[name]
        X0 = np.array([x, h, v, 0, 0.06, 0, 0.2])
        xs, us = nominal_land(X0, rw)
        for model in ['box', 'rate']:
            rads, dd = tube_widths(xs, us, model, Dmag, Drate, 2)
            ok, k, reason = check_land(xs, us, rads, dd, rw)
            print(f'landing at {name:6s} from x={x}, {model:4s}: {"certified" if ok else "fails: " + reason} '
                  f'(max h±{rads[:,1].max():.2f}, touchdown vz±{rads[-1,3]:.2f})')

if __name__ == '__main__':
    main()
