"""Untrusted zonotope tube estimate for the 2D model's autoland under a per-tick box D."""
import math, sys
import numpy as np

DT, G = 1 / 16, 9.81
kN, TAU, FLOOR, kD, TMAX = 0.056, 0.268, 0.5, 0.0006, 5.0
kE, kA, kQ, ELEV_STEP = 0.00131, 0.0036, 0.084, 0.125
TERRAIN = [(-400, 50), (0, 50), (700, 50), (1100, 60), (1400, 110), (1700, 180), (1850, 215),
           (2000, 195), (2200, 250), (2300, 240), (2550, 170), (2850, 125), (3100, 120),
           (3300, 120), (4100, 120), (4400, 165), (4750, 250), (5000, 310), (5150, 290),
           (5300, 360), (5450, 300), (5750, 200), (6100, 110), (6500, 50), (6900, 30),
           (8000, 30), (8200, 60), (8500, 200), (8800, 420), (9200, 560)]
RUNWAYS = {'MESA': (3350, 4050, 120), 'VALLEY': (6950, 7900, 30)}
TX, TZ = np.array([p[0] for p in TERRAIN], float), np.array([p[1] for p in TERRAIN], float)
NAMES = ['x', 'h', 'vx', 'vz', 'th', 'q', 'el', 'iv', 'iz']

def terrain(x): return float(np.interp(x, TX, TZ))

def max_terrain(a, b):
    inside = TZ[(TX > a) & (TX < b)]
    return max([terrain(a), terrain(b)] + list(inside))

def clamp(v, lo, hi): return min(hi, max(lo, v))

def lift_shape(a, t):
    if a > t: return max(t - (a - t), FLOOR * t)
    if a < -t: return -max(t - (-a - t), FLOOR * t)
    return a

def control(X, rw):
    x, h, vx, vz, th, q, el, iv, iz = X
    start, stop, elev = rw
    dx, dz = math.cos(th), math.sin(th)
    u = max(vx * dx + vz * dz, 15.0)
    dist = start + 200 - x
    h_glide = elev + 0.07 * dist
    clear_end = min(x + 800, start - 150)
    h_clear = max_terrain(x, clear_end) + 60 if x < clear_end else h_glide - 100
    h_ref = max(h_glide, h_clear)
    ff = -0.07 * u * clamp((h_glide - h_clear) / 20 + 0.5, 0, 1)
    hab = h - elev
    vz_cmd = max(clamp(0.25 * (h_ref - h) + ff, -6, 6), -(0.4 + 0.12 * hab))
    v_t = 34 + 6 * clamp((dist - 1200) / 600, 0, 1)
    thr = clamp(0.45 + 0.15 * (v_t - u) + iv, 0, 1)
    w = clamp((x - (start - 200)) / 100, 0, 1)
    thr *= 1 - w * (1 - clamp((hab - 1) / 8, 0, 1))
    aNc = clamp(G + 1.2 * (vz_cmd - vz) + iz, 2, 25)
    tanA = clamp(aNc / (kN * u * u), -0.1, 0.21)
    stick = clamp(2.75 * tanA - 0.3 * q, -1, 1)
    iv2 = clamp(iv + DT * 0.05 * (v_t - u), -0.4, 0.4)
    iz2 = clamp(iz + DT * 0.4 * (vz_cmd - vz), -5, 5)
    return stick, thr, iv2, iz2

def F(X, rw):
    x, h, vx, vz, th, q, el, iv, iz = X
    stick, thr, iv2, iz2 = control(X, rw)
    dx, dz = math.cos(th), math.sin(th)
    u = vx * dx + vz * dz
    a = vx * dz - vz * dx
    up = max(u, 0.0)
    aN = kN * up * lift_shape(a, TAU * up)
    drag = kD * up
    ax = TMAX * thr * dx - aN * dz - drag * vx
    az = TMAX * thr * dz + aN * dx - drag * vz - G
    qdot = kE * up * up * el - kA * up * a - kQ * up * q
    el2 = el + clamp(stick - el, -ELEV_STEP, ELEV_STEP)
    return np.array([x + DT * vx, h + DT * vz, vx + DT * ax, vz + DT * az, th + DT * q,
                     q + DT * qdot, el2, iv2, iz2])

def jac(X, rw, eps=1e-4):
    f0 = F(X, rw)
    J = np.zeros((9, 9))
    for i in range(9):
        Xp = X.copy(); Xp[i] += eps
        J[:, i] = (F(Xp, rw) - f0) / eps
    return f0, J

def reduce(Gm, m):
    if Gm.shape[1] <= m: return Gm
    score = np.abs(Gm).sum(0) - np.abs(Gm).max(0)
    idx = np.argsort(-score)
    keep, rest = Gm[:, idx[:m - 9]], Gm[:, idx[m - 9:]]
    return np.hstack([keep, np.diag(np.abs(rest).sum(1))])

def tube(X0, rw, D, mode='zono', ticks=4000, samples=24, order=40, seed=0):
    rng = np.random.default_rng(seed)
    dbox = np.diag([0.02, 0.02, D, D, 0.004, D / 3, 0, 0, 0])
    c = F(X0, rw)
    Gm = dbox.copy()
    out = []
    for k in range(ticks):
        rad = np.abs(Gm).sum(1)
        out.append((c.copy(), rad.copy()))
        if c[1] - rad[1] < rw[2] - 0.5 and c[1] + rad[1] <= rw[2]:
            break
        if rad[1] > 500: break
        f0, J = jac(c, rw)
        if mode == 'zono':
            lin = J @ Gm
        else:
            lin = np.diag(np.abs(J) @ rad)
        dev = np.zeros(9)
        for _ in range(samples):
            p = c + Gm @ rng.choice([-1.0, 1.0], Gm.shape[1])
            dev = np.maximum(dev, np.abs(F(p, rw) - f0 - J @ (p - c)))
        Gm = reduce(np.hstack([lin, np.diag(1.5 * dev), dbox]), order)
        c = f0
    return out

def nominal(X0, rw, ticks=4000):
    X = X0.copy(); traj = [X]
    for _ in range(ticks):
        X = F(X, rw); traj.append(X)
        if X[1] <= rw[2]: break
    return traj

def assess(out, rw):
    start, stop, elev = rw
    worst_clear, td = math.inf, []
    for c, r in out:
        lo, hi = c - r, c + r
        over_rw = lo[0] >= start and hi[0] <= stop
        if not over_rw and lo[1] > elev + 0.5:
            worst_clear = min(worst_clear, lo[1] - max_terrain(lo[0], hi[0]))
        if lo[1] <= elev + 0.5:
            td.append((lo, hi, over_rw))
    if not td:
        return worst_clear, None
    sink = min(t[0][3] for t in td)
    pitch = (min(t[0][4] for t in td), max(t[1][4] for t in td))
    on_rw = all(t[2] for t in td)
    return worst_clear, (sink, pitch, on_rw, len(td))

STARTS = [('MESA', 1500, 220, 40), ('MESA', 2300, 300, 40), ('MESA', 2800, 200, 38),
          ('VALLEY', 5400, 450, 35), ('VALLEY', 6000, 300, 40)]

def main():
    modes = sys.argv[1:] or ['zono']
    for mode in modes:
        print(f'=== {mode}')
        for D in [0.0, 0.01, 0.02, 0.03, 0.05, 0.1]:
            for name, x, h, v in STARTS:
                rw = RUNWAYS[name]
                X0 = np.array([x, h, v, 0, 0.06, 0, 0.2, 0, 0], float)
                nom = nominal(X0, rw)
                out = tube(X0, rw, D, mode)
                clear, td = assess(out, rw)
                maxw = {n: max(r[i] for _, r in out) for i, n in enumerate(NAMES[:6])}
                ok = td is not None and td[0] >= -3 and td[1][0] >= -0.05 and td[1][1] <= 0.26 \
                    and td[2] and clear >= 8
                tds = 'no touchdown window' if td is None else \
                    f'sink>={td[0]:.2f} pitch[{td[1][0]:.3f},{td[1][1]:.3f}] onRwy={td[2]} win={td[3]}'
                print(f'D={D:.2f} {name:6s} from x={x}: ticks={len(out)} nomTicks={len(nom)} '
                      f'clear>={clear:.1f} {tds} | halfwidth h={maxw["h"]:.2f} vz={maxw["vz"]:.2f} '
                      f'vx={maxw["vx"]:.2f} x={maxw["x"]:.1f} -> {"OK" if ok else "FAIL"}')

if __name__ == '__main__':
    main()
