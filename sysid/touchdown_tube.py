"""Robust landing escape: hag-driven flare, tubes judged at contact vs time-indexed. Untrusted 2D float estimate."""
import math, sys
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, 'sysid')
import tube as T
import tvlqr_tube as V

D_BOX = np.array([0.0006, 0.0006, 0.0192, 0.0166, 0.0021, 0.0104])  # measured worst case per tick
CLEAR, BAND, EXT = 8.0, 0.25, 48
SLOPE, ROLL = math.tan(math.radians(3)), 300.0
SINK, PMIN, PMAX, VMAX = 3.0, -0.05, 0.26, 50.0

def landable_zones():
    xs = np.arange(-400, 9201, 5.0)
    ok = np.array([abs(T.terrain(x + 2.5) - T.terrain(x - 2.5)) / 5 <= SLOPE for x in xs])
    n = int(ROLL / 5)
    good = np.array([ok[i:i + n + 1].all() for i in range(len(xs))]) & (np.arange(len(xs)) + n < len(xs))
    zones, i = [], 0
    while i < len(xs):
        if good[i]:
            j = i
            while j + 1 < len(xs) and good[j + 1]: j += 1
            zones.append((xs[i], xs[j])); i = j + 1
        else: i += 1
    return zones

ZONES = landable_zones()

def in_zone(lo, hi): return any(lo >= a and hi <= b for a, b in ZONES)

def hag(X): return X[1] - T.terrain(X[0])

def ctl(X, P):
    x, h, vx, vz, th, q, el = X
    dx, dz = math.cos(th), math.sin(th)
    u = max(vx * dx + vz * dz, 15.0)
    g = h - T.terrain(x)
    if P['mode'] == 'pow':
        dist = P['xa'] - x
        h_glide = P['zg'] + 0.07 * dist
        end = min(x + 800, P['xa'] - 400)
        h_clear = T.max_terrain(x, end) + 40 if x < end else h_glide - 100
        h_ref = max(h_glide, h_clear)
        ff = -0.07 * u * T.clamp((h_glide - h_clear) / 20 + 0.5, 0, 1)
        vz_cmd = T.clamp(P.get('kh', 0.25) * (h_ref - h) + ff, -6, 6)
        v_t = 34 + 6 * T.clamp((dist - 1200) / 600, 0, 1)
        w = T.clamp((300 - dist) / 100, 0, 1)
        thr = (0.45 + P.get('kv', 0.15) * (v_t - u)) * (1 - w * (1 - T.clamp((g - 1) / 8, 0, 1)))
    else:
        vz_cmd = T.clamp(-0.1 * u + 0.4 * (u - P['vg']), -6, 3)
        thr = 0.0
    vz_cmd = max(vz_cmd, -(P['f0'] + P['f1'] * g))
    aNc = T.clamp(T.G + P.get('kz', 1.2) * (vz_cmd - vz), 2, 25)
    tanA = T.clamp(aNc / (T.kN * u * u), -0.1, 0.21)
    stick = T.clamp(2.75 * tanA - P.get('kq', 0.3) * q, -1, 1)
    return stick - el, thr

def ctl_clipped(X, P):
    de, thr = ctl(X, P)
    return T.clamp(de, -T.ELEV_STEP, T.ELEV_STEP), T.clamp(thr, 0, 1)

def Fcl(X, P):
    de, thr = ctl_clipped(X, P)
    return V.plant(X, de, thr)

def grad(fn, X, k, eps=1e-5):
    f0 = fn(X)[k]; return np.array([(fn(np.where(np.arange(7) == i, X + eps, X))[k] - f0) / eps for i in range(7)])

def nominal(X0, P, ext=EXT):
    X = np.array(X0, float); xs = []; n0 = None
    for k in range(1500):
        xs.append(X.copy())
        if n0 is None and hag(X) <= 0: n0 = k
        if n0 is not None and k >= n0 + ext: break
        X = V.plant(X, 0.0, 0.0) if n0 is not None else Fcl(X, P)
        if X[1] < T.terrain(X[0]) - 50 or X[1] > 3000: break
    return xs, n0

def nominal_ok(xs, n0):
    if n0 is None: return False
    for k in range(n0):
        X = xs[k]
        if not in_zone(X[0], X[0]) and hag(X) < CLEAR: return False
    X = xs[n0]
    return in_zone(X[0], X[0]) and X[3] >= -SINK and PMIN <= X[4] <= PMAX and math.hypot(X[2], X[3]) <= VMAX

def slice_bounds(c, Gm):
    s = (T.terrain(c[0] + 1) - T.terrain(c[0] - 1)) / 2
    row = Gm[1] - s * Gm[0]; off = c[1] - T.terrain(c[0])
    A = np.vstack([row, -row]); b = np.array([-off, off + BAND])
    m = Gm.shape[1]; res = {}
    if linprog(np.zeros(m), A_ub=A, b_ub=b, bounds=[(-1, 1)] * m, method='highs').status != 0: return None
    rad = np.abs(Gm).sum(1)
    for name, i in (('x', 0), ('vx', 2), ('vz', 3), ('th', 4)):
        lo = linprog(Gm[i], A_ub=A, b_ub=b, bounds=[(-1, 1)] * m, method='highs')
        hi = linprog(-Gm[i], A_ub=A, b_ub=b, bounds=[(-1, 1)] * m, method='highs')
        res[name] = (c[i] + (lo.fun if lo.status == 0 else -rad[i]), c[i] - (hi.fun if hi.status == 0 else -rad[i]))
    return res

class Verdict:
    def __init__(self): self.sink = math.inf; self.flags = set(); self.pitch = [math.inf, -math.inf]; self.vx = 0.0; self.n = 0
    def add_contact(self, b):
        self.n += 1
        self.sink = min(self.sink, b['vz'][0])
        self.pitch = [min(self.pitch[0], b['th'][0]), max(self.pitch[1], b['th'][1])]
        self.vx = max(self.vx, b['vx'][1])
        if not in_zone(*b['x']): self.flags.add('off landable')
    def finish(self, touched):
        if not touched: self.flags.add('no contact')
        if self.sink < -SINK: self.flags.add('sink')
        if self.pitch[0] < PMIN or self.pitch[1] > PMAX: self.flags.add('pitch')
        if math.hypot(self.vx, SINK) > VMAX: self.flags.add('speed')
        return self

def judge_clearance(v, lo, hi, g_c):
    if g_c > 0 and not in_zone(lo[0], hi[0]) and lo[1] - T.max_terrain(lo[0], hi[0]) < CLEAR: v.flags.add('clearance')

QT = [1e-4, 1, 1, 4, 400, 25, 1e-3]
DESIGNS = {'base': ([1e-4, 1, 1, 4, 400, 25, 1e-3], 0.03, 0.3),
           'flare': ([1e-6, 1e-3, 1, 100, 4000, 100, 1e-3], 0.03, 0.3),
           'lowgain': ([1e-6, 1e-3, 1, 100, 4000, 100, 1e-3], 0.01, 0.1)}
QF = QT
GATE, TFLARE = 40.0, 260

def riccati(AB, nu, R, qs):
    """Backward TV-LQR gains for a per-tick list of Q matrices."""
    N = len(AB); Pm = qs[-1].copy(); Ks = [None] * N
    for k in reversed(range(N)):
        A, B = AB[k]; B = B[:, :nu]
        Ks[k] = np.linalg.solve(R + B.T @ Pm @ B, B.T @ Pm @ A); Pm = qs[k] + A.T @ Pm @ (A - B @ Ks[k])
    return np.array(Ks)

def make_laws(xs, P, nu, el_r, thr_r, qf):
    """TV-LQR laws: time-indexed (tracking Q), time-indexed with flare Q, and flare Q indexed by hag."""
    N = len(xs); gh = np.array([hag(x) for x in xs]); n0 = int(np.argmax(gh <= 0))
    us = [ctl_clipped(x, P) if k < n0 else (0.0, 0.0) for k, x in enumerate(xs)]
    mono = 1 + max([k for k in range(N - 1) if gh[k + 1] >= gh[k] - 1e-6], default=-1)
    kg = min(max(next((k for k in range(N) if gh[k] <= GATE), N), N - EXT - TFLARE, mono), n0 - 1)
    AB = [V.lin(xs[k], us[k]) for k in range(N)]
    R = np.diag([1 / el_r**2, 1 / thr_r**2][:nu])
    K_base = riccati(AB, nu, R, [np.diag(QT)] * N)
    K_fl = riccati(AB, nu, R, [np.diag(QT) if k < kg else np.diag(qf) for k in range(N)])
    Xr = np.array(xs); Ur = np.array(us); gs = gh[kg:n0 + 1][::-1]; sl = slice(kg, n0 + 1)
    def u_of(ref_u, K, e):
        d = K @ e
        return ref_u[0] - d[0], (ref_u[1] - d[1]) if nu == 2 else 0.0
    def time_law(Kr):
        def law(X, k):
            k = min(k, N - 1)
            return (0.0, 0.0) if k >= n0 else u_of(Ur[k], Kr[k], X - Xr[k])
        return law
    t_base, t_fl = time_law(K_base), time_law(K_fl)
    def hag_law(X, k):
        if k < kg: return t_fl(X, k)
        g = hag(X); kk = min(k, n0)
        xr = np.array([np.interp(g, gs, Xr[sl][::-1][:, j]) for j in range(7)])
        ur = np.array([np.interp(g, gs, Ur[sl][::-1][:, j]) for j in range(2)])
        Kt = np.array([[np.interp(g, gs, K_fl[sl][::-1][:, i, j]) for j in range(7)] for i in range(nu)])
        xr[2] = Xr[kk][2]; ur[1] = Ur[kk][1]
        e = X - xr; e[0] = 0.0; e[1] = 0.0
        return u_of(ur, Kt, e)
    return {'lqr-time': t_base, 'lqr-time-flareQ': t_fl, 'lqr-hag': hag_law}, kg

def Fl(X, k, law):
    de, thr = law(X, k)
    return V.plant(X, de, T.clamp(thr, 0, 1))

def tube_law(xs, n0, kg, law, nu, D, samples=0, order=60, seed=0):
    """Closed-loop zonotope tube (sampled remainder). Returns contact-checked verdict and time-indexed one."""
    rng = np.random.default_rng(seed); v = Verdict(); vt = Verdict()
    W = np.zeros((7, 6)); W[:6] = np.diag(D); Gm = W.copy(); touched = False; ti = None
    for k in range(len(xs) - 1):
        c = xs[k]; f0 = Fl(c, k, law); J = np.zeros((7, 7))
        for i in range(7):
            Xp = c.copy(); Xp[i] += 1e-5; J[:, i] = (Fl(Xp, k, law) - f0) / 1e-5
        dev = np.zeros(7)
        for _ in range(samples):
            p = c + Gm @ rng.choice([-1.0, 1.0], Gm.shape[1])
            dev = np.maximum(dev, np.abs(Fl(p, k, law) - f0 - J @ (p - c)))
        rad_old = np.abs(Gm).sum(1)
        de_c, thr_c = law(c, k)
        gd = np.array([(law(np.where(np.arange(7) == i, c + 1e-5, c), k)[j] - (de_c, thr_c)[j]) / 1e-5 for j in range(2) for i in range(7)]).reshape(2, 7)
        dde, dth = np.abs(gd) @ rad_old
        for f in (v, vt):
            tag = '@flare' if k >= kg else ''
            if abs(T.clamp(de_c, -T.ELEV_STEP, T.ELEV_STEP)) + dde > T.ELEV_STEP: f.flags.add('elevator rate' + tag)
            if nu == 2 and hag(c) > 9 and (thr_c - dth < 0 or thr_c + dth > 1): f.flags.add('throttle range' + tag)
        Gm = T.reduce(np.hstack([J @ Gm, np.diag(1.5 * dev), W]), order)
        cn = xs[k + 1]; rad = np.abs(Gm).sum(1); lo, hi = cn - rad, cn + rad
        for f in (v, vt): judge_clearance(f, lo, hi, hag(c) if k < n0 else -1)
        if k + 1 == n0: ti = (lo, hi)
        if lo[1] - T.max_terrain(lo[0], hi[0]) <= 0:
            b = slice_bounds(cn, Gm)
            if b: v.add_contact(b); touched = True
        if rad[1] > 150 or not np.isfinite(rad).all(): v.flags.add('diverged'); vt.flags.add('diverged'); break
        if hi[1] - T.max_terrain(lo[0], hi[0]) < -BAND and touched: break
    if ti is not None:
        lo, hi = ti
        vt.add_contact(dict(vz=(lo[3], hi[3]), th=(lo[4], hi[4]), vx=(lo[2], hi[2]), x=(lo[0], hi[0])))
        vt.finish(True)
    else: vt.finish(False)
    return v.finish(touched), vt

def candidates(X0, mode):
    out = []
    flares = [(0.4, 0.12), (0.6, 0.1)]
    if mode == 'pow':
        for a, b in ZONES:
            if b - a < 50 or b < X0[0] + 150: continue
            for xa in sorted({max(a + 150, X0[0] + 300), a + (b - a) / 2}):
                if not a <= xa <= b: continue
                for f0, f1 in flares:
                    out.append(dict(mode='pow', xa=xa, zg=T.terrain(xa), f0=f0, f1=f1))
    else:
        for vg in (28, 32, 36, 40, 46):
            for f0, f1 in flares: out.append(dict(mode='gl', vg=vg, f0=f0, f1=f1))
    res = []
    for P in out:
        xs, n0 = nominal(X0, P)
        if nominal_ok(xs, n0): res.append((xs[n0][0], P, xs, n0))
    res.sort(key=lambda r: r[0])
    return res

def one_start(args):
    X0, mode, scale, design = args; qf, el_r, thr_r = DESIGNS[design]
    D = D_BOX * scale; cands = candidates(X0, mode)
    if not cands: return None
    nu = 2 if mode == 'pow' else 1; best = None
    for xtd, P, xs, n0 in cands[:3]:
        laws, kg = make_laws(xs, P, nu, el_r, thr_r, qf)
        r = dict(x0=X0[0], xtd=xtd, vz_nom=xs[n0][3])
        for name, law in laws.items():
            r[name], r['ti-' + name] = tube_law(xs, n0, kg, law, nu, D)
        r['first'] = best is None
        if best is None: best = r; best['any'] = {k: not r[k].flags for k in laws}
        else:
            for k in laws: best['any'][k] |= not r[k].flags
    return best

def starts(step=600):
    S = []
    for x in range(600, 6001, step):
        for dh in (25, 60, 120):
            for u in (30, 42, 55):
                for g in (-0.1, 0.05):
                    S.append(np.array([x, T.terrain(x) + dh, u * math.cos(g), u * math.sin(g), g + 0.06, 0, 0.2]))
    return S

LAWS = ['lqr-time', 'lqr-time-flareQ', 'lqr-hag']
HEADROOM = {'elevator rate', 'throttle range', 'elevator rate@flare', 'throttle range@flare'}
FLARE_HR = {'elevator rate@flare', 'throttle range@flare'}

def summarize(rs, label):
    n = len(rs)
    if not n: print(label, 'no nominal-feasible starts'); return
    print(f'{label}: nominal-feasible starts {n}')
    for key, nm in [('ti-lqr-time', 'lqr-time, time-indexed')] + [(k, k + ', contact') for k in LAWS]:
        a = [r['vz_nom'] - r[key].sink for r in rs if r[key].sink < math.inf]
        md, mx = (np.median(a), np.max(a)) if a else (float('nan'),) * 2
        d = {}
        for r in rs:
            for f in r[key].flags: d[f] = d.get(f, 0) + 1
        cert = sum(1 for r in rs if not r[key].flags)
        touch = sum(1 for r in rs if not (r[key].flags - HEADROOM))
        fl = sum(1 for r in rs if not (r[key].flags - (HEADROOM - FLARE_HR)))
        anyc = sum(1 for r in rs if r['any'].get(key, False)) if key in LAWS else -1
        print(f'  {nm:24s} certified {cert:3d}/{n}, touchdown-only {touch:3d}/{n}, +flare headroom {fl:3d}/{n} (best of <=3 escapes: {anyc})  sink spread median {md:5.2f} max {mx:5.2f}  fails {d}')

if __name__ == '__main__':
    from multiprocessing import Pool
    step = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    design = sys.argv[2] if len(sys.argv) > 2 else 'base'
    S = starts(step)
    print('landable zones (x, m):', [(int(a), int(b)) for a, b in ZONES], 'design', design)
    with Pool() as pool:
        for scale in (1.0, 0.25):
            for mode in (sys.argv[3].split(',') if len(sys.argv) > 3 else ('pow', 'gl')):
                rs = [r for r in pool.map(one_start, [(X0, mode, scale, design) for X0 in S], chunksize=1) if r]
                summarize(rs, f'{"powered" if mode == "pow" else "glide"} at {scale}xD, {len(S)} starts')
