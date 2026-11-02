"""Membership of the level-off closed loop in the k-step contraction family (issue #58).

theta = (k, coordinates e = (h - h*, s, V - V*), A_k, ellipsoid P and r, the residual allowance, fast-state boxes
around quasi-steady values fbar(e) = f* + M e, a climb-rate bound between steps). The start set is
X0 = {e : e^T P e <= r^2} x {fast : |fast - fbar(e)| <= b}, everything explicit.

P[theta](f): for every x in X0, after k frames
  (a) the residual d = e_k - A_k e has ||d||_P <= (1 - ||A_k||_P) r   (rung 1's q_robust_step budget),
  (b) the fast states are back in their boxes around fbar(e_k),
  (c) every intermediate frame has sink rate at most vbar, with h* - hw_h - vbar k dt >= zTop + e.
The search is adversarial: corners and faces of X0, then multi-start Nelder-Mead on each violation measure.
"""
import sys, json, time
import numpy as np
import scipy.linalg as sl
from scipy.optimize import minimize
from tsmap import TsMap, NAMES, NY
from terminal import NEW
from abstract import coords, IV, IVR, IVD, DT, PSI, NORTH, K_HOLD

ZTOP_E = 941.0                       # zTop (934 m) plus the 7 m airframe cube
HW_H = float(__import__("os").environ.get("TS_HW", "20"))   # altitude half-width of the ellipsoid
FAST = [i for i in range(NY) if i not in (IV, IVD)]


def say(*a):
    print(*a); sys.stdout.flush()


class Loop:
    def __init__(self):
        self.m = TsMap(); self.m.cand(**NEW)
        x = np.array(json.load(open("/tmp/ts_level_cert2.json"))["east"]["trim"])
        self.hs, self.ys = x[0], x[1:]
        self.Vs = float(np.sqrt(self.ys[IV] ** 2 + self.ys[IVR] ** 2 + self.ys[IVD] ** 2))
        self.n = 0

    def state(self, e, fast):
        """Chart state with slow coordinates e and fast coordinates `fast` (values, in FAST order)."""
        y = self.ys.copy()
        y[FAST] = fast
        vz = e[1] - self.Vs * K_HOLD * e[0]
        V = self.Vs + e[2]
        y[IVD] = -vz
        y[IV] = np.sqrt(max(V ** 2 - vz ** 2 - y[IVR] ** 2, 1.0))
        return self.hs + e[0], y

    def roll(self, e, fast, n, every=1):
        h0, y0 = self.state(e, fast)
        self.n += 1
        return self.m.sim(h0, y0, n, every, PSI, NORTH)

    def e_of(self, row):
        return coords(row[3], row[4:], self.hs, self.Vs)


def settled_data(L, rng, n_runs=40, secs=40):
    """Slow and fast coordinates along rollouts started near the trim with offsets, from 3 s on (every 8 frames)."""
    E, F = [], []
    for k in range(n_runs):
        e0 = np.array([rng.uniform(-25, 25), rng.uniform(-4, 4), rng.uniform(-6, 6)])
        f0 = L.ys[FAST] + rng.normal(size=len(FAST)) * 0.0
        rows = L.roll(e0, f0, 128 * secs, 8)
        for rw in rows[48:]:
            E.append(L.e_of(rw)); F.append(rw[4:][FAST])
    return np.array(E), np.array(F), rows


def setup_theta(L, E, F, runs, k, margin=1.5):
    # quasi-steady fast values fbar(e) = f* + M e (least squares on settled data)
    X = np.column_stack([np.ones(len(E)), E])
    coef, *_ = np.linalg.lstsq(X, F, rcond=None)
    fstar, M = coef[0], coef[1:].T
    resid = np.abs(F - X @ coef)
    b = margin * resid.max(axis=0) + 1e-9 * (1 + np.abs(fstar))
    # A_k from settled pairs (e_t, e_{t+k})
    step = k // 8
    Ein, Eout = [], []
    for rows in runs:
        es = np.array([L.e_of(rw) for rw in rows[48:]])
        for t in range(len(es) - step):
            Ein.append(es[t]); Eout.append(es[t + step])
    Ein, Eout = np.array(Ein), np.array(Eout)
    Ak = np.linalg.lstsq(Ein, Eout, rcond=None)[0].T
    D = np.diag([1 / 20.0, 1 / 2.0, 1 / 8.0])
    Az = D @ Ak @ np.linalg.inv(D)
    mu = max(abs(np.linalg.eigvals(Ak))) ** 0.5 + 0.5 * (1 - max(abs(np.linalg.eigvals(Ak))) ** 0.5)
    P = D @ sl.solve_discrete_lyapunov((Az / mu).T, np.eye(3)) @ D
    Lc = np.linalg.cholesky(P)
    ck = float(np.linalg.norm(Lc.T @ Ak @ np.linalg.inv(Lc.T), 2))
    Pi = np.linalg.inv(P)
    r = HW_H / np.sqrt(Pi[0, 0])
    vbar = (L.hs - HW_H - ZTOP_E) / (k * DT)
    settled_res = np.array([np.sqrt((o - Ak @ i) @ P @ (o - Ak @ i)) for i, o in zip(Ein, Eout)]).max()
    return dict(k=k, fstar=fstar, M=M, b=b, Ak=Ak, P=P, Lc=Lc, ck=ck, r=r, vbar=vbar, allow=(1 - ck) * r,
                half=r * np.sqrt(np.diag(Pi)), settled_ratio=settled_res / ((1 - ck) * r))


def violations(L, th, z, detail=False):
    """z = (u (3, in the unit ball after radial projection), v (len FAST, in [-1, 1])) -> (a, b, c) ratios."""
    u = z[:3]; nu = np.linalg.norm(u)
    if nu > 1: u = u / nu
    v = np.clip(z[3:], -1, 1)
    e = th["r"] * np.linalg.solve(th["Lc"].T, u)
    fast = th["fstar"] + th["M"] @ e + v * th["b"]
    rows = L.roll(e, fast, th["k"], 1)
    ek = L.e_of(rows[-1])
    d = ek - th["Ak"] @ e
    va = float(np.sqrt(d @ th["P"] @ d)) / th["allow"]
    fk = rows[-1][4:][FAST]
    ratio = np.abs(fk - (th["fstar"] + th["M"] @ ek)) / th["b"]
    th["exit"] = np.maximum(th.get("exit", np.zeros(len(FAST))), ratio)
    vb = float(np.max(ratio))
    sink = max(float(rw[4 + IVD]) for rw in rows)            # v_down, m/s
    vc = max(sink, 0.0) / th["vbar"]
    out = np.array([va, vb, vc])
    for i in range(3):
        if out[i] > th.setdefault("wz", [(0, None)] * 3)[i][0]:
            th["wz"][i] = (out[i], z.copy())
    if detail:
        return out, e, d, fast - (th["fstar"] + th["M"] @ e)
    return out


def search(L, th, rng, n_screen=120, n_nm=3, maxfev=300):
    nf = len(FAST)
    cands = []
    for k in range(n_screen):
        if k < 16:                                           # slow corners on the ellipsoid, fast corners
            u = np.array([(1 if k & 1 else -1), (1 if k & 2 else -1), (1 if k & 4 else -1)]) / np.sqrt(3)
            v = rng.choice([-1.0, 1.0], size=nf)
        elif k < 40:                                          # faces: one slow axis at +-1
            u = np.zeros(3); u[k % 3] = rng.choice([-1, 1]); v = rng.choice([-1.0, 1.0], size=nf)
        else:
            u = rng.normal(size=3); u /= np.linalg.norm(u); u *= rng.uniform(0.5, 1) ** (1 / 3)
            v = rng.uniform(-1, 1, size=nf)
        z = np.concatenate([u, v])
        cands.append((z, violations(L, th, z)))
    worst = np.max([c[1] for c in cands], axis=0)
    for obj in range(3):
        starts = sorted(cands, key=lambda c: -c[1][obj])[:n_nm]
        for z0, _ in starts:
            f = lambda z: -violations(L, th, z)[obj]
            res = minimize(f, z0, method="Nelder-Mead", options=dict(maxfev=maxfev, initial_simplex=None, xatol=1e-3, fatol=1e-4))
            worst[obj] = max(worst[obj], -res.fun)
    return worst


if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [512]                # default: the surviving theta (k 512, TS_HW 20)
    rng = np.random.default_rng(58)
    L = Loop()
    t0 = time.time()
    E, F, _ = settled_data(L, rng)
    runs = []
    rng2 = np.random.default_rng(5)
    for k in range(20):
        e0 = np.array([rng2.uniform(-25, 25), rng2.uniform(-4, 4), rng2.uniform(-6, 6)])
        runs.append(L.roll(e0, L.ys[FAST], 128 * 40, 8))
    say(f"settled data: {len(E)} samples ({time.time() - t0:.0f} s)")
    out = {}
    rounds = int(__import__('os').environ.get('TS_ROUNDS', '4'))
    for k in ks:
      th = setup_theta(L, E, F, runs, k)
      for rnd in range(rounds):
        th["exit"] = np.zeros(len(FAST))
        say(f"k {k} round {rnd}: c_k {th['ck']:.4f}, r {th['r']:.3f}, half-widths h {th['half'][0]:.1f} m, s {th['half'][1]:.2f} m/s,"
            f" V {th['half'][2]:.2f} m/s; vbar {th['vbar']:.1f} m/s; settled-data residual / allowance {th['settled_ratio']:.3f}")
        say("   fast boxes (half-widths): " + ", ".join(f"{NAMES[i]} {bb:.3g}" for i, bb in zip(FAST, th["b"])
                                                       if NAMES[i] in ("phi", "theta", "q_i", "rpm", "ia", "ib", "iphi", "map")))
        t1 = time.time()
        w = search(L, th, rng)
        say(f"   worst violation found: (a) residual/allowance {w[0]:.3f}, (b) fast-box exit {w[1]:.3f}, (c) sink/vbar {w[2]:.3f}"
            f"  [{L.n} rollouts so far, {time.time() - t1:.0f} s]")
        wa, wzz = th["wz"][0]
        if wzz is not None:
            o, e_, d_, _ = violations(L, th, wzz, detail=True)
            z0 = wzz.copy(); z0[3:] = 0
            o0 = violations(L, th, z0)
            Lc = th["Lc"]
            say(f"   worst (a) at e = ({e_[0]:.1f} m, {e_[1]:.2f} m/s, {e_[2]:.2f} m/s): d = ({d_[0]:.3f} m, {d_[1]:.3f} m/s, "
                f"{d_[2]:.3f} m/s); same slow state with fast states at fbar: (a) {o0[0]:.3f}")
        th["wz"] = [(0, None)] * 3
        top = np.argsort(-th["exit"])[:5]
        say("   largest box exits: " + ", ".join(f"{NAMES[FAST[i]]} {th['exit'][i]:.1f}" for i in top))
        out[f"{k} round {rnd}"] = dict(ck=th["ck"], r=th["r"], half=th["half"].tolist(), vbar=th["vbar"],
                      settled_ratio=th["settled_ratio"], worst=w.tolist(),
                      fast_box={NAMES[i]: float(bb) for i, bb in zip(FAST, th["b"])})
        json.dump(out, open(f"/tmp/ts_membership_{'_'.join(map(str, ks))}_{HW_H:g}.json", "w"), indent=1)
        # theta update: widen each fast box to the largest exit found (fixed-point iteration for invariant boxes)
        th["b"] = th["b"] * np.maximum(1.0, 1.1 * th["exit"])
