"""k-step contraction membership with lateral motion in the slow model (issue #58, route (a)).

Slow coordinates e = (h - h*, s, V - V*, phi, dpsi, v_rt, iphi, ib) - lateral entries relative to the trim; the
fast boxes cover the remaining 25 chart coordinates (pitch, the body rates, the Adams-Bashforth memories, rpm,
manifold pressure, the alpha integrator) around affine quasi-steady values fbar(e). Property and search as in
membership.py: (a) ||e_k - A_k e||_P <= (1 - ||A_k||_P) r, (b) fast states back in their boxes, (c) sink-rate bound
between steps; corners, faces, multi-start Nelder-Mead, fixed-point widening of the fast boxes.

Usage: membership_lat.py K [law]   with law 'gate' (KPSI 1) or 'sched' (proposed: KPSI scaled by max(1, V/35.2)).
Environment: TS_HW (altitude half-width, m), TS_LAT (lateral target scale: roll and heading deg, v_rt m/s).
"""
import sys, os, json, time
import numpy as np
import scipy.linalg as sl
from scipy.optimize import minimize
from tsmap import TsMap, NAMES, NY
from terminal import NEW
from abstract import coords, IV, IVR, IVD, DT, PSI, NORTH, K_HOLD

ZTOP_E = 941.0
HW_H = float(os.environ.get("TS_HW", "15"))
LATS = float(os.environ.get("TS_LAT", "6"))
LAT_NAMES = ["phi", "dpsi", "v_rt", "iphi", "ib"]
LATI = [NAMES.index(n) for n in LAT_NAMES]
FAST = [i for i in range(NY) if i not in (IV, IVD) and i not in LATI]
NS = 3 + len(LATI)


def say(*a):
    print(*a); sys.stdout.flush()


class Loop:
    def __init__(self, law):
        self.m = TsMap()
        g = dict(NEW) if law == "gate" else dict(NEW, kpsiV=35.2)
        self.m.cand(**g)
        self.law = law
        x = np.array(json.load(open("/tmp/ts_level_cert2.json"))["east"]["trim"])
        self.hs, self.ys = x[0], x[1:]
        rows = self.m.sim(self.hs, self.ys, 128 * 120, 128 * 120, PSI, NORTH)   # re-settle under this law
        self.hs, self.ys = rows[-1][3], rows[-1][4:].copy()
        self.Vs = float(np.sqrt(self.ys[IV] ** 2 + self.ys[IVR] ** 2 + self.ys[IVD] ** 2))
        self.n = 0

    def e_of(self, row):
        y = row[4:]
        return np.concatenate([coords(row[3], y, self.hs, self.Vs), y[LATI] - self.ys[LATI]])

    def state(self, e, fast):
        y = self.ys.copy()
        y[FAST] = fast
        y[LATI] = self.ys[LATI] + e[3:]
        vz = e[1] - self.Vs * K_HOLD * e[0]
        V = self.Vs + e[2]
        y[IVD] = -vz
        y[IV] = np.sqrt(max(V ** 2 - vz ** 2 - y[IVR] ** 2, 1.0))
        return self.hs + e[0], y

    def roll(self, e, fast, n, every=1):
        h0, y0 = self.state(e, fast)
        self.n += 1
        return self.m.sim(h0, y0, n, every, PSI, NORTH)


def data(L, rng, n_runs=40, secs=40):
    runs = []
    for _ in range(n_runs):
        e0 = np.concatenate([[rng.uniform(-20, 20), rng.uniform(-3, 3), rng.uniform(-6, 6)],
                             [np.radians(rng.uniform(-4, 4)), np.radians(rng.uniform(-4, 4)), rng.uniform(-1.5, 1.5),
                              rng.uniform(-0.02, 0.02), rng.uniform(-0.02, 0.02)]])
        runs.append(L.roll(e0, L.ys[FAST], 128 * secs, 8))
    return runs


def setup(L, runs, k, margin=1.5):
    E = np.array([L.e_of(rw) for rows in runs for rw in rows[48:]])
    F = np.array([rw[4:][FAST] for rows in runs for rw in rows[48:]])
    X = np.column_stack([np.ones(len(E)), E])
    coef, *_ = np.linalg.lstsq(X, F, rcond=None)
    fstar, M = coef[0], coef[1:].T
    b = margin * np.abs(F - X @ coef).max(axis=0) + 1e-9 * (1 + np.abs(fstar))
    step = k // 8
    Ein, Eout = [], []
    for rows in runs:
        es = np.array([L.e_of(rw) for rw in rows[48:]])
        Ein += list(es[:-step]); Eout += list(es[step:])
    Ein, Eout = np.array(Ein), np.array(Eout)
    Ak = np.linalg.lstsq(Ein, Eout, rcond=None)[0].T
    scale = np.array([20.0, 2.0, 8.0, np.radians(LATS), np.radians(LATS), LATS / 2, 0.02, 0.02])
    D = np.diag(1 / scale)
    Az = D @ Ak @ np.linalg.inv(D)
    rho = max(abs(np.linalg.eigvals(Ak)))
    mu = np.sqrt(rho) + 0.5 * (1 - np.sqrt(rho))
    P = D @ sl.solve_discrete_lyapunov((Az / mu).T, np.eye(NS)) @ D
    Lc = np.linalg.cholesky(P)
    ck = float(np.linalg.norm(Lc.T @ Ak @ np.linalg.inv(Lc.T), 2))
    Pi = np.linalg.inv(P)
    r = HW_H / np.sqrt(Pi[0, 0])
    vbar = (L.hs - HW_H - ZTOP_E) / (k * DT)
    sres = max(np.sqrt((o - Ak @ i) @ P @ (o - Ak @ i)) for i, o in zip(Ein, Eout))
    return dict(k=k, fstar=fstar, M=M, b=b, Ak=Ak, P=P, Lc=Lc, ck=ck, r=r, vbar=vbar, allow=(1 - ck) * r,
                half=r * np.sqrt(np.diag(Pi)), settled_ratio=sres / ((1 - ck) * r), rho=rho)


def violations(L, th, z):
    u = z[:NS]; nu = np.linalg.norm(u)
    if nu > 1: u = u / nu
    v = np.clip(z[NS:], -1, 1)
    e = th["r"] * np.linalg.solve(th["Lc"].T, u)
    fast = th["fstar"] + th["M"] @ e + v * th["b"]
    rows = L.roll(e, fast, th["k"], 1)
    ek = L.e_of(rows[-1])
    d = ek - th["Ak"] @ e
    va = float(np.sqrt(d @ th["P"] @ d)) / th["allow"]
    ratio = np.abs(rows[-1][4:][FAST] - (th["fstar"] + th["M"] @ ek)) / th["b"]
    th["exit"] = np.maximum(th["exit"], ratio)
    vc = max(max(float(rw[4 + IVD]) for rw in rows), 0.0) / th["vbar"]
    return np.array([va, float(ratio.max()), vc])


def search(L, th, rng, n_screen=120, n_nm=3, maxfev=300):
    nf = len(FAST)
    cands = []
    for k in range(n_screen):
        if k < 32:
            u = rng.choice([-1.0, 1.0], size=NS) / np.sqrt(NS); v = rng.choice([-1.0, 1.0], size=nf)
        elif k < 56:
            u = np.zeros(NS); u[k % NS] = rng.choice([-1, 1]); v = rng.choice([-1.0, 1.0], size=nf)
        else:
            u = rng.normal(size=NS); u /= np.linalg.norm(u); u *= rng.uniform(0.5, 1) ** (1 / NS)
            v = rng.uniform(-1, 1, size=nf)
        z = np.concatenate([u, v])
        cands.append((z, violations(L, th, z)))
    worst = np.max([c[1] for c in cands], axis=0)
    for obj in range(3):
        for z0, _ in sorted(cands, key=lambda c: -c[1][obj])[:n_nm]:
            res = minimize(lambda z: -violations(L, th, z)[obj], z0, method="Nelder-Mead",
                           options=dict(maxfev=maxfev, xatol=1e-3, fatol=1e-4))
            worst[obj] = max(worst[obj], -res.fun)
    return worst


def physical(th):
    h = th["half"]
    return (f"h {h[0]:.1f} m, s {h[1]:.2f} m/s, V {h[2]:.2f} m/s, roll {np.degrees(h[3]):.2f} deg, heading "
            f"{np.degrees(h[4]):.2f} deg, v_rt {h[5]:.2f} m/s, iphi {h[6]:.3f}, ib {h[7]:.3f}")


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 768
    law = sys.argv[2] if len(sys.argv) > 2 else "sched"
    rounds = int(os.environ.get("TS_ROUNDS", "4"))
    L = Loop(law)
    runs = data(L, np.random.default_rng(58))
    th = setup(L, runs, k)
    say(f"[{law} k {k} hw {HW_H:g} lat {LATS:g}] rho(A_k) {th['rho']:.4f}, c_k {th['ck']:.4f}; half-widths {physical(th)};"
        f" vbar {th['vbar']:.1f} m/s; settled residual / allowance {th['settled_ratio']:.3f}")
    rng = np.random.default_rng(7)
    res = []
    for rnd in range(rounds + 1):
        th["exit"] = np.zeros(len(FAST))
        t0 = time.time()
        w = search(L, th, np.random.default_rng(100 + rnd) if rnd == rounds else rng,
                   **(dict(n_screen=300, n_nm=4, maxfev=600) if rnd == rounds else {}))
        tag = "re-search" if rnd == rounds else f"round {rnd}"
        say(f"  {tag}: worst (a) {w[0]:.3f}, (b) {w[1]:.3f}, (c) {w[2]:.3f}; largest exits "
            + ", ".join(f"{NAMES[FAST[i]]} {th['exit'][i]:.2f}" for i in np.argsort(-th['exit'])[:4])
            + f"  [{L.n} rollouts, {time.time() - t0:.0f} s]")
        res.append(dict(tag=tag, worst=w.tolist()))
        if rnd < rounds:
            th["b"] = th["b"] * np.maximum(1.0, 1.1 * th["exit"])
    fb = {NAMES[i]: float(bb) for i, bb in zip(FAST, th["b"])}
    say("  fast boxes: " + ", ".join(f"{n} {fb[n]:.3g}" for n in ("theta", "p_i", "q_i", "r_i", "rpm", "ia")))
    json.dump(dict(law=law, k=k, hw=HW_H, lat=LATS, ck=th["ck"], half=th["half"].tolist(), vbar=th["vbar"],
                   rounds=res, fast_box=fb), open(f"/tmp/ts_memlat_{law}_{k}_{HW_H:g}_{LATS:g}.json", "w"), indent=1)
