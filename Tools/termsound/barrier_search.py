"""Adversarial search for violations of the energy-barrier conditions C1-C3 (barrier.py) on the real loop."""
import copy
import json
import sys
import threading
import time
import numpy as np
from scipy.optimize import minimize, differential_evolution
from barrier import (THETA0, NDIM, decode, Pool, margins, c4_margin, B, excursion, say, FLOOR)

# objective per condition: (decode band, value to minimise from a margins dict)
OBJ = {
    "c1": (True, lambda mg: mg["c1"]),
    "drop": (False, lambda mg: -mg["drop"]),
    "c2": (False, lambda mg: mg["c2"]),
    "c3": (False, lambda mg: mg["c3"]),
    "U": (False, lambda mg: 1 - mg["ex"]["U"]),
}


class Search:
    def __init__(self, pool, th):
        self.pool, self.th, self.nev, self.exmax = pool, th, 0, {}

    def batch(self, U, cond):
        band, val = OBJ[cond]
        states = [decode(self.th, u, self.th["Delta"] if band else None) for u in U]
        rolls = self.pool.roll(states, self.th["k"])
        self.nev += len(U)
        out = []
        for s, r in zip(states, rolls):
            if s is None:
                out.append((np.inf, None)); continue
            m = margins(self.th, s, r)
            for kk, v in m["ex"].items():
                self.exmax[kk] = max(self.exmax.get(kk, 0.0), v)
            out.append((val(m), m))
        return out

    def run(self, cond, n_rand=256, n_vert=256, de_iter=12, n_nm=4, nm_fev=250, seed=0):
        rng = np.random.default_rng(seed)
        U = np.concatenate([rng.uniform(size=(n_rand, NDIM)), rng.integers(0, 2, size=(n_vert, NDIM)).astype(float)])
        res = self.batch(U, cond)
        best = sorted(zip([r[0] for r in res], range(len(U))))[:n_nm]
        starts = [U[i] for _, i in best]
        # differential evolution, population evaluated in one batch per generation
        if de_iter:
            init = np.concatenate([np.array(starts), rng.uniform(size=(8 * NDIM - len(starts), NDIM))])
            de = differential_evolution(lambda X: np.array([r[0] for r in self.batch(X.T, cond)]),
                                        [(0, 1)] * NDIM, maxiter=de_iter, init=init, polish=False,
                                        vectorized=True, updating="deferred", seed=seed, tol=0)
            starts = [de.x] + starts[:n_nm - 1]
        # Nelder-Mead polish from each start, one tsmap process per start
        found = []

        def nm(u0, m):
            sub = Pool.__new__(Pool); sub.ms = [m]
            s = Search(sub, self.th)
            r = minimize(lambda u: s.batch([u], cond)[0][0], u0, method="Nelder-Mead", bounds=[(0, 1)] * NDIM,
                         options=dict(maxfev=nm_fev, xatol=1e-4, fatol=1e-6, adaptive=True))
            found.append((r.fun, np.clip(r.x, 0, 1))); self.nev += s.nev
            for kk, v in s.exmax.items():
                self.exmax[kk] = max(self.exmax.get(kk, 0.0), v)
        ts = [threading.Thread(target=nm, args=(u0, m)) for u0, m in zip(starts, self.pool.ms)]
        [t.start() for t in ts]; [t.join() for t in ts]
        cand = found + [(r[0], U[i]) for r, i in zip([res[i] for _, i in best], [i for _, i in best])]
        f, u = min(cand, key=lambda t: t[0])
        return f, u, self.batch([u], cond)[0][1]


def run_theta(pool, th, conds=("c1", "drop", "c2", "c3"), **kw):
    out = {}
    for c in conds:
        t = time.time()
        s = Search(pool, th)
        f, u, mg = s.run(c, **kw)
        out[c] = dict(value=float(f) if c != "drop" else float(-f), u=u.tolist(),
                      which=mg["c2_which"] if mg else None, evals=s.nev, secs=time.time() - t)
    out["c4"] = dict(value=c4_margin(th))
    return out


if __name__ == "__main__":
    pool = Pool(4)
    th = copy.deepcopy(THETA0)
    t = time.time()
    r = pool.roll([decode(th, np.full(NDIM, 0.5))] * 64, th["k"])
    say(f"64 rolls of k={th['k']}: {time.time() - t:.2f} s")
    r = run_theta(pool, th, de_iter=4, n_nm=4, nm_fev=150)
    say({c: {k: v for k, v in d.items() if k != "u"} for c, d in r.items()})
    pool.close()


def describe(pool, th, u, band=None):
    """Start and end of the k-frame roll from decode(u): slow values, B, U and the largest excursions."""
    from barrier import speed_vz, dalpha, U as Uf
    s = decode(th, np.asarray(u), band)
    r = pool.roll([s], th["k"])[0]
    lines = []
    for tag, (h, y) in (("start", s), ("end", (r[0], r[1]))):
        V, vz = speed_vz(y)
        ex = excursion(th, h, y)
        top = sorted(ex.items(), key=lambda kv: -kv[1])[:5]
        lines.append(f"{tag}: h {h:.2f} V {V:.2f} vz {vz:.2f} dAlpha {dalpha(y):+.4f} B {B(th, h, y):.2f} "
                     f"U {Uf(th, h, y):.2f}; top excursions " + ", ".join(f"{k} {v:.2f}" for k, v in top))
    lines.append(f"min h over frames 1..k: {r[2]:.2f} (floor {FLOOR})")
    return "\n".join(lines)
