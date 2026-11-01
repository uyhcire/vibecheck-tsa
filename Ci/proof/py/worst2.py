"""Adversarial search against the Lean T v3: hill-climb (V'/r^2, fast'/tol), exits score +10."""
import numpy as np, sys, kinv
from kinv import *
R = 6.0; SAFE = 1.1
rng2 = np.random.default_rng(int(sys.argv[1]))
HLO, HHI = float(sys.argv[2]), float(sys.argv[3])
def fc(x):
    h, y, e = coords(x); e = e.copy(); e[10] = 0; k = kat(h); lam = e @ k; perp = e - lam * k
    return lam, perp
def build(h, y, lam, perp):
    c = center(h); k = kat(h); g = Gat(h) @ y + lam * k + perp
    x = c.copy(); x[0] = 0; x[1] = int(h * 65536); x[11] = 0
    x[yidx] = np.round(c[yidx] + y * Sy); x[gidx] = np.round(c[gidx] + g * Sg); x[20] = int(c[20])
    return x.astype(np.int64)
def proj(h, y, lam, perp):
    v = V(h, y)
    if v > (R * 0.999) ** 2: y = y * R * 0.999 / np.sqrt(v)
    t = tkat(h) * SAFE * 0.999; lam = np.clip(lam, -t, t)
    tp = tpat(h) * SAFE * 0.999; perp = np.clip(perp, -tp, tp); perp[10] = 0
    return h, y, lam, perp
def score(params):
    X = np.array([build(*p) for p in params])
    img, safe, cl, t0, t1 = ticks_T(X)
    out = []
    for xi, a, b, sf, c in zip(img, t0, t1, safe, cl):
        if not a: out.append(-1.0); continue
        h1, y1, _ = coords(xi); lam, perp = fc(xi)
        f = max(abs(lam) / (tkat(h1) * SAFE), np.max(np.abs(perp[:10]) / (tpat(h1)[:10] * SAFE)))
        out.append(max(V(h1, y1) / R**2, f) + (10 if (not b or not sf or not c) else 0))
    return np.array(out)
params = []
for _ in range(3000):
    h = rng2.uniform(HLO, HHI); u = rng2.normal(size=7); y = u / np.sqrt(u @ Pat(h) @ u) * R
    lam = tkat(h) * SAFE * rng2.choice([-1, 1]); perp = tpat(h) * SAFE * rng2.choice([-1, 1], size=11)
    params.append(proj(h, y, lam, perp))
s = score(params); o = np.argsort(-s)[:60]; pop = [params[i] for i in o]; ps = s[o]
print("init", ps[:3].round(4))
for it in range(15):
    cand = []
    for (h, y, lam, perp) in pop:
        for _ in range(5):
            h2 = float(np.clip(h + rng2.normal() * 3, 10, 2635))
            cand.append(proj(h2, y + rng2.normal(size=7) * 0.2, lam + rng2.normal() * 0.1 * tkat(h2), perp + rng2.normal(size=11) * 0.1 * tpat(h2)))
    cs = score(cand)
    allp = pop + cand; alls = np.concatenate([ps, cs]); o = np.argsort(-alls)[:60]
    pop = [allp[i] for i in o]; ps = alls[o]
    print(f"iter {it}: best {ps[:3].round(4)} at h {[round(p[0]) for p in pop[:3]]}", flush=True)
