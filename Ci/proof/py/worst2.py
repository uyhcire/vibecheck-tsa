"""Adversarial search against the Lean T v3: hill-climb (V'/r^2, fast'/tol), exits score +10."""
import numpy as np, sys, kinv
from kinv import *
import os; R = float(os.environ.get("RR", "6.0")); SAFE = float(os.environ.get("SAFE", "1.25"))
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
    if v > (rat(h) * 0.999) ** 2: y = y * rat(h) * 0.999 / np.sqrt(v)
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
        out.append(max(V(h1, y1) / rat(h1)**2, f) + (10 if (not b or not sf or not c) else 0))
    return np.array(out)
params = []
for _ in range(3000):
    h = rng2.uniform(HLO, HHI); u = rng2.normal(size=7); y = u / np.sqrt(u @ Pat(h) @ u) * rat(h)
    lam = tkat(h) * SAFE * rng2.choice([-1, 1]); perp = tpat(h) * SAFE * rng2.choice([-1, 1], size=11)
    params.append(proj(h, y, lam, perp))
s = score(params); o = np.argsort(-s)[:60]; pop = [params[i] for i in o]; ps = s[o]
print("init", ps[:3].round(4))
for it in range(15):
    cand = []
    for (h, y, lam, perp) in pop:
        for _ in range(5):
            h2 = float(np.clip(h + rng2.normal() * 3, 10, 2689.9))
            cand.append(proj(h2, y + rng2.normal(size=7) * 0.2, lam + rng2.normal() * 0.1 * tkat(h2), perp + rng2.normal(size=11) * 0.1 * tpat(h2)))
    cs = score(cand)
    allp = pop + cand; alls = np.concatenate([ps, cs]); o = np.argsort(-alls)[:60]
    pop = [allp[i] for i in o]; ps = alls[o]
    print(f"iter {it}: best {ps[:3].round(4)} at h {[round(p[0]) for p in pop[:3]]}", flush=True)
X = np.array([build(*p) for p in pop[:4]])
img, safe, cl, t0, t1 = ticks_T(X)
for p, x, xi, a, b in zip(pop[:4], X, img, t0, t1):
    h0, y0, _ = coords(x); h1, y1, _ = coords(xi); l0, p0 = fc(x); l1, p1 = fc(xi)
    print(f"h {h0:.1f}->{h1:.2f} V/r2 {V(h0,y0)/rat(h0)**2:.4f}->{V(h1,y1)/rat(h1)**2:.4f} lam/tk {l0/(tkat(h0)*SAFE):+.3f}->{l1/(tkat(h1)*SAFE):+.3f} perp {np.max(np.abs(p0[:10])/(tpat(h0)[:10]*SAFE)):.3f}->{np.max(np.abs(p1[:10])/(tpat(h1)[:10]*SAFE)):.3f} inT {a}->{b}")
print("--- sensitivity at the worst point")
h, y, lam, perp = pop[0]
names = [ZN[i] for i in GI]
def vnext(h, y, lam, perp):
    X = np.array([build(h, y, lam, perp)]); img, *_ = ticks_T(X); h1, y1, _ = coords(img[0]); return V(h1, y1) / rat(h1)**2
print("as is", round(vnext(h, y, lam, perp), 4), " no fast", round(vnext(h, y, 0.0, perp * 0), 4), " no lam", round(vnext(h, y, 0.0, perp), 4))
for k in range(10):
    p2 = perp.copy(); p2[k] = 0; print(names[k], round(vnext(h, y, lam, p2), 4), end="; ")
print()
