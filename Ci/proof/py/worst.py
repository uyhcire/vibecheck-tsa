"""Adversarial search for one-tick exits from the Lean T: hill-climb V'/r^2 and fast'/tol from the worst samples."""
import numpy as np, sys, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy"); tolN = np.load("tolN.npy")
def tolat(h): return sm.interpN(tolN, h)
R = 6.0
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
def score(X):
    img, safe, cl, t0, t1 = ticks_T(X)
    s = []
    for x, xi, a, b, sf, c in zip(X, img, t0, t1, safe, cl):
        if not a: s.append(-1.0); continue
        h1, y1, e1 = coords(xi)
        s.append(max(V(h1, y1)/(R*R), np.max(np.abs(e1)/tolat(h1))) + (10 if (not b or not sf or not c) else 0))
    return np.array(s)
def project(x):
    """scale a candidate back into T: shrink y to the ellipse and fast coords to the tolerance band"""
    h, y, e = coords(x); c = center(h)
    v = V(h, y)
    if v > (R*0.999)**2: y = y * (R*0.999) / np.sqrt(v)
    t = tolat(h) * 0.999; e = np.clip(e, -t, t)
    g = Gat(h) @ y + e
    x = x.copy(); x[yidx] = np.round(c[yidx] + y*Sy); x[gidx] = np.round(c[gidx] + g*Sg)
    return x
HLO = float(sys.argv[2]) if len(sys.argv) > 2 else 10; HHI = float(sys.argv[3]) if len(sys.argv) > 3 else 2635
X = sm.sample(3000, R*0.999, None, hlo=HLO, hhi=HHI, tolfun=lambda h: tolat(h)*0.999)
X = np.array([project(x) for x in X]); s = score(X)
print("initial best", np.sort(s)[-5:].round(4))
pop = X[np.argsort(-s)[:60]]; ps = np.sort(s)[::-1][:60]
for it in range(12):
    cand = []
    for x in pop:
        for _ in range(5):
            h, y, e = coords(x)
            y2 = y + rng.normal(size=7) * 0.3; e2 = e + rng.normal(size=len(GI)) * 0.1 * tolat(h)
            h2 = np.clip(h + rng.normal() * 5, 10, 2635)
            c = center(h2); g = Gat(h2) @ y2 + e2
            z = x.copy(); z[1] = int(h2*65536); z[yidx] = np.round(c[yidx] + y2*Sy); z[gidx] = np.round(c[gidx] + g*Sg)
            cand.append(project(z))
    cand = np.array(cand); cs = score(cand)
    allx = np.concatenate([pop, cand]); alls = np.concatenate([ps, cs])
    o = np.argsort(-alls)[:60]; pop = allx[o]; ps = alls[o]
    print(f"iter {it}: best {ps[:3].round(4)} at h {[round(p[1]/65536) for p in pop[:3]]}", flush=True)
img, safe, cl, t0, t1 = ticks_T(pop[:5])
for x, xi, a, b in zip(pop[:5], img, t0, t1):
    h0, y0, e0 = coords(x); h1, y1, e1 = coords(xi)
    print(f"h {h0:.1f}->{h1:.2f} V {V(h0,y0)/R/R:.4f}->{V(h1,y1)/R/R:.4f} inT {a}->{b} fast0/tol {np.round(np.abs(e0)/tolat(h0),3)} fast1/tol {np.round(np.abs(e1)/tolat(h1),3)}")
np.save("worst_pop.npy", pop)
