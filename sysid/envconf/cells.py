"""Shared parameters per commit cell (V0, gam0) over all commit variants (throttle, alpha and q offsets), for
forms B (commit-referenced vz schedule) and C (commit-referenced flight-path schedule); bound vs actual loss."""
import math
import sys
import pandas as pd
from forms import DT, G, loss_from_vz, sched_c

d = pd.read_csv(sys.argv[1])
meta = d[d.k == 0][['tag', 'V', 'gam', 'al', 'q', 'rpm', 'h']].rename(columns={'V': 'V0', 'gam': 'g0', 'h': 'h0'})
meta['cV'] = meta.V0.round(0)
meta['cg'] = meta.g0.round(2)
runs = {t: r for t, r in d.groupby('tag')}


def b_params(rs, K):
    D = max(max(0.0, r.vz.values[0] - r.vz.values[1:K + 2].min()) for r in rs)
    a = 60.0
    for r in rs:
        vz = r.vz.values
        s0 = vz[0] - D
        for k in range(K + 1, len(vz)):
            if vz[k] < 0:
                a = min(a, (vz[k] - s0) / ((k - K) * DT))
    return D, a


def b_loss(vz0, K, D, a):
    if a <= 0:
        return math.inf
    sig = [vz0] + [vz0 - D] * K
    while sig[-1] < 0:
        sig.append(sig[-1] + a * DT)
    sig.append(sig[-1])
    return loss_from_vz(sig)


def c_params(rs, K):
    dg = max(max(0.0, r.gam.values[0] - r.gam.values[1:K + 2].min()) for r in rs)
    Vhi = 0.0
    for r in rs:
        g = r.gam.values
        idx = next((i for i in range(1, len(g)) if g[i] >= 0), len(g) - 1)
        Vhi = max(Vhi, r.V.values[:idx + 1].max())
    lo, hi = 0.5, 6.0
    for _ in range(30):
        mid = (lo + hi) / 2
        ok = True
        for r in rs:
            g = r.gam.values
            sc = sched_c(g[0] - dg, K, mid, Vhi)
            if any(g[k] < min(0.0, sc[min(k, len(sc) - 1)]) - 1e-9 for k in range(1, len(g))):
                ok = False
                break
        lo, hi = (mid, hi) if ok else (lo, mid)
    return dg, lo, Vhi


def c_loss(V0, g0, K, dg, nmin, Vhi):
    if nmin <= 1:
        return math.inf
    sc = sched_c(g0 - dg, K, nmin, Vhi)
    return loss_from_vz([V0 * math.sin(g0)] + [Vhi * math.sin(x) for x in sc[1:]] + [0.0])


rows = []
for (cV, cg), m in meta.groupby(['cV', 'cg']):
    rs = [runs[t] for t in m.tag]
    actual = max(r.h.values[0] - r.hmin.values[1:].min() for r in rs)
    V0, g0 = m.V0.iloc[0], m.g0.iloc[0]
    vz0 = V0 * math.sin(g0)
    bestB = min(((b_loss(vz0, K, *b_params(rs, K)), K) for K in (4, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128)), key=lambda x: x[0])
    bestC = min(((c_loss(V0, g0, K, *c_params(rs, K)), K) for K in (4, 6, 8, 10, 12, 16, 24, 32, 48, 64, 96, 128)), key=lambda x: x[0])
    pC = c_params(rs, bestC[1])
    pB = b_params(rs, bestB[1])
    rows.append(dict(V0=cV, g0=cg, actual=actual, HB=bestB[0], KB=bestB[1], D=pB[0], a=pB[1], HC=bestC[0],
                     KC=bestC[1], dg=pC[0], nmin=pC[1], Vhi=pC[2],
                     Vmin=min(r.Vmin.min() for r in rs), almax=max(r.almax.max() for r in rs),
                     nmax=max(r.n.max() for r in rs)))
out = pd.DataFrame(rows)
out.to_csv(sys.argv[2], index=False)
pd.set_option('display.width', 250)
print(out.round(3).to_string(index=False))
