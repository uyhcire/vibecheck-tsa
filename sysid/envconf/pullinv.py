"""Candidate pull-phase invariant R_P for one commit-speed cell, fitted to pull-phase trajectory states:
  V in [Vlo, Vhi], gam in [glo, 0), alpha in [a0 + ag*gam + aV*(V - Vc) - wa, amax],
  elev in fe(V, gam, al) +- we, q in fq(V, gam, al) +- wq.
`sample` writes points of R_P (half of them on the alpha floor face) for `envconf onetick`;
`check` tests the one-tick pull clause and whether each face of R_P is kept (or the pull phase is exited)."""
import json
import sys
import numpy as np
import pandas as pd

DT, G = 1 / 16, 9.80665


def fit(grid, V0, K):
    d = pd.read_csv(grid)
    meta = d[d.k == 0].set_index('tag')
    tags = meta.index[(meta.V.round(0) == V0) & (meta.gam <= -0.099)]
    x = d[d.tag.isin(tags) & (d.k >= K) & (d.gam < 0)]
    Vc = float(V0)
    A = np.c_[np.ones(len(x)), x.gam, x.V - Vc]
    # alpha floor: least squares, then shifted down to touch the lowest state
    ca, *_ = np.linalg.lstsq(A, x.al, rcond=None)
    ra = x.al - A @ ca
    B = np.c_[np.ones(len(x)), x.V - Vc, x.gam, x.al]
    ce, *_ = np.linalg.lstsq(B, x.elev, rcond=None)
    cq, *_ = np.linalg.lstsq(B, x.q, rcond=None)
    re, rq = x.elev - B @ ce, x.q - B @ cq
    R = dict(Vc=Vc, Vlo=x.V.min(), Vhi=x.V.max(), glo=x.gam.min(), ca=list(ca), wa=float(-ra.min()), amax=0.28,
             ce=list(ce), we=float(max(-re.min(), re.max())), cq=list(cq), wq=float(max(-rq.min(), rq.max())),
             hlo=x.h.min(), hhi=x.h.max(), rlo=x.rpm.min(), rhi=x.rpm.max(), nmin=float(x.n.min()))
    return R


def floor_a(R, V, g):
    return R['ca'][0] + R['ca'][1] * g + R['ca'][2] * (V - R['Vc']) - R['wa']


def sample(R, out, n, slack=1.0):
    rng = np.random.default_rng(2)
    pts, kinds = [], []
    while len(pts) < n:
        V = rng.uniform(R['Vlo'], R['Vhi']); g = rng.uniform(R['glo'], 0)
        fa = floor_a(R, V, g)
        on_face = len(pts) % 2 == 0
        al = fa if on_face else rng.uniform(fa, R['amax'])
        b = np.array([1, V - R['Vc'], g, al])
        e = b @ R['ce'] + slack * R['we'] * rng.uniform(-1, 1)
        q = b @ R['cq'] + slack * R['wq'] * rng.uniform(-1, 1)
        if rng.random() < 0.5:   # push e, q to their band edges
            e = b @ R['ce'] + slack * R['we'] * rng.choice([-1, 1])
            q = b @ R['cq'] + slack * R['wq'] * rng.choice([-1, 1])
        h = rng.uniform(R['hlo'], R['hhi']); rpm = rng.uniform(R['rlo'], R['rhi'])
        pts.append([h, V, g, al, q, e, rpm, 0, 1]); kinds.append('face' if on_face else 'inner')
    with open(out, 'w') as f, open(out + '.kind', 'w') as k:
        for p, kd in zip(pts, kinds):
            f.write(' '.join(f'{v:.6f}' for v in p) + '\n'); k.write(kd + '\n')


def check(R, pts, outp, nmin):
    P = pd.read_csv(pts, sep=' ', header=None, names=['h', 'V', 'gam', 'al', 'q', 'e', 'rpm', 'tmap', 'thr'])
    P['kind'] = open(pts + '.kind').read().split()
    X = pd.concat([P, pd.read_csv(outp)], axis=1)
    X['pull'] = (X.gam1 - X.gam) - DT * G * (nmin - np.cos(X.gam)) / R['Vhi']
    exitp = X.gam1 >= 0
    b1 = np.c_[np.ones(len(X)), X.V1 - R['Vc'], X.gam1, X.al1]
    faces = {
        'alpha floor': X.al1 - floor_a(R, X.V1, X.gam1),
        'alpha max': R['amax'] - X.almax,
        'elev band': R['we'] - (X.e1 - b1 @ R['ce']).abs(),
        'q band': R['wq'] - (X.q1 - b1 @ R['cq']).abs(),
        'V band': np.minimum(X.V1 - R['Vlo'], R['Vhi'] - X.V1),
    }
    print(f"pull clause (nmin {nmin:.2f}): fails at {(X.pull < 0).sum()}/{len(X)}, worst {X.pull.min():.4f} rad/tick")
    for name, m in faces.items():
        bad = (m < 0) & ~exitp
        print(f"  face {name:12s}: violated after one tick at {bad.sum():5d}/{len(X)} (from face pts {(bad & (X.kind == 'face')).sum()}), worst {m[~exitp].min():.4f}")


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'fit':
        R = fit(sys.argv[2], float(sys.argv[3]), int(sys.argv[4]))
        json.dump(R, open(sys.argv[5], 'w'), indent=1); print(json.dumps(R, indent=1))
    elif cmd == 'sample':
        sample(json.load(open(sys.argv[2])), sys.argv[3], int(sys.argv[4]), float(sys.argv[5]) if len(sys.argv) > 5 else 1.0)
    elif cmd == 'check':
        R = json.load(open(sys.argv[2]))
        check(R, sys.argv[3], sys.argv[4], float(sys.argv[5]) if len(sys.argv) > 5 else R['nmin'])
