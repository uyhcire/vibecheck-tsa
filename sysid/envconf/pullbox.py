"""Pull-phase states (k >= K, gam < 0) of one commit-speed cell: ranges, and sample points of the box
(corners + uniform) and of a data-coupled sub-region, for the `envconf onetick` pointwise check."""
import sys
import numpy as np
import pandas as pd

grid, V0, K, out = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
d = pd.read_csv(grid)
meta = d[d.k == 0].set_index('tag')
tags = meta.index[(meta.V.round(0) == V0) & (meta.gam <= -0.099)]
x = d[d.tag.isin(tags) & (d.k >= K) & (d.gam < 0)].copy()
x['tmap'] = 0.0
cols = ['h', 'V', 'gam', 'al', 'q', 'elev', 'rpm']
print(len(x), 'pull-phase states from', len(tags), 'runs')
print(x[cols + ['n']].describe().loc[['min', 'max']].round(3).to_string())
print('min n in pull phase', x.n.min().round(3))
# linear fit of elev and q on (V, gam, al): the coupling the box ignores
A = np.c_[np.ones(len(x)), x.V, x.gam, x.al]
ce, *_ = np.linalg.lstsq(A, x.elev, rcond=None)
cq, *_ = np.linalg.lstsq(A, x.q, rcond=None)
re = x.elev - A @ ce
rq = x.q - A @ cq
print('elev ~', ce.round(4), 'resid range', re.min().round(3), re.max().round(3))
print('q    ~', cq.round(4), 'resid range', rq.min().round(3), rq.max().round(3))
rng = np.random.default_rng(1)
lo, hi = x[cols].min().values, x[cols].max().values
pts = []
for i in range(4000):
    u = rng.random(len(cols))
    if i % 2 == 0:
        u = (u > 0.5).astype(float)
    pts.append(('box', lo + (hi - lo) * u))
for i in range(4000):
    u = rng.random(len(cols))
    p = lo + (hi - lo) * u
    V, gam, al = p[1], p[2], p[3]
    b = np.array([1, V, gam, al])
    p[5] = b @ ce + re.min() + (re.max() - re.min()) * rng.random()
    p[4] = b @ cq + rq.min() + (rq.max() - rq.min()) * rng.random()
    pts.append(('coupled', p))
with open(out, 'w') as f, open(out + '.kind', 'w') as g:
    for kind, p in pts:
        f.write(' '.join(f'{v:.6f}' for v in p) + ' 0 1\n')
        g.write(kind + '\n')
