"""Pointwise one-tick pull clause on sampled region points (box vs data-coupled region)."""
import sys
import numpy as np
import pandas as pd

pts, outp, nmin, Vhi = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4])
P = pd.read_csv(pts, sep=' ', header=None, names=['h', 'V', 'gam', 'al', 'q', 'e', 'rpm', 'tmap', 'thr'])
P['kind'] = open(pts + '.kind').read().split()
O = pd.read_csv(outp)
X = pd.concat([P.reset_index(drop=True), O], axis=1)
DT, G = 1 / 16, 9.80665
X['need'] = DT * G * (nmin - np.cos(X.gam)) / Vhi
X['marg'] = (X.gam1 - X.gam) - X.need
for kind, x in X.groupby('kind'):
    bad = x[x.marg < 0]
    print(f"{kind}: {len(x)} pts, pull clause fails at {len(bad)} ({100*len(bad)/len(x):.1f}%), worst margin {x.marg.min():.4f} rad/tick "
          f"(need ~{x.need.mean():.4f}); n1<nmin at {(x.n1 < nmin).sum()}; almax>0.28 at {(x.almax > 0.28).sum()}, max alpha {x.almax.max():.3f}")
    if len(bad):
        w = bad.sort_values('marg').iloc[0]
        print('   worst point:', w[['V', 'gam', 'al', 'q', 'e', 'rpm', 'n0', 'n1', 'marg']].round(3).to_dict())
