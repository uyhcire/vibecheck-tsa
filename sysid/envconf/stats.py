"""Global trajectory statistics over the commit grid: transient, stall, load, speed floor, climb-out."""
import sys
import numpy as np
import pandas as pd

d = pd.read_csv(sys.argv[1])
meta = d[d.k == 0].set_index('tag')
g = d.groupby('tag')
K = 8
first = d[d.k <= K + 1]
dg = (meta.gam - first.groupby('tag').gam.min())
print(f"transient (k<={K+1}): max gam drop {dg.max():.4f} rad, at commit {meta.loc[dg.idxmax(), ['V','gam','al','q','elev','rpm']].round(3).to_dict()}")
desc = meta.index[meta.gam <= -0.05]
de = first[first.tag.isin(desc)].sort_values(['tag', 'k']).groupby('tag').elev.apply(lambda s: np.diff(s.values).min())
print(f"elevator nondecreasing over the first {K} ticks in {(de >= -1e-9).sum()}/{len(de)} descending commits; min step {de.min():.4f}")
nT = first[first.tag.isin(desc) & (first.k >= 1)]
print(f"transient n - cos(gam) min over descending commits: {(nT.n - np.cos(nT.gam)).min():.3f}")
print(f"alpha max over all runs {d.almax.max():.3f} (CLmax at 0.28); runs with alpha > 0.25: {(g.almax.max() > 0.25).sum()}")
nm = g.n.max()
print(f"n max {nm.max():.2f}; runs with n > 3.8: {(nm > 3.8).sum()} / {len(nm)}; smallest commit V among them {meta.loc[nm[nm > 3.8].index, 'V'].min():.1f}")
vm = g.Vmin.min()
print(f"V min over runs {vm.min():.2f} at commit {meta.loc[vm.idxmin(), ['V','gam','al','q','rpm']].round(3).to_dict()}")
last = d[d.k == d.k.max()]
print(f"end state (k={d.k.max()}): V {last.V.min():.2f}..{last.V.max():.2f}, gam {last.gam.min():.3f}..{last.gam.max():.3f}, vz {last.vz.min():.2f}..{last.vz.max():.2f}")
# climb-out entry: first tick with gam >= 0 after which gam stays >= 0
neg_after = d[(d.k >= 40)].groupby('tag').gam.min()
print(f"runs with gam < 0 at some k >= 40: {(neg_after < 0).sum()}; their commit V range {meta.loc[neg_after[neg_after < 0].index, 'V'].min():.1f}..{meta.loc[neg_after[neg_after < 0].index, 'V'].max():.1f}")
