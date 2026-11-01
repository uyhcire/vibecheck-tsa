"""Per-run summary of escape trajectories written by `envconf fly/grid`."""
import sys
import pandas as pd

d = pd.read_csv(sys.argv[1])
for tag, r in d.groupby('tag'):
    r0 = r.iloc[0]
    hmin = r.hmin.iloc[1:].min()
    kmin = int(r.k.iloc[1:][r.hmin.iloc[1:].idxmin() - r.index[0] - 1]) if False else int(r.loc[r.hmin.iloc[1:].idxmin(), 'k'])
    print(f"run {tag}: V0 {r0.V:.1f} gam0 {r0.gam:+.2f} al0 {r0.al:.3f} rpm0 {r0.rpm:.0f} | loss {r0.h - hmin:6.2f} m at k {kmin:3d} | "
          f"Vmin {r.Vmin.min():5.1f} Vmax {r.V.max():5.1f} almax {r.almax.max():.3f} nmax {r.n.max():.2f} nmin {r.n.iloc[1:].min():.2f} "
          f"elevmax {r.elev.max():.2f} | end V {r.V.iloc[-1]:.1f} vz {r.vz.iloc[-1]:.2f} gam {r.gam.iloc[-1]:.3f} | Emin-E0 {r.E.min()-r0.E:.1f}")
