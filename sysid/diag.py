import csv, math, numpy as np
rows = list(csv.DictReader(open('sysid/test.csv')))
ep = np.array([int(r['ep']) for r in rows]); same = ep[:-1] == ep[1:]
def col(c): return np.array([float(r[c]) for r in rows])[:-1][same]
phi, q, elev, thr, alpha = col('phi'), col('q'), col('elev'), col('thr'), col('alpha')
r = np.load('sysid/resid_ext.npy')
avz, avx, aq = np.abs(r[:, 3]), np.abs(r[:, 2]), np.abs(r[:, 5])
print('phi quantiles deg', np.round(np.degrees(np.quantile(np.abs(phi), [.5, .9, .99])), 1))
for lo, hi in [(0, 2), (2, 5), (5, 10), (10, 40)]:
    m = (np.abs(np.degrees(phi)) >= lo) & (np.abs(np.degrees(phi)) < hi)
    print(f'|phi| in [{lo},{hi}) n={m.sum():6d}  vz p90 {np.quantile(avz[m], .9):.3f} p99 {np.quantile(avz[m], .99):.3f}  vx p99 {np.quantile(avx[m], .99):.3f}')
for lo, hi in [(0, .1), (.1, .3), (.3, 2)]:
    m = (np.abs(q) >= lo) & (np.abs(q) < hi) & (np.abs(np.degrees(phi)) < 2)
    print(f'|q| in [{lo},{hi}) & level n={m.sum():6d}  vz p90 {np.quantile(avz[m], .9):.3f} p99 {np.quantile(avz[m], .99):.3f}')
print('corr(vz resid, cos phi - 1)', np.corrcoef(r[:, 3], np.cos(phi) - 1)[0, 1])
