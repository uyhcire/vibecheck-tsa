"""Is the model-mismatch residual smooth in time? Compare |r| with |r_{k+1} - r_k|."""
import csv, numpy as np
rows = list(csv.DictReader(open('sysid/test.csv')))
ep = np.array([int(r['ep']) for r in rows])
r = np.load('sysid/resid_ext1.npy')
ok = (ep[1:-1] == ep[:-2]) & (ep[2:] == ep[1:-1])
ok = ok[:len(r) - 1]
for i, n in [(2, 'vx'), (3, 'vz'), (5, 'q')]:
    a = r[:, i]
    d = np.abs(a[1:] - a[:-1])[ok[:len(a) - 1]]
    rho = np.corrcoef(a[:-1][ok[:len(a)-1]], a[1:][ok[:len(a)-1]])[0, 1]
    print(f'{n}: |r| p99 {np.quantile(np.abs(a), .99):.4f} max {np.abs(a).max():.4f} | '
          f'|dr| p99 {np.quantile(d, .99):.4f} max {d.max():.4f} | lag-1 corr {rho:.3f}')
