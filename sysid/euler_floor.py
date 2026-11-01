"""Residual of Euler at 1/16 s with JSBSim's exact accelerations at the tick start."""
import csv, numpy as np
rows = list(csv.DictReader(open('sysid/test.csv')))
ep = np.array([int(r['ep']) for r in rows]); ok = ep[:-1] == ep[1:]
c = lambda n: np.array([float(r[n]) for r in rows])
vx, vz, q, ax0, az0, qd0 = c('vx'), c('vz'), c('q'), c('ax0'), c('az0'), c('qd0')
for name, v, a in [('vx', vx, ax0), ('vz', vz, az0), ('q', q, qd0)]:
    e = np.abs((v[1:] - v[:-1] - a[:-1] / 16)[ok])
    print(f'{name}: p50 {np.quantile(e,.5):.3f} p90 {np.quantile(e,.9):.3f} p99 {np.quantile(e,.99):.3f} max {e.max():.3f}')
