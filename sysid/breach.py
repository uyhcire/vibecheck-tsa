"""Usage: breach.py RESID.csv STATES.csv, with RESID from `jsbresid STATES --dump RESID` and STATES from collect.py.

Held-out check of a per-tick residual bound D: calibrate on half the episodes, count breaches
on the other half (ticks and whole flights). Also residual rate and autocorrelation."""
import csv, sys, numpy as np
R = list(csv.DictReader(open(sys.argv[1])))
S = {(int(float(r['ep'])), int(float(r['k']))): r for r in csv.DictReader(open(sys.argv[2]))}
comps = ['rx', 'rh', 'rvx', 'rvz', 'rth', 'rq']
ep = np.array([int(float(r['ep'])) for r in R]); k = np.array([int(float(r['k'])) for r in R])
A = np.array([[float(r[c]) for c in comps] for r in R])
lat = np.array([max(abs(float(S[(e, j)]['phi'])), abs(float(S[(e, j)]['beta']))) for e, j in zip(ep, k)])
def run(label, mask):
    cal, hold = mask & (ep % 2 == 0), mask & (ep % 2 == 1)
    for qname, q in [('max', 1.0), ('p99.9', 0.999), ('p99', 0.99)]:
        D = np.quantile(np.abs(A[cal]), q, axis=0)
        breach = (np.abs(A[hold]) > D).any(1)
        eps_hold = np.unique(ep[hold])
        lapsed = sum(breach[ep[hold] == e].any() for e in eps_hold)
        print(f'{label:22s} D=cal {qname:5s}: held-out ticks breached {breach.mean()*100:6.3f}%  '
              f'flights lapsed {lapsed}/{len(eps_hold)}  D(vx,vz,q)=({D[2]:.4f},{D[3]:.4f},{D[5]:.4f})')
    same = (ep[1:] == ep[:-1]) & (k[1:] == k[:-1] + 1) & mask[1:] & mask[:-1]
    d = np.abs(A[1:] - A[:-1])[same]
    rho = [np.corrcoef(A[:-1][same][:, i], A[1:][same][:, i])[0, 1] for i in range(6)]
    print(f'{"":22s} rate max (vx,vz,q)=({d[:,2].max():.4f},{d[:,3].max():.4f},{d[:,5].max():.4f}) '
          f'p99=({np.quantile(d[:,2],.99):.4f},{np.quantile(d[:,3],.99):.4f},{np.quantile(d[:,5],.99):.4f}) '
          f'lag-1 corr (vx,vz,q)=({rho[2]:.2f},{rho[3]:.2f},{rho[5]:.2f})')
run('all ticks', np.ones(len(A), bool))
run('|phi|,|beta| <= 0.01', lat <= 0.01)
