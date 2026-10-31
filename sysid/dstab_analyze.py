"""D-stability analysis: running max, per-regime max, held-out lapse rates, GPD tail of per-flight maxima."""
import csv, sys, numpy as np
from scipy.stats import genpareto
RNG = np.random.default_rng(0)
C8 = ['rx', 'rh', 'rvx', 'rvz', 'rth', 'rq', 'rrpm', 'rmap']
CORE = [2, 3, 5, 0, 1, 4]                                  # vx, vz, q, x, h, theta first in tables

def load(res, coll, meta):
    A = np.genfromtxt(res, delimiter=',', skip_header=1)
    ep = A[:, 0].astype(int); k = A[:, 1].astype(int); A = np.abs(A[:, 2:])
    f = open(coll); hdr = f.readline().strip().split(','); ix = [hdr.index(c) for c in ('ep', 'k', 'alpha', 'thr', 'vt', 'h', 'stallh')]
    S = {}
    for line in f:
        t = line.split(',')
        S[(int(float(t[ix[0]])), int(float(t[ix[1]])))] = [float(t[i]) for i in ix[2:]]
    X = np.array([S[(e, j)] for e, j in zip(ep, k)])
    M = {int(r['ep']): r for r in csv.DictReader(open(meta))}
    return dict(ep=ep, k=k, A=A, alpha=X[:, 0], thr=X[:, 1], vt=X[:, 2], h=X[:, 3], stallh=X[:, 4], M=M)

def flight_max(d):
    eps = np.unique(d['ep'])
    FM = np.array([d['A'][d['ep'] == e].max(0) for e in eps])
    return eps, FM

def running(d, sizes, perms=200):
    eps, FM = flight_max(d)
    print('\n== D = max over first N flights (median [min..max] over random orderings); ratio to all-flight max ==')
    print(f'{"N":>5s} ' + ' '.join(f'{C8[i]:>24s}' for i in CORE[:3] + [3 - 3 + 0, 4][:0]) if False else '', end='')
    hdr = [2, 3, 5, 4, 0, 1]
    print(f'{"N flights":>9s} {"ticks":>8s} ' + ' '.join(f'{C8[i]:>22s}' for i in hdr))
    tot = FM.max(0)
    cnt = {e: (d['ep'] == e).sum() for e in eps}
    for n in sizes:
        if n > len(eps): continue
        vals = np.array([FM[RNG.permutation(len(eps))[:n]].max(0) for _ in range(perms)])
        med = np.median(vals, 0); lo = vals.min(0); hi = vals.max(0)
        ticks = int(np.mean(list(cnt.values())) * n)
        print(f'{n:9d} {ticks:8d} ' + ' '.join(f'{med[i]:.4f} [{lo[i]/tot[i]:.2f}-{hi[i]/tot[i]:.2f}]x'.rjust(22) for i in hdr))
    print(f'{"all":>9s} {len(d["ep"]):8d} ' + ' '.join(f'{tot[i]:.4f}'.rjust(22) for i in hdr))
    print('growth of max over the last doubling (median ratio max(N)/max(N/2), N=all/all2 splits):')
    r = []
    for _ in range(200):
        p = RNG.permutation(len(eps)); r.append(FM[p].max(0) / FM[p[:len(eps) // 2]].max(0))
    print('  ' + ' '.join(f'{C8[i]}:{np.median(r,0)[i]:.2f}' for i in range(8)))

def regimes(d):
    M = d['M']
    sty = np.array([M[e]['style'] for e in d['ep']]); v0 = np.array([float(M[e]['v0']) for e in d['ep']])
    h0 = np.array([float(M[e]['h0']) for e in d['ep']])
    A = d['A']
    def tab(title, labels):
        print(f'\n== max |residual| per regime: {title} ==')
        print(f'{"regime":>14s} {"flights":>7s} {"ticks":>8s} ' + ' '.join(f'{C8[i]:>9s}' for i in [2, 3, 5, 4, 0, 1]))
        for lab in sorted(set(labels)):
            m = labels == lab
            print(f'{lab:>14s} {len(np.unique(d["ep"][m])):7d} {m.sum():8d} ' + ' '.join(f'{A[m][:, i].max():9.4f}' for i in [2, 3, 5, 4, 0, 1]))
    tab('pilot style', sty)
    tab('initial speed kt', np.array([f'v0 {int(v//20)*20}-{int(v//20)*20+20}' for v in v0]))
    tab('initial altitude ft', np.array([f'h0 {int(h//2000)*2000}-{int(h//2000)*2000+2000}' for h in h0]))
    al = np.degrees(d['alpha'])
    tab('tick alpha deg', np.array([f'a {int(a//4)*4}..{int(a//4)*4+4}' if -4 <= a < 16 else ('a<-4' if a < -4 else 'a>=16') for a in al]))
    tab('tick throttle', np.array([f'thr {min(int(t*4),3)/4:.2f}+' for t in d['thr']]))
    tab('tick airspeed m/s', np.array([f'vt {int(v//10)*10}' for v in d['vt']]))
    tab('stall hysteresis', np.array(['stallh>0' if s > 1e-3 else 'stallh=0' for s in d['stallh']]))
    print('\n== who sets the max: top-5 ticks per component (style, v0 kt, alpha deg, thr, vt m/s) ==')
    for i in [3, 2, 5, 4, 0, 1]:
        o = np.argsort(-A[:, i])[:5]
        print(f' {C8[i]}: ' + '; '.join(f'{A[j,i]:.4f} ({M[d["ep"][j]]["style"]}, {float(M[d["ep"][j]]["v0"]):.0f}, {al[j]:.1f}, {d["thr"][j]:.2f}, {d["vt"][j]:.0f})' for j in o))
    print('  share of the top-0.1% ticks by style: ' + '; '.join(
        f'{c}: ' + ', '.join(f'{s} {np.mean(sty[A[:, c] >= np.quantile(A[:, c], .999)] == s):.2f}' for s in sorted(set(sty))) for c in [3, 2, 5]).replace(';', '\n   '))

def lapse(d, sizes, splits=100):
    eps, FM = flight_max(d)
    print('\n== held-out flight lapse rate: calibrate D on n random flights, test on a disjoint random half of the rest ==')
    for lab, idx in [('all 8 components', list(range(8))), ('6 core (x,h,vx,vz,theta,q)', [0, 1, 2, 3, 4, 5])]:
        print(f' -- lapse = any of: {lab}')
        print(f'{"n_cal":>6s} ' + ' '.join(f'{q:>16s}' for q in ['D=max', 'D=1.25*max', 'D=1.5*max', 'D=2*max', 'D=p99.9 ticks']))
        for n in sizes:
            if n > len(eps) // 2: continue
            out = np.zeros((splits, 5))
            for s in range(splits):
                p = RNG.permutation(len(eps)); cal = p[:n]; test = p[len(eps) // 2:]
                calm = np.isin(d['ep'], eps[cal])
                Dm = FM[cal].max(0)
                Dp = np.quantile(d['A'][calm], 0.999, axis=0)
                for j, D in enumerate([Dm, 1.25 * Dm, 1.5 * Dm, 2 * Dm, Dp]):
                    out[s, j] = (FM[test][:, idx] > D[idx]).any(1).mean()
            print(f'{n:6d} ' + ' '.join(f'{out[:, j].mean()*100:6.2f}% (<={np.quantile(out[:, j], .95)*100:5.1f}%)'.rjust(16) for j in range(5)))

def tail(d):
    eps, FM = flight_max(d)
    print(f'\n== GPD tail of per-flight maxima (peaks over threshold = 80th pct of {len(eps)} flight maxima) ==')
    print('P(new flight > max of all N flights) is exactly 1/(N+1) by exchangeability = %.4f; the GPD gives the return levels:' % (1 / (len(eps) + 1)))
    print(f'{"comp":>6s} {"max":>8s} {"xi":>6s} {"xi 90% CI":>14s} {"D@p=1e-2":>9s} {"D@1e-3":>9s} {"D@1e-4":>9s} {"D@1e-6":>9s} {"P(>max) GPD":>12s}')
    for i in [2, 3, 5, 4, 0, 1, 6, 7]:
        x = FM[:, i]; u = np.quantile(x, 0.8); ex = x[x > u] - u
        c, _, sc = genpareto.fit(ex, floc=0)
        bs = []
        for _ in range(200):
            b = RNG.choice(ex, len(ex)); bs.append(genpareto.fit(b, floc=0)[0])
        rate = len(ex) / len(x)
        rl = lambda p: u + genpareto.ppf(1 - p / rate, c, scale=sc)
        pmax = rate * genpareto.sf(x.max() - u, c, scale=sc)
        print(f'{C8[i]:>6s} {x.max():8.4f} {c:6.2f} [{np.quantile(bs,.05):5.2f},{np.quantile(bs,.95):5.2f}] ' + ' '.join(f'{rl(p):9.4f}' for p in (1e-2, 1e-3, 1e-4, 1e-6)) + f' {pmax:12.5f}')
    print('(xi<0: bounded tail, a finite supremum exists; xi>0: heavy tail, D grows without bound as p shrinks)')

def cross(d, dc):
    eps, FM = flight_max(d); _, FMc = flight_max(dc)
    D = FMc.max(0)
    print('\n== this set vs D = max of the reference set ==')
    print(f'flights {len(eps)}; flights exceeding reference D (any of 8): {(FM > D).any(1).sum()} ({(FM > D).any(1).mean()*100:.1f}%)')
    for i in range(8):
        print(f'  {C8[i]:>5s}: ref D {D[i]:.4f}  this max {FM[:, i].max():.4f}  ratio {FM[:, i].max()/D[i]:.2f}  flights over {(FM[:, i] > D[i]).sum()}  ticks over {(d["A"][:, i] > D[i]).sum()}')

if __name__ == '__main__':
    d = load(*sys.argv[1:4])
    ref = load(*sys.argv[5:8]) if len(sys.argv) > 7 and sys.argv[4] == '--ref' else None
    print(f'{len(np.unique(d["ep"]))} flights, {len(d["ep"])} ticks')
    n_all = len(np.unique(d['ep']))
    sizes = [n for n in (10, 25, 50, 100, 200, 400, 800, 1600) if n <= n_all]
    running(d, sizes); lapse(d, [5, 10, 20, 50, 100, 200, 400, 600]); regimes(d); tail(d)
    if ref: cross(d, ref)
