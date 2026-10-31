"""Bucket jsbresid --dump residuals by |bank| and |sideslip|: turns_buckets.py DATA.csv DUMP.csv [DUMP2.csv ...]."""
import sys, numpy as np

def load(path):
    return np.genfromtxt(path, delimiter=',', names=True)

def key(d):
    return {(int(e), int(k)): i for i, (e, k) in enumerate(zip(d['ep'], d['k']))}

def table(data, dumps, comps=('rvx', 'rvz', 'rq', 'rth'), edges=(0, 5, 15, 30, 46), by='phi'):
    idx = key(data)
    print('bucket by |%s| deg; each cell p99/max of |residual|' % by)
    for name, d in dumps:
        rows = np.array([idx[(int(e), int(k))] for e, k in zip(d['ep'], d['k'])])
        v = np.degrees(np.abs(data[by][rows]))
        print(f'-- {name}')
        for lo, hi in zip(edges[:-1], edges[1:]):
            m = (v >= lo) & (v < hi)
            cells = ' | '.join(f"{c} {np.percentile(np.abs(d[c][m]), 99):.4f}/{np.abs(d[c][m]).max():.4f}" for c in comps)
            print(f'  {lo:>2}-{hi:<2} n={m.sum():5d}: {cells}')

if __name__ == '__main__':
    data = load(sys.argv[1])
    dumps = [(p.split('/')[-1], load(p)) for p in sys.argv[2:]]
    table(data, dumps)
    table(data, dumps, edges=(0, 2, 4, 7, 15), by='beta')
