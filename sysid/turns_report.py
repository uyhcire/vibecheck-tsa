"""Residual tables for turning flight: turns_report.py DATA.csv  (needs `lake build jsbresid`; run from the repo root)."""
import os, subprocess, sys, tempfile
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from turns_buckets import load, table

EXT = ['--kin', '--coup', '--gyro', '--side', '--rot', '--exact', '--phidot']
BIN = '.lake/build/bin/jsbresid'

def run(data, flags, tag):
    out = os.path.join(tempfile.gettempdir(), f'turns_{tag}.csv')
    subprocess.run([BIN, data, '--phi', '100', '--beta', '100', '--dump', out, *flags], check=True, capture_output=True)
    return load(out)

def main():
    data = sys.argv[1]
    d = load(data)
    cfgs = [('no-lat', []), ('lat', ['--lat']), ('lat+kin', ['--lat', '--kin']), ('lat+all', ['--lat', *EXT])]
    dumps = [(n, run(data, f, n.replace('+', '_'))) for n, f in cfgs]
    table(d, dumps, comps=('rvx', 'rvz', 'rq'))
    table(d, dumps, comps=('rvx', 'rvz', 'rq'), edges=(0, 2, 4, 7, 15), by='beta')
    print('leave-one-out from lat+all: overall p99/max of vx, vz, q')
    for drop in [None, *EXT]:
        fl = ['--lat', *[e for e in EXT if e != drop]]
        r = run(data, fl, 'loo')
        cells = ' | '.join(f"{c} {np.percentile(np.abs(r[c]), 99):.4f}/{np.abs(r[c]).max():.4f}" for c in ('rvx', 'rvz', 'rq'))
        print(f"  without {drop or 'nothing':8s}: {cells}")

if __name__ == '__main__':
    main()
