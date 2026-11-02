"""Scan of candidate terminal-phase parameters: trim alpha across the band, and settling statistics."""
import sys
import numpy as np
from tsmap import TsMap, NAMES
from design import reference, settle, stats, say, c_at

m = TsMap(); m.smooth(True)
configs = [dict(vRefE=v, kv=k) for k in (0.02, 0.04, 0.06) for v in (36.0,)] + \
          [dict(vRefE=36.0, kv=0.04, kg=k) for k in (3.5,)] + [dict(vRefE=36.0, kv=0.06, kg=4.0)]
for c in configs:
    m.cand(**c)
    ref = reference(m)
    alphas = []
    for h in (10.0, 500.0, 1000.0):
        alphas.append(m.diag(h, c_at(ref, h))["alpha"])
    V = [c_at(ref, h)[3] for h in (10.0, 1000.0)]
    climb = [-c_at(ref, h)[5] for h in (10.0, 1000.0)]
    st = stats(settle(m, ref))
    say(c, "alpha(10,500,1000)", np.round(alphas, 5), "V", np.round(V, 2), "climb", np.round(climb, 3), st)
