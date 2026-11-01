"""Does the escape (our model + Jsb/Escape.lean law) satisfy the fitted mu=0.25 envelope's escape clauses,
read with Envelope3D (commit-referenced) semantics?"""
import sys
import pandas as pd
from mu025 import P, perf, DT

d = pd.read_csv(sys.argv[1])
bad_vz, bad_V, bad_vmin, n = {}, {}, {}, 0
for tag, r in d.groupby('tag'):
    n += 1
    V0, vz0 = r.V.iloc[0], r.vz.iloc[0]
    VF = max(P['vMin'], V0 - P['escV'])
    pull, climb = perf(VF)
    sig = vz0 - P['dvz']
    for k, (vz, Vm) in enumerate(zip(r.vz.values[1:], r.Vmin.values[1:]), start=1):
        if k > P['delay']:
            sig = min(climb, sig + DT * pull)
        if vz < sig:
            bad_vz.setdefault(tag, (V0, r.gam.iloc[0], k, vz, sig))
        if Vm < VF:
            bad_V.setdefault(tag, (V0, k))
        if Vm < P['vMin']:
            bad_vmin.setdefault(tag, (V0, r.gam.iloc[0]))
print(f"{n} runs; vz schedule violated in {len(bad_vz)}, airspeed floor V0-escVDrop violated in {len(bad_V)}, vMin=32 violated in {len(bad_vmin)}")
vzV = sorted({round(v[0]) for v in bad_vz.values()})
print("commit speeds with vz-schedule violations:", vzV)
ex = next(iter(bad_vz.values()), None)
print("example (V0, gam0, k, vz, sched):", ex and tuple(round(x, 2) for x in ex))
print("commit speeds with vMin violations:", sorted({round(v[0]) for v in bad_vmin.values()}))
