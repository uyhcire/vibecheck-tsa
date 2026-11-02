"""How the level trim moves with latitude (north offset) and held track: the slowly varying parameter of the
level-trim certificate (docs/termsound-proof.tex, Section 6)."""
import sys, json
import numpy as np
from tsmap import TsMap
from terminal import NEW
from level_cert import SC, NAMES33
import ref as refmod

m = TsMap(); m.smooth(True); m.cand(**NEW)
ref = refmod.load()
out = {}
x0 = None
for psi, label in ((np.pi / 2, "east"), (3 * np.pi / 2, "west")):
    trims = {}
    for north in (100.0, 10000.0, 50000.0):
        sim = m.sim(900.0, refmod.c_of(ref, 900.0), 128 * 240, 128 * 240, psi=psi, north=north)
        sim2 = m.sim(sim[-1][3], sim[-1][4:], 128 * 120, 128 * 120, psi=psi, north=north)
        x = np.concatenate([[sim2[-1][3]], sim2[-1][4:]])   # settled after 360 s (the box Newton is not used here)
        trims[north] = x
        print(f"{label} north {north:7.0f}: h {x[0]:.4f} V {x[4]:.4f} v_rt {x[5]:.5f} theta {x[2]:.6f} phi {x[1]:.6f}", flush=True)
    g1 = np.abs(trims[10000.0] - trims[100.0]) / 9900.0 / SC
    g2 = np.abs(trims[50000.0] - trims[10000.0]) / 40000.0 / SC
    out[label] = dict(dxdN_scaled=np.maximum(g1, g2).tolist(), v_rt=float(trims[100.0][5]),
                      trims={str(k): v.tolist() for k, v in trims.items()})
    print(f"  max scaled |dx*/dN| per m: {np.maximum(g1, g2).max():.3e} ({NAMES33[np.argmax(np.maximum(g1, g2))]})", flush=True)
json.dump(out, open("/tmp/ts_level_param.json", "w"), indent=1)
