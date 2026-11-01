import numpy as np, subprocess, kinv, aff
from kinv import *
import aff as A
h0 = 1000; frac = 0.01
c = center(h0); P = Pat(h0); r = rat(h0) * frac
L = np.linalg.cholesky(P); Bs = r * np.linalg.inv(L.T)
G = Gat(h0); k = kat(h0); tk = tkat(h0) * A.SAFE * frac; tp = tpat(h0) * A.SAFE * frac
rows = np.zeros((21, 18))
for a, i in enumerate(yidx): rows[i, :7] = Sy[a] * Bs[a]
for b, i in enumerate(gidx):
    if i == 20: continue
    rows[i, :7] = Sg[b] * (G[b] @ Bs); rows[i, 7] = Sg[b] * k[b] * tk; rows[i, 8 + b] = Sg[b] * tp[b]
cen = c.copy(); cen[0] = 0; cen[1] = h0 * 65536; cen[11] = 0
inp = " ".join(str(int(round(v))) for v in cen) + "\n" + "\n".join(" ".join(str(int(round(v * 1000))) for v in row) for row in rows) + "\n"
out = subprocess.run([EXE, "aff"], input=inp, capture_output=True, text=True, check=True).stdout.strip().split("\n")
import os
if os.environ.get("PROBE"): print("\n".join(l for l in out if not l[0].isdigit() and not l.startswith("-")) ) 
print("input radius per field (raw):", {NAMES[i]: round(np.abs(rows[i]).sum(), 1) for i in range(21) if np.abs(rows[i]).sum() > 0})
for name, l in zip(["elev"] + NAMES[:19] + ["eI"], out):
    w = l.split()
    if name == "elev": w = w[1:]
    if len(w) < 3: continue
    print(f"{name:6s} c {float(w[0]):14.1f}  err {float(w[1]):12.1f}  lin-rad {np.abs(np.array([float(v) for v in w[2:]])).sum():10.1f}")
