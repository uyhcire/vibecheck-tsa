"""Per-tick gap between the real (Float stand-in) tick and the Fx tick from the same state, over samples of T,
in STEP units of the slow coordinates (and raw for others)."""
import numpy as np, subprocess, kinv, sys
from kinv import *
n = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
X = np.concatenate([ksample(n // 2, r=R * 0.99, fl=1.2, fp=1.2), ksample(n // 2, r=R * 0.5, fl=0.5, fp=0.5)])
inp = "\n".join(" ".join(str(int(v)) for v in x) for x in X) + "\n"
out = subprocess.run([EXE, "realgap"], input=inp, capture_output=True, text=True, check=True).stdout.strip().split("\n")
D = np.array([[float(v) for v in l.split()] for l in out])
names = ["h", "vx", "vz", "dx", "dz", "q", "rpm", "tmap", "au", "ah", "wdot", "qd"]
steps = {"vx": 6554, "vz": 6554, "dz": 655, "q": 655, "rpm": 655360, "tmap": 6554, "au": 6554, "ah": 6554, "wdot": 6554, "qd": 6554, "h": 65536, "dx": 66}
for k, nm in enumerate(names):
    a = np.abs(D[:, k])
    print(f"{nm:5s} max {a.max():10.2f} raw = {a.max() / steps[nm]:.5f} STEP   p99 {np.quantile(a, 0.99) / steps[nm]:.5f}   mean {a.mean() / steps[nm]:.5f}")
