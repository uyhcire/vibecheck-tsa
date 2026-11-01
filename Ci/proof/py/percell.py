"""Per-cell one-tick margin: short adversarial search per 50 m cell (worst ratio of the Lyapunov form or a fast
constraint to its bound after one tick; > 1 would be an exit)."""
import numpy as np, sys, subprocess, os
out = []
for a in range(10, 2680, 50):
    b = min(a + 50, 2679)
    r = subprocess.run(["uv", "run", "--with", "numpy", "python", "worst2.py", str(1000 + a), str(a), str(b)],
                       capture_output=True, text=True, env=dict(os.environ)).stdout
    line = [l for l in r.split("\n") if l.startswith("iter 14")]
    best = float(line[0].split("[")[1].split()[0]) if line else float("nan")
    out.append((a, b, best)); print(a, b, best, flush=True)
np.save("percell.npy", np.array(out))
