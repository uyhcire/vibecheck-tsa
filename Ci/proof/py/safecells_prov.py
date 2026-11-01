import subprocess, time, sys
from provbox import cellbox_prov
from pf import EXE
lines = []
for ci in range(267):
    L, H, elo, ehi = cellbox_prov(ci)
    lines.append(" ".join(str(int(v)) for v in L + H + [elo, ehi]))
t = time.time()
out = subprocess.run([EXE, "safecheck", "22", "0", sys.argv[1] if len(sys.argv) > 1 else "5"], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.strip().split("\n")
bad = [(10 + 10 * i, o) for i, o in enumerate(out) if o != "true 1"]
print("cells", len(out), "non-trivial:", bad[:20], "time", round(time.time() - t, 1))
