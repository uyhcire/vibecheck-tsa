import subprocess, sys
from provbox import cellbox_prov
from pf import EXE
ci = int(sys.argv[1])
L, H, elo, ehi = cellbox_prov(ci)
line = " ".join(str(int(v)) for v in L + H + [elo, ehi]) + "\n"
for f in sys.argv[2:]:
    out = subprocess.run([EXE, "safecheck", "22", "0", f], input=line, capture_output=True, text=True, check=True).stdout.strip()
    print(f, out)
