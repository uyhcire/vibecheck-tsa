"""T v3 bounding boxes per altitude cell (fields, vz-pvz, pvz-pvz2) and interval safety checks of one tick."""
import numpy as np, sys, subprocess, kinv
from kinv import *
import os; R = float(os.environ.get("RR", "6.0")); SAFE = float(os.environ.get("SAFE", "1.25"))
def thrH(hraw): return max(0, min(65536, 65536 - max(0, hraw - 2500*65536)//500))
NF = len(GI)
def lin_bounds(h, pad):
    """for each raw field (and d1, d2): centre value and half-width over T at altitude h"""
    c = center(h); P = Pat(h); Pi = np.linalg.inv(P); G = Gat(h); k = kat(h)
    tk = tkat(h) * SAFE; tp = tpat(h) * SAFE + 2 / Sg
    # raw field = c + A_y y + A_l lam + A_p perp ; y in ellipse, |lam|<=tk, |perp_i|<=tp_i
    rows = {}
    for a, i in enumerate(yidx):
        Ay = np.zeros(7); Ay[a] = Sy[a]; rows[i] = (Ay, 0.0, np.zeros(NF))   # i = 19 is the memory eI
    for b, i in enumerate(gidx):
        if i == 20: continue
        Ay = G[b] * Sg[b]; Al = k[b] * Sg[b]; Ap = np.zeros(NF); Ap[b] = Sg[b]; rows[i] = (Ay, Al, Ap)
    def half(Ay, Al, Ap): return rat(h) * np.sqrt(Ay @ Pi @ Ay) * pad + abs(Al) * tk + np.abs(Ap) @ tp
    out = {i: (c[i], half(*rows[i])) for i in rows}
    out[19] = (c[19], half(*rows[19]))
    for name, (i, j) in {"d1": (3, 17), "d2": (17, 18)}.items():
        Ay = rows[i][0] - rows[j][0]; Al = rows[i][1] - rows[j][1]; Ap = rows[i][2] - rows[j][2]
        out[name] = (c[i] - c[j], half(Ay, Al, Ap))
    return out
def cellbox(ha, hb, pad=1.02):
    lo = {}; hi = {}
    for h in np.linspace(ha, hb, 6):
        for key, (cv, hw) in lin_bounds(h, pad).items():
            lo[key] = min(lo.get(key, np.inf), cv - hw); hi[key] = max(hi.get(key, -np.inf), cv + hw)
    L = np.zeros(19); H = np.zeros(19)
    for i in range(19):
        if i in lo: L[i], H[i] = lo[i], hi[i]
    L[0], H[0] = -2**40, 2**40; L[1], H[1] = ha*65536, hb*65536; L[11] = H[11] = 0
    return np.floor(L).astype(np.int64), np.ceil(H).astype(np.int64), (int(np.floor(lo["d1"])), int(np.ceil(hi["d1"])), int(np.floor(lo["d2"])), int(np.ceil(hi["d2"])), int(np.floor(lo[19])), int(np.ceil(hi[19])))
def check(cells, elev=(-65536, 65536)):
    lines = []
    for ha, hb in cells:
        lo, hi, d = cellbox(ha, hb)
        st = list(lo) + list(hi) + [elev[0], elev[1], thrH(int(hb*65536)), thrH(int(ha*65536))] + list(d)
        lines.append(" ".join(str(int(v)) for v in st))
    out = subprocess.run([EXE, "ivcheck"], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout
    return out.strip().split("\n")
if __name__ == "__main__":
    w = float(sys.argv[1]); el = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (-65536, 65536)
    cells = [(a, min(a + w, 2640)) for a in np.arange(10, 2640, w)]
    res = check(cells, el); nbad = 0
    for (ha, hb), r in zip(cells, res):
        flags = [seg.split(" vz")[0] for seg in r.split(" | ")]
        ok = all(f == "[1, 1, 1, 1, 1]1" for f in flags); nbad += not ok
        if not ok: print(f"{ha:.0f}-{hb:.0f}: BAD {flags}")
    print("cells", len(cells), "bad", nbad)
