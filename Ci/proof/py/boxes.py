"""Bounding boxes of T per altitude cell, and interval safety checks of one tick over them (any elevator)."""
import numpy as np, sys, os, subprocess, sample as sm
from sample import *
sm.GsN = np.load("GsN_fit.npy"); tolN = np.load("tolN.npy")
R = 6.0
def tolat(h): return sm.interpN(tolN, h)
def thrH(hraw): return max(0, min(65536, 65536 - max(0, hraw - 2500*65536)//500))
def cellbox(ha, hb, pad=1.02):
    hs = np.linspace(ha, hb, 6)
    lo = np.full(21, np.inf); hi = np.full(21, -np.inf)
    for h in hs:
        c = sm.center(h); P = sm.Pat(h); Pi = np.linalg.inv(P); G = sm.Gat(h); t = tolat(h)
        ey = R * np.sqrt(np.diag(Pi)) * pad
        eg = (R * np.sqrt(np.einsum('kj,jl,kl->k', G, Pi, G)) * pad + t * 1.01)
        e = np.zeros(21); e[yidx] = ey * Sy; e[gidx] = eg * Sg
        lo = np.minimum(lo, c - e); hi = np.maximum(hi, c + e)
    lo[1] = ha*65536; hi[1] = hb*65536; lo[0] = -2**40; hi[0] = 2**40; lo[11] = hi[11] = 0
    return np.floor(lo).astype(np.int64), np.ceil(hi).astype(np.int64)
def check(cells, elev=(-65536, 65536)):
    lines = []
    for ha, hb in cells:
        lo, hi = cellbox(ha, hb)
        st = list(lo[:19]) + list(hi[:19]) + [elev[0], elev[1], thrH(int(hb*65536)), thrH(int(ha*65536))]
        lines.append(" ".join(str(int(v)) for v in st))
    out = subprocess.run([EXE, "ivcheck"], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout
    return out.strip().split("\n")
if __name__ == "__main__":
    w = float(sys.argv[1]) if len(sys.argv) > 1 else 50
    cells = [(a, min(a + w, 2640)) for a in np.arange(10, 2640, w)]
    res = check(cells)
    for (ha, hb), r in zip(cells, res):
        flags = [seg.split()[0] for seg in r.split(" | ")]
        ok = all(f == "[1, 1, 1, 1, 1]1" for f in flags)
        if not ok or ha % 500 < w: print(f"{ha:.0f}-{hb:.0f}: {'OK ' if ok else 'BAD'} {flags[-1]} {r.split(' | ')[-1]}")
