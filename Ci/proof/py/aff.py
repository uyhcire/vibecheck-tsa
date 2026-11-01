"""Affine-arithmetic feasibility: enclose one tick over the piece of T at a fixed altitude and compare the enclosure's
remainder with the contraction margin."""
import numpy as np, sys, subprocess, kinv
from kinv import *
SAFE = float(os.environ.get("SAFE", "1.25"))
def run(h0, frac=1.0):
    c = center(h0); P = Pat(h0); r = rat(h0) * frac
    L = np.linalg.cholesky(P); Bs = r * np.linalg.inv(L.T)          # y = Bs eps_slow, eps in the box covers the ball
    G = Gat(h0); k = kat(h0); tk = tkat(h0) * SAFE * frac; tp = tpat(h0) * SAFE * frac
    rows = np.zeros((21, 18))
    for a, i in enumerate(yidx): rows[i, :7] = Sy[a] * Bs[a]
    for b, i in enumerate(gidx):
        if i == 20: continue
        rows[i, :7] = Sg[b] * (G[b] @ Bs); rows[i, 7] = Sg[b] * k[b] * tk; rows[i, 8 + b] = Sg[b] * tp[b]
    cen = c.copy(); cen[0] = 0; cen[1] = h0 * 65536; cen[11] = 0
    inp = " ".join(str(int(round(v))) for v in cen) + "\n" + "\n".join(" ".join(str(int(round(v * 1000))) for v in row) for row in rows) + "\n"
    out = subprocess.run([EXE, "aff"], input=inp, capture_output=True, text=True, check=True).stdout.strip().split("\n")
    parse = lambda l: (lambda w: (float(w[0]), float(w[1]), np.array([float(v) for v in w[2:]])))(l.split())
    el = parse(out[0].split(" ", 1)[1]); F = [parse(l) for l in out[1:20]]; eI = parse(out[20])
    # slow coordinates at the image, recentred at h' (centre linearised in h)
    hc, he, ha = F[1]; h1 = hc / 65536
    dc = (center(h1 + 0.5) - center(h1 - 0.5))      # raw per metre
    c1 = center(h1)
    y0 = np.zeros(7); M = np.zeros((7, 18)); err = np.zeros(7)
    for a, i in enumerate(yidx):
        fc, fe, fa = (eI if i == 19 else F[i])
        # field' − c(h') = (fc − c1) + fa·eps − dc·(ha·eps)/65536
        y0[a] = (fc - c1[i]) / Sy[a]
        M[a] = (fa - dc[i] * ha / 65536) / Sy[a]
        err[a] = (fe + abs(dc[i]) * he / 65536) / Sy[a]
    P1 = Pat(h1); L1 = np.linalg.cholesky(P1); r1 = rat(h1)
    Ms = L1.T @ M[:, :7]                              # slow part, in the P' norm
    lin = np.linalg.norm(Ms, 2)                          # image of the unit eps-ball, in the P' norm
    fastgain = np.abs(L1.T @ M[:, 7:]).sum(axis=1)       # box of fast noise
    rem = np.linalg.norm(L1.T @ y0) + np.linalg.norm(np.abs(L1.T) @ err) + np.linalg.norm(fastgain)
    r1 = r1 * frac   # report relative to the piece's own radius
    return dict(h=h0, lin_over_r=lin / (r1 * frac), rem_over_r=rem / r1, total=(lin + rem) / r1, elev_err=el[1], y0=np.linalg.norm(L1.T @ y0) / r1,
                err=np.linalg.norm(np.abs(L1.T) @ err) / r1, fast=np.linalg.norm(fastgain) / r1)
if __name__ == "__main__":
    for fr in [1.0, 0.3, 0.1, 0.03, 0.01]:
      for h in [1000, 2600]:
        d = run(h, fr)
        print(f"frac {fr} h {h}: linear gain {d['lin_over_r']:.4f}, remainder {d['rem_over_r']:.4f} (offset {d['y0']:.4f}, AA error {d['err']:.4f}, fast noise {d['fast']:.4f}), total {d['total']:.4f}, elev err {d['elev_err']:.0f}")
