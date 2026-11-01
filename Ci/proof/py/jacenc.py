"""Interval Jacobian enclosure (unverified prototype) of the real one-tick map over boxes of T, and the P-norm gain
bound it implies: |Lᵀ J L⁻ᵀ| ≤ |Lᵀ Jc L⁻ᵀ| + || |Lᵀ| W |L⁻ᵀ| ||  (Jc, W = centre and radius of the enclosure)."""
import numpy as np, subprocess, kinv, sys
from kinv import *
SAFE = float(os.environ.get("SAFE", "1.25"))
rng = np.random.default_rng(3)
def law_fd(x0, coefs, ylo, yhi, nsamp=8):
    """law elevator and eI' : value range and derivative range w.r.t. y by central differences at sample points"""
    pts = []
    for _ in range(nsamp):
        y = rng.uniform(ylo, yhi)
        base = x0 + coefs @ y
        pts.append(base)
        for i in range(7):
            e = np.zeros(7); e[i] = 0.25
            pts.append(x0 + coefs @ (y + e)); pts.append(x0 + coefs @ (y - e))
    X = np.round(np.array(pts)).astype(np.int64)
    img, *_ = ticks(X)       # not needed for the law, but the probe returns the memory: use memory fields
    return X
def run(h0, frac, cen_y=None):
    c = center(h0); P = Pat(h0); r = rat(h0)
    G = Gat(h0); kk = kat(h0); tk = tkat(h0) * SAFE; tp = tpat(h0) * SAFE
    Pi = np.linalg.inv(P); half = r * np.sqrt(np.diag(Pi)) * frac
    yc = np.zeros(7) if cen_y is None else cen_y
    ylo, yhi = yc - half, yc + half
    coefs = np.zeros((21, 7)); ext = np.zeros(21)
    for a, i in enumerate(yidx): coefs[i, a] = Sy[a]
    for b, i in enumerate(gidx):
        if i == 20: continue
        coefs[i] = Sg[b] * G[b]; ext[i] = Sg[b] * (abs(kk[b]) * tk + tp[b])
    x0 = c.copy(); x0[0] = 0; x0[1] = h0 * 65536; x0[11] = 0
    # law: sample elevator and eI' (and their derivatives) with the probe's realgap-free path: use 'tick' on 1 step
    def lawvals(Y):
        X = np.round(np.array([x0 + coefs @ y for y in Y])).astype(np.int64)
        img, *_ = ticks(X)
        return img[:, 19]   # eI' (memory after the tick)
    # elevator via the T harness is not exposed; approximate its derivative by the eI' / kI relation is wrong, so
    # sample it directly from a one-substep probe: we use eI' only and take the elevator from LawIv-like FD below
    lines = []
    for f in range(19):
        lo = x0[f] + np.minimum(coefs[f] * ylo, coefs[f] * yhi).sum() - ext[f] + (coefs[f] @ yc) * 0
        hi = x0[f] + np.maximum(coefs[f] * ylo, coefs[f] * yhi).sum() + ext[f]
        if f == 1: lo, hi = x0[1], x0[1]
        d = " ".join(f"{int(round(1000 * v))} {int(round(1000 * v))}" for v in coefs[f])
        lines.append(f"{int(round(1000 * lo))} {int(round(1000 * hi))} {d}")
    # elevator: finite differences of the law at sample points
    Ys = [rng.uniform(ylo, yhi) for _ in range(6)]
    Xs = []
    for y in Ys:
        Xs.append(x0 + coefs @ y)
        for i in range(7):
            e = np.zeros(7); e[i] = 0.25; Xs.append(x0 + coefs @ (y + e)); Xs.append(x0 + coefs @ (y - e))
    Xs = np.round(np.array(Xs)).astype(np.int64)
    out = subprocess.run([EXE, "elevof"], input="\n".join(" ".join(str(v) for v in x) for x in Xs) + "\n",
                         capture_output=True, text=True, check=True).stdout.split()
    E = np.array([[float(v) for v in l.split(",")] for l in out])   # elev, eI'
    nb = 15
    vals = E[::nb]; der = []
    for k in range(len(Ys)):
        blk = E[k * nb:(k + 1) * nb]
        der.append([(blk[1 + 2 * i] - blk[2 + 2 * i]) / 0.5 for i in range(7)])
    der = np.array(der)   # samples x 7 x 2
    def enc(v, d, widen=0.2, add=0):
        lo, hi = v.min(), v.max(); w = (hi - lo) * widen + add
        dlo, dhi = d.min(axis=0), d.max(axis=0); dw = (dhi - dlo) * widen + 2
        return lo - w, hi + w, dlo - dw, dhi + dw
    elo, ehi, edlo, edhi = enc(vals[:, 0], der[:, :, 0], add=20)
    lines.append(f"{int(round(1000 * elo))} {int(round(1000 * ehi))} " + " ".join(f"{int(round(1000 * a))} {int(round(1000 * b))}" for a, b in zip(edlo, edhi)))
    ilo, ihi, idlo, idhi = enc(vals[:, 1], der[:, :, 1], add=2)
    thr = int(Ci_thr(h0))
    inp = "\n".join(lines) + f"\n{thr}\n"
    out = subprocess.run([EXE, "jac"], input=inp, capture_output=True, text=True, check=True).stdout.strip().split("\n")
    F = [np.array([float(v) for v in l.split()]) for l in out]
    if os.environ.get('DBG'):
        for nm, f in zip(NAMES, F): print(nm, f[:2], np.abs(f[2:]).max())
    h1 = (F[1][0] + F[1][1]) / 2 / 65536
    dc = center(h1 + 0.5) - center(h1 - 0.5)
    Jlo = np.zeros((7, 7)); Jhi = np.zeros((7, 7))
    for a, i in enumerate(yidx):
        if i == 19:
            Jlo[a], Jhi[a] = idlo / Sy[a], idhi / Sy[a]; continue
        dlo = F[i][2::2]; dhi = F[i][3::2]
        hlo = F[1][2::2]; hhi = F[1][3::2]
        corr = [sorted([dc[i] * hlo[j] / 65536, dc[i] * hhi[j] / 65536]) for j in range(7)]
        Jlo[a] = (dlo - np.array([cc[1] for cc in corr])) / Sy[a]
        Jhi[a] = (dhi - np.array([cc[0] for cc in corr])) / Sy[a]
    Jc = (Jlo + Jhi) / 2; W = (Jhi - Jlo) / 2
    L = np.linalg.cholesky(P); Li = np.linalg.inv(L.T)
    gn = np.linalg.norm(L.T @ Jc @ Li, 2); gd = np.linalg.norm(np.abs(L.T) @ W @ np.abs(Li), 2)
    return gn, gd
def Ci_thr(h):
    hraw = int(h * 65536); d = max(0, hraw - 2500 * 65536)
    return max(0, min(65536, 65536 - d * d // 6553200024))
if __name__ == "__main__":
    for h in [1000, 2600]:
        for frac in [1.0, 0.3, 0.1, 0.03]:
            gn, gd = run(h, frac)
            print(f"h {h} piece {frac}: nominal gain {gn:.4f}, enclosure spread {gd:.4f}, bound {gn + gd:.4f}", flush=True)
