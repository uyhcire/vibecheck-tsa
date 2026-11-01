"""Tightest per-commit-state parameters of three envelope clause forms, and the altitude bound each implies.

A: per-tick Cartesian (Envelope/, 2D): delay K ticks with per-tick vz drop d, then per-tick pull a.
B: commit-referenced Cartesian (Envelope3D/): vz_k >= vz0 - D for k <= K, then vz0 - D + a (k - K) dt.
C: commit-referenced path coordinates: gam_k >= gam0 - dg for k <= K, then the schedule
   G' = G + dt g (nmin - cos G) / Vhi; vertical-speed bound Vhi sin G while G < 0.
Bounds count altitude lost until the schedule reaches vz >= 0 (form A/B) or G >= 0 (form C).
"""
import math
import sys
import numpy as np
import pandas as pd

DT, G = 1 / 16, 9.80665


def loss_from_vz(sig):
    """Altitude lost by a vertical-speed lower-bound sequence sig[0..] (trapezoid of the min, as Box.adv)."""
    h, worst = 0.0, 0.0
    for a, b in zip(sig[:-1], sig[1:]):
        h += DT * min(a, b)
        worst = min(worst, h)
        if a >= 0 and b >= 0:
            break
    return -worst


def form_a(vz, kmax=40):
    best = (1e9, None)
    for K in range(0, kmax):
        d = max([vz[k] - vz[k + 1] for k in range(K)], default=0.0)
        d = max(d, 0.0)
        rest = [(vz[k + 1] - vz[k]) / DT for k in range(K, len(vz) - 1) if vz[k + 1] < 0]
        a = min(rest, default=10.0)
        if a <= 0:
            continue
        sig = [vz[0] - d * k for k in range(K + 1)]
        while sig[-1] < 0:
            sig.append(sig[-1] + a * DT)
        sig.append(sig[-1])
        L = loss_from_vz(sig)
        if L < best[0]:
            best = (L, (K, d, a))
    return best


def form_b(vz, kmax=40):
    best = (1e9, None)
    for K in range(0, kmax):
        D = max(0.0, vz[0] - min(vz[1:K + 2]))
        s0 = vz[0] - D
        a = 50.0
        for k in range(K + 1, len(vz)):
            if s0 + a * (k - K) * DT >= 0:
                break
            a = min(a, (vz[k] - s0) / ((k - K) * DT))
        if a <= 0:
            continue
        sig = [s0] * (K + 1)
        while sig[-1] < 0:
            sig.append(sig[-1] + a * DT)
        sig.append(sig[-1])
        L = loss_from_vz([vz[0]] + sig[1:])
        if L < best[0]:
            best = (L, (K, D, a))
    return best


def sched_c(g0, K, nmin, Vhi):
    G0 = g0
    out = [G0] * (K + 1)
    while out[-1] < 0 and len(out) < 4000:
        Gk = out[-1]
        out.append(Gk + DT * G * (nmin - math.cos(Gk)) / Vhi)
    return out


def form_c(gam, V, kmax=40):
    best = (1e9, None)
    idx0 = next((i for i in range(1, len(gam)) if gam[i] >= 0 and gam[i - 1] >= 0), len(gam) - 1)
    Vhi = max(V[:idx0 + 1])
    for K in range(0, kmax):
        dg = max(0.0, gam[0] - min(gam[1:K + 2]))
        s0 = gam[0] - dg
        lo, hi = 0.5, 6.0
        for _ in range(40):
            mid = (lo + hi) / 2
            sc = sched_c(s0, K, mid, Vhi)
            ok = all(gam[k] >= sc[k] - 1e-9 for k in range(1, min(len(sc), len(gam))))
            lo, hi = (mid, hi) if ok else (lo, mid)
        nmin = lo
        if nmin <= 1.0:
            continue
        sc = sched_c(s0, K, nmin, Vhi)
        sig = [Vhi * math.sin(x) for x in sc] + [0.0]
        L = loss_from_vz([V[0] * math.sin(gam[0])] + sig[1:])
        if L < best[0]:
            best = (L, (K, dg, nmin, Vhi))
    return best


if __name__ == '__main__':
    d = pd.read_csv(sys.argv[1])
    rows = []
    for tag, r in d.groupby('tag'):
        vz, V, gam = r.vz.values, r.V.values, r.gam.values
        loss = r.h.iloc[0] - r.hmin.iloc[1:].min()
        A, B, C = form_a(vz), form_b(vz), form_c(gam, V)
        rows.append(dict(tag=tag, V0=V[0], g0=gam[0], al0=r.al.iloc[0], q0=r.q.iloc[0], rpm0=r.rpm.iloc[0], loss=loss,
                         HA=A[0], HB=B[0], HC=C[0], pA=A[1], pB=B[1], pC=C[1],
                         Vmin=r.Vmin.min(), almax=r.almax.max(), nmax=r.n.max()))
    out = pd.DataFrame(rows)
    out.to_csv(sys.argv[2], index=False)
    pd.set_option('display.width', 250)
    print(out.round(3).to_string(index=False))
