"""Energy-barrier family: P[theta](f) for the level-off loop and its adversarial search (see docs/termsound/barrier.md)."""
import json
import os
import sys
import threading
import numpy as np
from tsmap import TsMap, NAMES
from terminal import NEW

HERE = os.path.dirname(os.path.abspath(__file__))
G0 = 9.80665
ZTOP, EAIR = 934.0, 7.0
FLOOR = ZTOP + EAIR
K_HOLD, H_LEVEL = NEW["kHold"], NEW["hLevel"]
PSI, NORTH = np.pi / 2, 0.0
IV, IVR, IVD, ITH = (NAMES.index(n) for n in ("v_al", "v_rt", "v_dn", "theta"))
TRIM = np.array(json.load(open(os.path.join(HERE, "barrier_trim.json")))["trim"])
HS, YS = TRIM[0], TRIM[1:]
VS = float(np.linalg.norm(YS[[IV, IVR, IVD]]))

AX = ("al", "rt", "dn")
# boxed quantities: chart coordinates, except beta = v_rt / V - dpsi for v_rt and one-frame differences
# da = a1 - a0, ddv = dv1 - dv0 for the integrator histories a1, dv1 (corners of plain boxes are inconsistent)
BOXED = ([n for n in NAMES if n not in ("v_al", "v_dn", "theta", "v_rt") and not n.startswith(("a1_", "dv1_"))]
         + ["beta"] + [f"da_{a}" for a in AX] + [f"ddv_{a}" for a in AX])
FAST0 = dict(phi=0.03, dpsi=0.03, beta=0.01, p_i=0.05, q_i=0.2, r_i=0.05,
             dv0_al=0.04, dv0_rt=0.003, dv0_dn=0.1, ddv_al=0.003, ddv_rt=0.001, ddv_dn=0.01,
             a0_al=4.5, a0_rt=0.3, a0_dn=12.0, da_al=0.3, da_rt=0.1, da_dn=1.0,
             pdot_i=0.08, qdot_i=1.0, rdot_i=0.06, udot=4.0, vdot=1.3, wdot=10.0,
             rpm=70.0, map=1500.0, ia=0.08, ib=0.015, iphi=0.03)

THETA0 = dict(k=128, w1=0.5, wl=0.15, wq=0.03, b=946.0, Delta=30.0, eps=25.0,
              uV=1.0, ul=0.15, uq=0.08, u_hi=1065.0,
              V_lo=50.0, V_hi=86.0, gam_lo=-0.4, gam_hi=0.4, dalpha=0.12, fast=FAST0)


def speed_vz(y):
    return float(np.linalg.norm(y[[IV, IVR, IVD]])), float(-y[IVD])


def B(th, h, y):
    """Lower barrier: altitude (capped at hB) less penalties for descending and for flying slower than V* (the latter
    scaled down to 0 over the L metres below H_LEVEL if L is set); B <= h."""
    V, vz = speed_vz(y)
    vd = max(-vz, 0.0)
    sched = 1.0 if th.get("L") is None else min(max((H_LEVEL - h) / th["L"], 0.0), 1.0)
    return min(h, th.get("hB", np.inf)) - sched * th["w1"] * max(VS * VS - V * V, 0.0) / (2 * G0) - th["wl"] * vd - th["wq"] * vd * vd


def U(th, h, y):
    """Upper barrier: altitude (raised to hU if set) plus bonuses for flying faster than V* and for climbing (if hU
    is unset, only for climbing faster than the level-off command V K_HOLD (H_LEVEL - h)); U >= h."""
    V, vz = speed_vz(y)
    vu = max(min(vz, vz - V * K_HOLD * (H_LEVEL - h)), 0.0) if th.get("hU") is None else max(vz, 0.0)
    return max(h, th.get("hU") or -np.inf) + th["uV"] * max(V * V - VS * VS, 0.0) / (2 * G0) + th["ul"] * vu + th["uq"] * vu * vu


def qvals(y):
    """The boxed quantities of chart y (dict)."""
    V, _ = speed_vz(y)
    q = {n: y[NAMES.index(n)] for n in BOXED if n in NAMES}
    q["beta"] = y[IVR] / V - y[NAMES.index("dpsi")]
    for a in AX:
        q[f"da_{a}"] = y[NAMES.index(f"a1_{a}")] - y[NAMES.index(f"a0_{a}")]
        q[f"ddv_{a}"] = y[NAMES.index(f"dv1_{a}")] - y[NAMES.index(f"dv0_{a}")]
    return q


Q_TRIM = qvals(YS)


def dalpha(y):
    V, vz = speed_vz(y)
    return y[ITH] - YS[ITH] - np.arcsin(vz / V)


def excursion(th, h, y):
    """R's constraints as normalised values, each <= 1 inside R (dict)."""
    V, vz = speed_vz(y)
    q = qvals(y)
    out = {n: abs(q[n] - Q_TRIM[n]) / w for n, w in th["fast"].items()}
    out["dalpha"] = abs(dalpha(y)) / th["dalpha"]
    mid, half = (th["V_hi"] + th["V_lo"]) / 2, (th["V_hi"] - th["V_lo"]) / 2
    out["V"] = abs(V - mid) / half
    mid, half = (th["gam_hi"] + th["gam_lo"]) / 2, (th["gam_hi"] - th["gam_lo"]) / 2
    out["gamma"] = abs(np.arcsin(vz / V) - mid) / half
    out["U"] = 1.0 + (U(th, h, y) - th["u_hi"]) / 10.0
    return out


NDIM = 3 + len(BOXED) + 1


def decode(th, u, band=None):
    """u in [0,1]^NDIM -> (h, y). band=None: h in [h(B = b), h(U = u_hi)]; band=Delta: h in [h(B = b), h(B = b + Delta)]."""
    u = np.clip(u, 0.0, 1.0)
    y = YS.copy()
    V = th["V_lo"] + u[0] * (th["V_hi"] - th["V_lo"])
    vz = V * np.sin(th["gam_lo"] + u[1] * (th["gam_hi"] - th["gam_lo"]))
    q = {n: Q_TRIM[n] + (2 * u[3 + j] - 1) * th["fast"].get(n, 0.0) for j, n in enumerate(BOXED)}
    for n in BOXED:
        if n in NAMES:
            y[NAMES.index(n)] = q[n]
    for a in AX:
        y[NAMES.index(f"a1_{a}")] = q[f"a0_{a}"] + q[f"da_{a}"]
        y[NAMES.index(f"dv1_{a}")] = q[f"dv0_{a}"] + q[f"ddv_{a}"]
    y[IVR] = V * (q["dpsi"] + q["beta"])
    y[IVD] = -vz
    y[IV] = np.sqrt(max(V * V - vz * vz - y[IVR] ** 2, 1.0))
    y[ITH] = YS[ITH] + np.arcsin(vz / V) + (2 * u[2] - 1) * th["dalpha"]
    if th.get("L") is None:
        off = B(dict(th, hB=np.inf), 0.0, y)
        h_lo = th["b"] - off
    else:
        lo_, hi_ = th["b"], th["u_hi"] + 200.0
        for _ in range(50):
            mid = 0.5 * (lo_ + hi_)
            lo_, hi_ = (lo_, mid) if B(dict(th, hB=np.inf), mid, y) >= th["b"] else (mid, hi_)
        h_lo, off = hi_, th["b"] - hi_
    if h_lo > th.get("hB", np.inf):
        return None
    lo, hi = h_lo, th["u_hi"]
    if U(th, lo, y) > th["u_hi"]:
        return None
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        lo, hi = (mid, hi) if U(th, mid, y) <= th["u_hi"] else (lo, mid)
    h_hi = lo
    if band is not None and th.get("L") is not None:
        lo_, hi_ = h_lo, h_hi
        for _ in range(50):
            mid = 0.5 * (lo_ + hi_)
            lo_, hi_ = (mid, hi_) if B(th, mid, y) <= th["b"] + band else (lo_, mid)
        h_hi = lo_
    elif band is not None and th["b"] + band - off < th.get("hB", np.inf):
        h_hi = min(h_hi, th["b"] + band - off)
    if h_hi < h_lo:
        return None
    return h_lo + u[-1] * (h_hi - h_lo), y


class Pool:
    def __init__(self, n=4):
        self.ms = []
        for _ in range(n):
            m = TsMap(); m.cand(**NEW); self.ms.append(m)

    def roll(self, states, k):
        """For each (h, y): (h_k, y_k, min_{1<=j<=k} h_j). None states give None."""
        out = [None] * len(states)
        idx = [i for i, s in enumerate(states) if s is not None]
        chunks = [idx[j::len(self.ms)] for j in range(len(self.ms))]

        def work(m, ids):
            for i in ids:
                h, y = states[i]
                rows = m.sim(h, y, k, 1, PSI, NORTH)
                out[i] = (rows[-1][3], np.array(rows[-1][4:]), float(rows[1:, 3].min()))
        ts = [threading.Thread(target=work, args=(m, c)) for m, c in zip(self.ms, chunks)]
        [t.start() for t in ts]; [t.join() for t in ts]
        return out

    def close(self):
        for m in self.ms:
            m.close()


def margins(th, s, r):
    """Margins of one start (h, y) and its roll result; each >= 0 where the condition holds, except drop (eps needed)."""
    h, y = s
    hk, yk, hmin = r
    ex = excursion(th, hk, yk)
    worst = max(ex, key=ex.get)
    return dict(c1=B(th, hk, yk) - th["b"], drop=B(th, h, y) - B(th, hk, yk), c2=1 - ex[worst], c2_which=worst,
                c3=hmin - FLOOR, ex=ex)


def c4_margin(th):
    return th["b"] - FLOOR


def say(*a):
    print(*a); sys.stdout.flush()
