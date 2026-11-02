"""Design of the straight escape's terminal phase (docs/escape-law-terminal.md).

settle(m, ...) flies the 48 representative starts (150 m; 25/35/45/60 m/s; flight path -0.35/-0.15/0/0.2 rad; bank
0/0.6/1.1 rad) and returns, per start, the first time the state is within the settled box around the law's own
reference climb (|dV| <= 0.5 m/s, |d climb| <= 0.5 m/s, |d phi|, |d psi| <= 0.02 rad, integrators within 0.02) and
stays there for the rest of 60 s, and which box component was last to settle.
"""
import sys
import numpy as np
from tsmap import TsMap, NY, NAMES, GATE
from trim import trim, SCALE

DT = 1.0 / 128
BOX_IDX = [NAMES.index(n) for n in ("v_al", "v_dn", "phi", "dpsi", "ia", "ib", "iphi")]
BOX_TOL = np.array([0.5, 0.5, 0.02, 0.02, 0.02, 0.02, 0.02])
BOX_NAMES = ["V", "climb", "phi", "psi", "ia", "ib", "iphi"]
STARTS = [(v, g, p) for v in (25.0, 35.0, 45.0, 60.0) for g in (-0.35, -0.15, 0.0, 0.2) for p in (0.0, 0.6, 1.1)]


def say(*a):
    print(*a); sys.stdout.flush()


def reference(m, h_lo=10.0, h_hi=1000.0):
    """The law's settled climb: trims y*(h) on a 50 m grid by continuation from a settled run (linear in h between)."""
    r = m.run(0, 0, 300.0, 40.0, 0.0, np.pi / 2, 0, 1, 1, 128 * 90, 128 * 90)
    h0, y0 = r[-1][4], r[-1][5:]
    y, _ = trim(m, h0, y0)
    hs = np.arange(h_lo, h_hi + 1, 50.0)
    out = {}
    yc = y
    for h in sorted(hs, key=lambda x: abs(x - h0)):
        near = min(out, key=lambda k: abs(k - h)) if out else None
        yc, res = trim(m, h, out[near] if near is not None else y)
        out[h] = yc
    H = np.array(sorted(out)); Y = np.array([out[h] for h in H])
    return H, Y


def c_at(ref, h):
    H, Y = ref
    return np.array([np.interp(h, H, Y[:, j]) for j in range(NY)])


def settle(m, ref, z0=150.0, n_s=60):
    res = []
    for v0, g0, ph in STARTS:
        rows = m.run(0, 0, z0, v0, g0, np.pi / 2, ph, 1, 1, 128 * n_s, 4)
        ok = []
        for row in rows:
            if row[1] == 0 or not (ref[0][0] <= row[4] <= ref[0][-1]):
                ok.append(np.full(len(BOX_IDX), np.inf)); continue
            ok.append(np.abs(row[5:] - c_at(ref, row[4]))[BOX_IDX] / BOX_TOL)
        ok = np.array(ok)
        inside = np.all(ok <= 1, axis=1)
        # first index after which it stays inside
        t_in = None
        if inside[-1]:
            k = len(inside) - 1
            while k > 0 and inside[k - 1]:
                k -= 1
            t_in = rows[k][0] * DT
        last = None
        if t_in is not None:
            per = []
            for j in range(len(BOX_IDX)):
                kk = len(inside) - 1
                while kk > 0 and ok[kk - 1, j] <= 1:
                    kk -= 1
                per.append(rows[kk][0] * DT)
            last = BOX_NAMES[int(np.argmax(per))]
        res.append((v0, g0, ph, t_in, last, float(rows[:, 4].min())))
    return res


def stats(res):
    t = np.array([r[3] if r[3] is not None else np.inf for r in res])
    from collections import Counter
    return dict(median=float(np.median(t)), p90=float(np.percentile(t, 90)), max=float(t.max()),
                within16=int(np.sum(t <= 16)), n=len(t), last=Counter(r[4] for r in res).most_common(4),
                min_h=min(r[5] for r in res))


if __name__ == "__main__":
    m = TsMap(); m.smooth(True)
    m.gate()
    ref = reference(m)
    say("gate law:", stats(settle(m, ref)))
