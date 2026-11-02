"""The redesigned terminal phase of the straight escape (docs/escape-law-terminal.md): trims, table segments,
contraction across the climb band and at the level-off trim, and settling statistics, old law against new.

`NEW` is the candidate (`TsMap.lean` `Cand`): speed term in equivalent airspeed with reference 35.2 m/s, KV 0.06,
KI_A 6, GC_LO 0, GC_HI 0.5 once past the pull-up, and the level-off at 1,000 m (K_HOLD 0.005).
"""
import sys
import numpy as np
import scipy.linalg as sl
from tsmap import TsMap, NY, NAMES
from trim import trim, jacobian, SCALE
from lin import qnorm
from design import reference, settle, stats, c_at, STARTS
from regime import seg

DT = 1.0 / 128
NEW = dict(vRefE=35.2, kv=0.06, kiA=6.0, gcLo=0.0, gcHi=0.5, hLevel=1000.0, kHold=0.005)
CLIMB_ONLY = dict(NEW, hLevel=float("nan"))
FAST = [k for k, n in enumerate(NAMES) if n.startswith(('dv0', 'dv1', 'a0', 'a1')) or n.endswith('dot_i') or n in ('udot', 'vdot', 'wdot')]


def say(*a):
    print(*a); sys.stdout.flush()


def sided(m, h, y):
    off = np.zeros(NY); off[NAMES.index("v_rt")] = 1e-3
    D, Di = np.diag(SCALE), np.diag(1 / SCALE)
    return [Di @ jacobian(m, h, y + s * off, 1e-6) @ D for s in (1, -1)]


if __name__ == "__main__":
    m = TsMap(); m.smooth(True)
    keys = m.keys()
    # ---- trims and segments over the climb band (climb law without the level-off: the band is below it)
    m.cand(**CLIMB_ONLY)
    ref = reference(m, 10.0, 1000.0)
    say("== trims of the new climb (10-1000 m) ==")
    segs_seen = set(); amin, amax = 1, 0
    for h in np.arange(10.0, 1001.0, 10.0):
        d = m.diag(h, c_at(ref, h))
        s = (seg(keys["CLwbh"], d["alpha"]), seg(keys["CDwbh"], d["alpha"]), seg(keys["cThrust"], d["J"]),
             seg(keys["mixEff"], d["fuel_air"]), seg(keys["CtMach"], d["tipMach"]))
        segs_seen.add(s); amin = min(amin, d["alpha"]); amax = max(amax, d["alpha"])
        if h in (10.0, 250.0, 500.0, 750.0, 934.0, 1000.0) or abs(h - 930) < 1:
            y = c_at(ref, h)
            say(f"  h {h:5.0f}: V {np.hypot(y[3], y[4]):.3f} climb {-y[5]:.3f} gradient {-y[5] / y[3]:.4f} alpha {d['alpha']:.5f}"
                f" J {d['J']:.4f} f/a {d['fuel_air']:.5f} tipM {d['tipMach']:.4f} gc_raw-free")
    say(f"  alpha range {amin:.5f}..{amax:.5f}; margins to CD breakpoints 0.0698/0.0873: {amin - 0.0698:.4f}, {0.0873 - amax:.4f};"
        f" segment tuples seen (CL, CD, J, mixEff, CtMach): {sorted(segs_seen)}")
    # ---- contraction across the band
    say("== contraction across the band ==")
    grid = [10.0, 150.0, 300.0, 450.0, 600.0, 750.0, 900.0, 1000.0]
    J = {}
    for h in grid:
        y, _ = trim(m, h, c_at(ref, h))
        J[h] = sided(m, h, y)
        r1 = max(max(abs(np.linalg.eigvals(A))) for A in J[h])
        say(f"  h {h:5.0f}: per-frame rho {r1:.6f} (slowest {-np.log(r1) / DT:.4f}/s), one-second {r1 ** 128:.4f}")
    A0 = (J[450.0][0] + J[450.0][1]) / 2
    AN = np.linalg.matrix_power(A0, 128)
    W = np.eye(NY); W[FAST, FAST] = 1e-4
    best = None
    for mu in (0.85, 0.88, 0.9, 0.92):
        Q = sl.solve_discrete_lyapunov((AN / mu).T, W)
        worst = max(qnorm(np.linalg.matrix_power(A, 128), Q) for h in grid for A in J[h])
        say(f"  Q_N from 450 m, mu {mu}: max over band and both beta pieces of ||A^128||_QN = {worst:.4f}")
        best = worst if best is None else min(best, worst)
    # ---- level-off trim
    say("== level-off trim (new law with the level-off) ==")
    m.cand(**NEW)
    rows = m.sim(900.0, c_at(ref, 900.0), 128 * 240, 128 * 240)
    x = np.concatenate([[rows[-1][3]], rows[-1][4:]])
    SC = np.concatenate([[1.0], SCALE])
    def F(xs):
        return m.step_many_full([v[0] for v in xs], [v[1:] for v in xs])[:, :1 + NY]
    def jfull(x, side):
        x = x.copy(); x[1 + NAMES.index("v_rt")] += side
        xs = []
        for j in range(1 + NY):
            for s in (1, -1):
                z = x.copy(); z[j] += s * 1e-6 * SC[j]; xs.append(z)
        out = F(xs)
        Jf = np.array([(out[2 * j] - out[2 * j + 1]) / (2e-6 * SC[j]) for j in range(1 + NY)]).T
        return np.diag(1 / SC) @ Jf @ np.diag(SC)
    for it in range(8):
        r = F([x])[0] - x
        if np.max(np.abs(r) / SC) < 1e-9: break
        Jm = (jfull(x, 1e-3) + jfull(x, -1e-3)) / 2
        x = x - np.diag(SC) @ np.linalg.solve(Jm - np.eye(1 + NY), r / SC)
    d = m.diag(x[0], x[1:])
    Jp, Jn = jfull(x, 1e-3), jfull(x, -1e-3)
    r1 = max(max(abs(np.linalg.eigvals(A))) for A in (Jp, Jn))
    say(f"  level trim h {x[0]:.2f} V {x[4]:.2f} alpha {d['alpha']:.5f} (CL seg {seg(keys['CLwbh'], d['alpha'])}, CD seg "
        f"{seg(keys['CDwbh'], d['alpha'])}) tipMach {d['tipMach']:.4f} J {d['J']:.4f}; per-frame rho {r1:.6f}, one-second {r1 ** 128:.4f}")
    # ---- settling, old against new
    say("== settling from the 48 starts ==")
    m.gate(); refg = reference(m)
    so = settle(m, refg)
    m.cand(**CLIMB_ONLY)
    sn = settle(m, ref)
    say("  gate law:", stats(so))
    say("  new law: ", stats(sn))
    for v0 in (25.0, 35.0, 45.0, 60.0):
        to = [r[3] for r in so if r[0] == v0]; tn = [r[3] for r in sn if r[0] == v0]
        say(f"  starts at {v0:.0f} m/s: gate median {np.median(to):.1f} s max {max(to):.1f}; new median {np.median(tn):.1f} s max {max(tn):.1f}")
