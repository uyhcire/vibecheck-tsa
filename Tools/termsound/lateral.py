"""Why the level-off's lateral motion settles slowly, and a proposed stiffer lateral hold (issue #58).

At the level trim (east, latitude 0) under the terminal law, with the gate's lateral gains and with candidate
gains (harness `Cand`: heading gain kpsi, roll gains kphi and kp, roll integrator kiPhi), this computes the frame
map's central-difference Jacobian (which averages the |beta| kink), its slow modes, and which chart coordinates
each mode lives in; and it flies lateral upsets (bank, heading and sideslip offsets) to measure settling.
"""
import sys, json
import numpy as np
from tsmap import TsMap, NAMES, NY
from terminal import NEW
from trim import SCALE

DT = 1.0 / 128
PSI, NORTH = np.pi / 2, 0.0
SC = np.concatenate([[1.0], SCALE])
LAT = [NAMES.index(n) for n in ("phi", "dpsi", "v_rt", "p_i", "r_i", "ib", "iphi")]


def say(*a):
    print(*a); sys.stdout.flush()


def F(m, xs):
    return m.step_many_full([x[0] for x in xs], [x[1:] for x in xs], PSI, NORTH)[:, :1 + NY]


def jac(m, x, rel=1e-5):
    xs = []
    for j in range(1 + NY):
        for s in (1, -1):
            z = x.copy(); z[j] += s * rel * SC[j]; xs.append(z)
    out = F(m, xs)
    J = np.array([(out[2 * j] - out[2 * j + 1]) / (2 * rel * SC[j]) for j in range(1 + NY)]).T
    return np.diag(1 / SC) @ J @ np.diag(SC)


def level_trim(m, x):
    for _ in range(10):
        r = F(m, [x])[0] - x
        if np.max(np.abs(r) / SC) < 1e-10:
            break
        x = x - np.diag(SC) @ np.linalg.solve(jac(m, x) - np.eye(1 + NY), r / SC)
    return x


def analyse(m, gains, x0):
    m.cand(**dict(NEW, **gains))
    rows = m.sim(x0[0], x0[1:], 128 * 120, 128 * 120, PSI, NORTH)
    x = level_trim(m, np.concatenate([[rows[-1][3]], rows[-1][4:]]))
    A = jac(m, x)
    ev, V = np.linalg.eig(A)
    rate = -np.log(np.abs(ev)) / DT
    order = np.argsort(rate)
    modes = []
    for i in order[:8]:
        w = np.abs(V[:, i]); w /= w.max()
        latw = sum(w[1 + j] for j in LAT) / sum(w)
        modes.append((rate[i], abs(np.angle(ev[i])) / DT, latw, [(["h"] + NAMES)[k] for k in np.argsort(-w)[:3]]))
    # lateral upset: 3 deg bank, 3 deg heading, 1 m/s sideslip; time until |phi|, |dpsi| < 0.2 deg and |v_rt - v_rt*| < 0.1
    y = x[1:].copy()
    y[NAMES.index("phi")] += np.radians(3); y[NAMES.index("dpsi")] += np.radians(3); y[NAMES.index("v_rt")] += 1.0
    rows = m.sim(x[0], y, 128 * 60, 8, PSI, NORTH)
    t_set, peak = None, 0.0
    for rw in rows:
        dev = np.abs(rw[4:] - x[1:])
        peak = max(peak, abs(rw[4 + NAMES.index("phi")] - x[1 + NAMES.index("phi")]))
        ok = dev[NAMES.index("phi")] < np.radians(0.2) and dev[NAMES.index("dpsi")] < np.radians(0.2) and dev[NAMES.index("v_rt")] < 0.1
        if ok and t_set is None:
            t_set = rw[0] * DT
        elif not ok:
            t_set = None
    cross = float(np.sum(rows[:, 4 + NAMES.index("v_rt")] - x[1 + NAMES.index("v_rt")]) * 8 * DT)
    return x, modes, t_set, np.degrees(peak), cross


if __name__ == "__main__":
    m = TsMap(); m.smooth(True)
    x0 = np.array(json.load(open("/tmp/ts_level_cert2.json"))["east"]["trim"])
    variants = [("gate (KPSI 1, KPHI 2.5, KP 0.8, KI_PHI 1)", {}),
                ("kpsi 2", dict(kpsi=2.0)),
                ("kpsi 2, kiPhi 2", dict(kpsi=2.0, kiPhi=2.0)),
                ("kpsi 3, kphi 4, kp 1.2", dict(kpsi=3.0, kphi=4.0, kp=1.2)),
                ("kpsi 2, kphi 4, kp 1.2, kiPhi 2", dict(kpsi=2.0, kphi=4.0, kp=1.2, kiPhi=2.0)),
                ("PROPOSED: KPSI scaled by max(1, V/35.2)", dict(kpsiV=35.2))]
    out = {}
    for name, g in variants:
        x, modes, ts, peak, cross = analyse(m, g, x0)
        say(f"== {name}: level trim h {x[0]:.3f} V {x[4]:.3f} phi* {np.degrees(x[1]):.3f} deg")
        for rt, om, lw, top in modes:
            say(f"   mode: rate {rt:.4f}/s, freq {om:.3f} rad/s, lateral share {lw:.2f}, top {top}")
        say(f"   upset (3 deg bank, 3 deg heading, 1 m/s sideslip): settled (0.2 deg, 0.1 m/s) at {ts} s; peak bank "
            f"{peak:.2f} deg; cross-track displacement {cross:.1f} m")
        out[name] = dict(gains=g, modes=[m_[:3] for m_ in modes], settle=ts, peak_bank=peak, cross=cross)
    json.dump(out, open("/tmp/ts_lateral.json", "w"), indent=1, default=float)
