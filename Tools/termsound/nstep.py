"""Sampled contraction of the one-second map (N = 128 frames) in a quadratic norm Q_N.

Per-frame quadratic contraction fails (cert.py C2: no common Q found with margin; the per-frame margin is about
1e-3 and the trim sits on the |beta| kink). Over one second the slow modes contract by about 0.87 and the kink is
averaged, so this script tests E_N(xi) = chart after N frames minus c(h_N), from y = c(h) + xi.
Q_N solves (A_N/mu)^T Q (A_N/mu) - Q = -W with A_N = A0^N (A0: average of the one-sided frame Jacobians at 600 m).
"""
import pickle, sys, time
import numpy as np
from tsmap import TsMap, NY, NAMES
from trim import SCALE
from lin import lyap_q, qnorm
import ref as refmod

N = 128
ref = refmod.load()
LIN = pickle.load(open("/tmp/ts_LIN.pkl", "rb"))
m = TsMap(); m.smooth(True)


def c_of(h):
    return refmod.c_of(ref, h)


def EN(h, zs):
    c = c_of(h)
    out = m.stepn_many([h] * len(zs), [c + SCALE * z for z in zs], N)
    hn = out[:, 2]
    return (out[:, 3:] - np.array([c_of(x) for x in hn])) / SCALE, hn, out[:, 0], out[:, 1]


def say(*a):
    print(*a); sys.stdout.flush()


if __name__ == "__main__":
    fast = [i for i, n in enumerate(NAMES) if n.startswith(('dv0', 'dv1', 'a0', 'a1')) or n.endswith('dot_i') or n in ('udot', 'vdot', 'wdot')]
    AN = np.linalg.matrix_power(LIN[600.0]["A0"], N)
    res = {}
    for eps in (1.0, 1e-4):
        W = np.eye(NY); W[fast, fast] = eps
        QN = lyap_q(AN, 0.92, W)
        QN /= np.max(np.linalg.eigvalsh(QN))
        say(f"eps {eps}: ||A_N||_QN {qnorm(AN, QN):.4f}, max over h of ||A0(h)^N||_QN "
            f"{max(qnorm(np.linalg.matrix_power(L['A0'], N), QN) for L in LIN.values()):.4f}, cond {np.linalg.cond(QN):.2e}")
        LTi = np.linalg.inv(np.linalg.cholesky(QN).T)
        qn = lambda z: float(np.sqrt(z @ QN @ z))
        rng = np.random.default_rng(7)
        dirs = []
        for _ in range(40):
            w = rng.normal(size=NY); w /= np.linalg.norm(w); dirs.append(LTi @ w)
        for i in range(NY):
            e = np.zeros(NY); e[i] = 1; dirs.append(e / qn(e))
        dirs += [-d for d in dirs]
        for h in (10.0, 450.0, 900.0):
            e0, _, _, _ = EN(h, [np.zeros(NY)])
            for r in (1.0, 10.0, 100.0, 1000.0):
                t0 = time.time()
                e, hn, _, _ = EN(h, [r * d for d in dirs])
                ratio = max(qn(x - e0[0]) for x in e) / r
                inv = max(qn(x) for x in e) / r
                res[(eps, h, r)] = (ratio, inv, qn(e0[0]))
                say(f"  h {h:5.0f} r {r:7.1f}: max ||E_N(xi)-E_N(0)||/r {ratio:.4f}; max ||E_N(xi)||/r {inv:.4f};"
                    f" ||E_N(0)|| {qn(e0[0]):.2e}  ({time.time()-t0:.0f}s)")
        Qi = np.linalg.inv(QN)
        say("  half-widths of {||xi||_QN <= 1}:", {NAMES[i]: float(np.sqrt(Qi[i, i]) * SCALE[i]) for i in (0, 1, 2, 3, 4, 5, 7, 27, 29, 30, 31)})
        pickle.dump(dict(QN=QN, eps=eps), open(f"/tmp/ts_QN_{eps}.pkl", "wb"))
    pickle.dump(res, open("/tmp/ts_nstep.pkl", "wb"))
