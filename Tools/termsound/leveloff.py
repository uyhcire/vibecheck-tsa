"""The user's question: would a level-off at zTop + margin reduce the part above zTop to one level-flight trim?

Flies the candidate level-off (`TsMap.lean` `stepHold`: gc capped by K_HOLD (h_ref - h)) from the reference climb,
finds the level trim as a fixed point of the full frame map (altitude included as a state: no band), and reports
its per-frame and one-second contraction (spectral radius, and the norm in a Lyapunov Q for the one-second map).
"""
import sys
import numpy as np
import scipy.linalg as sl
from tsmap import TsMap, NY, NAMES
from trim import SCALE
from lin import qnorm
import ref as refmod

DT = 1.0 / 128
H_REF = 1000.0          # zTop (934 m) plus a 66 m margin


def say(*a):
    print(*a); sys.stdout.flush()


m = TsMap(); m.smooth(True)
ref = refmod.load()
m.hold(H_REF)
rows = m.sim(700.0, refmod.c_of(ref, 700.0), 128 * 300, 128 * 30)
for r in rows:
    say(f"  t {r[0] / 128:5.0f} s  h {r[3]:8.2f}  V_along {r[4 + 3]:6.2f}  climb {-r[4 + 5]:7.3f}  theta {r[4 + 1]:.4f}")
h, y = rows[-1][3], rows[-1][4:]
SC = np.concatenate([[1.0], SCALE])          # scaled full state (h, y)


def F(xs):
    out = m.step_many_full([x[0] for x in xs], [x[1:] for x in xs])
    return out[:, :1 + NY]


def jac(x, rel=1e-6, side=0.0):
    x = x.copy(); x[1 + NAMES.index("v_rt")] += side
    xs = []
    for j in range(1 + NY):
        for s in (1, -1):
            z = x.copy(); z[j] += s * rel * SC[j]; xs.append(z)
    out = F(xs)
    J = np.empty((1 + NY, 1 + NY))
    for j in range(1 + NY):
        J[:, j] = (out[2 * j] - out[2 * j + 1]) / (2 * rel * SC[j])
    return np.diag(1 / SC) @ J @ np.diag(SC)


x = np.concatenate([[h], y])
for it in range(10):
    r = F([x])[0] - x
    say(f"  newton {it}: max scaled residual {np.max(np.abs(r) / SC):.2e}")
    if np.max(np.abs(r) / SC) < 1e-12:
        break
    J = (jac(x, side=1e-3) + jac(x, side=-1e-3)) / 2
    x = x - np.diag(SC) @ np.linalg.solve(J - np.eye(1 + NY), r / SC)
say(f"level trim: h {x[0]:.3f} m, V_along {x[1 + 3]:.3f} m/s, climb {-x[1 + 5]:.2e} m/s, theta {x[1 + 1]:.4f}, "
    f"phi {x[1]:.5f}, rpm {x[1 + 27]:.1f}")
d = m.diag(x[0], x[1:])
say("  internals:", {k: round(v, 5) for k, v in d.items() if k in ("alpha", "J", "tipMach", "fuel_air", "gc_raw", "n_raw", "acmd_raw", "elev_raw", "sc")})
Ap = jac(x, side=1e-3); Am = jac(x, side=-1e-3); A = (Ap + Am) / 2
ev = np.linalg.eigvals(A); i = np.argsort(-abs(ev))
say("per-frame slowest rates (1/s):", np.round(np.log(ev[i[:8]]) / DT, 4))
rho1 = max(abs(ev)); rhoN = rho1 ** 128
say(f"per-frame spectral radius {rho1:.6f}; one-second {rhoN:.4f}")
AN = np.linalg.matrix_power(A, 128); ApN = np.linalg.matrix_power(Ap, 128); AmN = np.linalg.matrix_power(Am, 128)
fast = [1 + k for k, n in enumerate(NAMES) if n.startswith(('dv0', 'dv1', 'a0', 'a1')) or n.endswith('dot_i') or n in ('udot', 'vdot', 'wdot')]
for mu in (rhoN + 0.02, rhoN + 0.05):
    W = np.eye(1 + NY); W[fast, fast] = 1e-4
    Q = sl.solve_discrete_lyapunov((AN / mu).T, W)
    say(f"  Q_N at mu {mu:.3f}: ||A_N||_Q {qnorm(AN, Q):.4f}  one-sided ||A+^N||_Q {qnorm(ApN, Q):.4f} ||A-^N||_Q {qnorm(AmN, Q):.4f}")
