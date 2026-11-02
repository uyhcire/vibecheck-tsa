"""Linearisation, kink and disturbance numbers for the straight climb (docs/termsound-proof.tex, section 5).

Run by `make certify` after `ref.py`. Prints, in order: C1 the one-sided frame Jacobians of the error map at the
reference climb (the trim sits on the |beta| kink), the rank of the jump and the small-gain margin of the kink;
C2 the best common per-frame quadratic norm found (it does not contract: lambda > 1); C3 the disturbances (altitude
drift of the reference, heading and latitude, the hidden quaternion norm). Results go to /tmp/ts_cert.json.
"""
import json
import pickle
import sys
import time

import numpy as np

from tsmap import TsMap, NY, NAMES
from trim import SCALE
from lin import lyap_q, qnorm
import ref as refmod

DT = 1.0 / 128
H_BAND = (10.0, 1000.0)          # certified altitude band (m); release altitude zTop = 934 m lies inside
H_GRID = [10.0, 150.0, 300.0, 450.0, 600.0, 750.0, 900.0, 1000.0]
H_REF = 600.0
MU = 0.999                       # Lyapunov rate for Q
SIDE = NAMES.index("v_rt")
OFF = 1e-3                       # one-sided offset in v_rt (m/s): beta ~ 3e-5 rad
FD_REL = 1e-6
TH_RAY = None                    # ray direction relative to the held track (rad), set from the reference
OUT = {}


def say(*a):
    print(*a)
    sys.stdout.flush()


m = TsMap()
m.smooth(True)
ref = refmod.load()
Ds, Di = np.diag(SCALE), np.diag(1 / SCALE)


def c_of(h):
    return refmod.c_of(ref, h)


def E_many(h, xis, psi=0.0, north=0.0):
    """Error map in scaled coordinates: z -> (y' - c(h'))/SCALE with y = c(h) + SCALE z; also h', east, north."""
    c = c_of(h)
    out = m.step_many_full([h] * len(xis), [c + SCALE * z for z in xis], psi, north)
    hp = out[:, 0]
    yp = out[:, 1:1 + NY]
    cs = np.array([c_of(x) for x in hp])
    return (yp - cs) / SCALE, hp, out[:, 1 + NY], out[:, 2 + NY]


def jac_E(h, z0, rel=FD_REL):
    xs = []
    for j in range(NY):
        for s in (1, -1):
            z = z0.copy(); z[j] += s * rel
            xs.append(z)
    e, hp, ea, no = E_many(h, xs)
    J = np.empty((NY, NY)); gh = np.empty(NY); ge = np.empty(NY); gn = np.empty(NY)
    for j in range(NY):
        J[:, j] = (e[2 * j] - e[2 * j + 1]) / (2 * rel)
        gh[j] = (hp[2 * j] - hp[2 * j + 1]) / (2 * rel)
        ge[j] = (ea[2 * j] - ea[2 * j + 1]) / (2 * rel)
        gn[j] = (no[2 * j] - no[2 * j + 1]) / (2 * rel)
    return J, gh, ge, gn


# ---------------- C1: linearisation, one-sided Jacobians at the kink --------------------------------------------
say("== C1 linearisation (error map, scaled coordinates) ==")
off = np.zeros(NY); off[SIDE] = OFF / SCALE[SIDE]
import os
LIN = pickle.load(open("/tmp/ts_LIN.pkl", "rb")) if os.environ.get("TS_REUSE") and os.path.exists("/tmp/ts_LIN.pkl") else {}
for h in [x for x in H_GRID if x not in LIN]:
    Jp, ghp, gep, gnp = jac_E(h, off)
    Jm, ghm, gem, gnm = jac_E(h, -off)
    U, s, Vt = np.linalg.svd(Jp - Jm)
    u, v = U[:, 0] * s[0], Vt[0]
    sgn = np.sign(v @ off)
    A0 = (Jp + Jm) / 2
    LIN[h] = dict(Ap=Jp, Am=Jm, A0=A0, u=u, v=v, sgn=sgn, gh=(ghp + ghm) / 2, ge=(gep + gem) / 2, gn=(gnp + gnm) / 2)
    say(f"h {h:6.0f}: rho(A+) {max(abs(np.linalg.eigvals(Jp))):.6f}  rho(A-) {max(abs(np.linalg.eigvals(Jm))):.6f}"
        f"  jump sv {s[0]:.3f} / {s[1]:.2e}")
pickle.dump(LIN, open("/tmp/ts_LIN.pkl", "wb"))
L6 = LIN[H_REF]
for mu in (0.9992, 0.9995):
    w = np.concatenate([np.linspace(0, 0.02, 2000), np.linspace(0.02, np.pi, 2000)])
    g = max(abs(L6["v"] @ np.linalg.solve(np.exp(1j * om) * np.eye(NY) - L6["A0"] / mu, L6["u"] / mu)) for om in w)
    say(f"kink small gain at h_ref, mu {mu}: sup_omega |v^T (zI - A0/mu)^-1 u/mu| / 2 = {g / 2:.4f} (< 1 needed)")
    OUT[f"small_gain_{mu}"] = g / 2
ev = np.linalg.eigvals(LIN[H_REF]["A0"])
idx = np.argsort(-abs(ev))
say("slowest modes at h_ref (1/s):", np.round(np.log(ev[idx[:8]]) / DT, 4))
OUT["slow_rate"] = float(-np.log(abs(ev[idx[0]])) / DT)

# ---------------- C2: common Q ------------------------------------------------------------------------------------
say("== C2 common quadratic Lyapunov function ==")
FAST = [i for i, n in enumerate(NAMES) if n.startswith(('dv0', 'dv1', 'a0', 'a1')) or n.endswith('dot_i')
        or n in ('udot', 'vdot', 'wdot')]
W = np.eye(NY); W[FAST, FAST] = 1e-4       # best of the weightings tried (eps in 1..1e-8, mu in 0.999..0.9995)
Q = lyap_q(LIN[H_REF]["A0"], MU, W)
Q = Q / np.max(np.linalg.eigvalsh(Q))       # normalisation only
lam = 0.0
for h in H_GRID:
    a = qnorm(LIN[h]["Ap"], Q); b = qnorm(LIN[h]["Am"], Q)
    lam = max(lam, a, b)
    say(f"h {h:6.0f}: ||A+||_Q {a:.6f}  ||A-||_Q {b:.6f}")
say(f"lambda_lin (max over grid, both pieces) = {lam:.6f}; cond(Q) = {np.linalg.cond(Q):.3e}")
OUT["lambda_lin"] = lam
Lc = np.linalg.cholesky(Q); LTi = np.linalg.inv(Lc.T); Qi = np.linalg.inv(Q)


def qn(z):
    return float(np.sqrt(z @ Q @ z))


# ---------------- C3: disturbance budget --------------------------------------------------------------------------
say("== C3 disturbances ==")
hs = np.arange(H_BAND[0], H_BAND[1] + 0.01, 1.0)
d_drift = []
for h in hs:
    e, _, _, _ = E_many(h, [np.zeros(NY)])
    d_drift.append(qn(e[0]))
d_drift = np.array(d_drift)
lip = np.max(np.abs(np.diff(d_drift)))
say(f"delta_drift: max over 1 m grid {d_drift.max():.3e} at h {hs[d_drift.argmax()]:.0f}; max step between "
    f"neighbours {lip:.3e} (bound used: max + step = {d_drift.max() + lip:.3e})")
dl = []
for h in (10.0, 500.0, 1000.0):
    e0, _, _, _ = E_many(h, [np.zeros(NY)])
    for psi in (0.5 * np.pi, np.pi, 1.5 * np.pi, 0.25 * np.pi):
        for north in (-30000.0, 0.0, 30000.0):
            e1, _, _, _ = E_many(h, [np.zeros(NY)], psi, north)
            dl.append(qn(e1[0] - e0[0]))
d_loc = max(dl)
say(f"delta_loc (heading, +-30 km north): {d_loc:.3e}")
# hidden quaternion norm: plain loop versus smoothed loop over 60 s from the reference at 500 m
m2 = TsMap()
rows_p = m2.sim(500.0, c_of(500.0), 128 * 60, 1)
m2.smooth(True)
rows_s = m2.sim(500.0, c_of(500.0), 128 * 60, 1)
m2.close()
dq = max(qn((rp[4:] - rs[4:]) / SCALE) for rp, rs in zip(rows_p, rows_s))
say(f"plain minus smoothed loop over 60 s (max Q-norm of the chart difference): {dq:.3e}")
delta = d_drift.max() + lip + d_loc + dq
say(f"delta (total, per frame, Q-norm) = {delta:.3e}")
OUT.update(delta_drift=float(d_drift.max() + lip), delta_loc=float(d_loc), delta_q=float(dq), delta=float(delta))

json.dump(OUT, open("/tmp/ts_cert.json", "w"), indent=1, default=float)
say("written /tmp/ts_cert.json")
