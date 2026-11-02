"""Certificate for the level trim of the redesigned law (docs/termsound-proof.tex, Section 6).

Covering argument, no sampling: interval-dual enclosures (`tsmap B`, Tools/termsound/TsInterval.lean) of the frame
map G(x, w) and its Jacobian over a box, with w standing for |beta|, then an explicit N-frame bound.
"""
import sys
import json
import numpy as np
import scipy.linalg as sl
from tsmap import TsMap, NY, NAMES
from trim import SCALE
from terminal import NEW

N = 128
SC = np.concatenate([[1.0], SCALE])                 # scaled coordinates: (x - x*) / SC
NAMES33 = ["h"] + NAMES
FAST = [1 + k for k, n in enumerate(NAMES) if n.startswith(('dv0', 'dv1', 'a0', 'a1')) or n.endswith('dot_i')
        or n in ('udot', 'vdot', 'wdot')]


def say(*a):
    print(*a); sys.stdout.flush()


def level_trim(m, psi, north, x0):
    x = x0.copy()
    for _ in range(12):
        lo, hi, dlo, dhi, _ = m.box(x, np.zeros(33), psi, north)
        r = 0.5 * (lo[:33] + hi[:33]) - x
        if np.max(np.abs(r) / SC) < 1e-11:
            break
        A = 0.5 * (dlo[:33, :33] + dhi[:33, :33])
        x = x - np.linalg.solve(A - np.eye(33), r)
    return x


def analyse(m, psi, north, x, r, Q, box_margin=1.3, verbose=True):
    """Returns (bound on ||Delta_N||_Q / r, details) for D = {||Delta||_Q <= r} around x."""
    Di = np.diag(1 / SC)
    lo, hi, dlo, dhi, sats = m.box(x, np.zeros(33), psi, north)
    A = Di @ (0.5 * (dlo[:33, :33] + dhi[:33, :33])) @ np.diag(SC)
    u = (0.5 * (dlo[:33, 33] + dhi[:33, 33])) / SC
    v = 0.5 * (dlo[33, :33] + dhi[33, :33]) * SC
    beta0 = max(abs(lo[33]), abs(hi[33]))
    d0 = np.maximum(np.abs(lo[:33] - x), np.abs(hi[:33] - x)) / SC    # trim residual enclosure
    Qi = np.linalg.inv(Q)
    L = np.linalg.cholesky(Q)
    qn = lambda z: float(np.linalg.norm(L.T @ z))
    P = [np.eye(33)]
    for _ in range(N):
        P.append(A @ P[-1])
    lamN = float(np.linalg.norm(L.T @ P[N] @ np.linalg.inv(L.T), 2))
    # linear envelope of |A^k Delta0| over D, and of |v^T A^k Delta0|
    S = np.array([r * np.sqrt(np.einsum("ij,jk,ik->i", Pk, Qi, Pk)) for Pk in P])   # (N+1, 33)
    Sv = np.array([r * np.sqrt((v @ Pk) @ Qi @ (v @ Pk)) for Pk in P])
    b = box_margin * S.max(axis=0)
    for it in range(6):
        blo, bhi, bdlo, bdhi, bsats = m.box(x, b * SC, psi, north)
        Ex = np.maximum(np.abs(Di @ bdlo[:33, :33] @ np.diag(SC) - A), np.abs(Di @ bdhi[:33, :33] @ np.diag(SC) - A))
        Ew = np.maximum(np.abs(bdlo[:33, 33] / SC - u), np.abs(bdhi[:33, 33] / SC - u))
        Eb = np.maximum(np.abs(bdlo[33, :33] * SC - v), np.abs(bdhi[33, :33] * SC - v))
        wmax = max(abs(blo[33]), abs(bhi[33]))
        # forward recursion of the nonlinear excursion bound ebar_k (componentwise) and of omega_k, rho_k
        eb = [np.zeros(33)]; om = []; rh = []
        absP = [np.abs(Pk) for Pk in P]
        Pu = [np.abs(Pk @ u) for Pk in P]
        Pd = [np.abs(Pk) @ d0 for Pk in P]
        for k in range(N):
            mk = S[k] + eb[k]
            w_k = min(beta0 + Sv[k] + np.abs(v) @ eb[k] + Eb @ mk, wmax)
            r_k = Ex @ mk + Ew * w_k
            om.append(w_k); rh.append(r_k)
            e_next = sum(Pu[k - j] * om[j] + absP[k - j] @ rh[j] + Pd[k - j] for j in range(k + 1))
            eb.append(e_next)
        reach = (S + np.array(eb)).max(axis=0)
        inside = bool(np.all(reach <= b)) and not any(bsats[i] for i in range(13) if i != 6)
        if verbose:
            say(f"   box iteration {it}: inside={inside}  max reach/box {np.max(reach / b):.3f}  w_max {wmax:.2e}  sats {bsats}")
        if inside:
            break
        b = np.maximum(b, 1.05 * reach)
    # final N-frame bound in Q
    kink = sum(qn(P[N - 1 - j] @ u) * om[j] for j in range(N))
    rem = sum(sum(rh[j][i] * qn(P[N - 1 - j][:, i]) for i in range(33)) for j in range(N))
    dist = sum(qn(P[N - 1 - j] @ (d0 * np.sign(d0 + 1e-300))) for j in range(N))
    bound = lamN + (kink + rem + dist) / r
    det = dict(r=r, lamN=lamN, kink=kink / r, rem=rem / r, dist=dist / r, bound=bound, inside=inside,
               box=dict(zip(NAMES33, (b * SC).tolist())), wmax=wmax, beta0=beta0, sats=bsats,
               kink_first_order=sum(qn(P[N - 1 - j] @ u) * Sv[j] for j in range(N)) / r)
    return bound, det


if __name__ == "__main__":
    PSI, NORTH = np.pi / 2, 100.0          # held track east, 100 m north of the map origin
    m = TsMap(); m.smooth(True); m.cand(**NEW)
    import ref as refmod
    ref = refmod.load()
    sim = m.sim(900.0, refmod.c_of(ref, 900.0), 128 * 240, 128 * 240, psi=PSI, north=NORTH)
    x = level_trim(m, PSI, NORTH, np.concatenate([[sim[-1][3]], sim[-1][4:]]))
    lo, hi, dlo, dhi, sats = m.box(x, np.zeros(33), PSI, NORTH)
    say(f"L0 level trim (psi {PSI:.4f}, north {NORTH:.0f} m): h {x[0]:.4f} m, V_along {x[4]:.4f} m/s, theta {x[2]:.5f};"
        f" fixed-point residual (scaled, enclosure) {np.max(np.maximum(abs(lo[:33] - x), abs(hi[:33] - x)) / SC):.2e};"
        f" beta {lo[33]:.2e}..{hi[33]:.2e}")
    A = np.diag(1 / SC) @ (0.5 * (dlo[:33, :33] + dhi[:33, :33])) @ np.diag(SC)
    AN = np.linalg.matrix_power(A, N)
    say(f"L1 one-second spectral radius of G_x (w held): {max(abs(np.linalg.eigvals(AN))):.4f}")
    W = np.eye(33); W[FAST, FAST] = 1e-4
    Q = sl.solve_discrete_lyapunov((AN / 0.95).T, W); Q /= np.max(np.linalg.eigvalsh(Q))
    Qi = np.linalg.inv(Q)
    say("   half-widths of {||Delta||_Q <= 1e-5} (physical):",
        {n: float(f"{1e-5 * v:.3g}") for n, v in zip(NAMES33, np.sqrt(np.diag(Qi)) * SC) if n in ("h", "phi", "theta", "dpsi", "v_al", "v_rt", "v_dn")})
    bnd, det = analyse(m, PSI, NORTH, x, 1e-5, Q, verbose=False)
    say(f"L2 N-frame bound at r = 1e-5: {bnd:.4f} = lambda_N {det['lamN']:.4f} + kink {det['kink']:.4f} (first-order part "
        f"{det['kink_first_order']:.4f}) + remainder {det['rem']:.4f} + residual {det['dist']:.2e}; box consistent: {det['inside']}")
    say("L3 interval Jacobian radius (scaled) against box width, the beta-table hull:")
    for scale in (0.0, 1e-8, 1e-6):
        blo, bhi, bdlo, bdhi, _ = m.box(x, scale * SC, PSI, NORTH)
        Wd = np.diag(1 / SC) @ (bdhi[:33, :33] - bdlo[:33, :33]) @ np.diag(SC) / 2
        i, j = np.unravel_index(np.argmax(Wd), Wd.shape)
        say(f"   box {scale:g} x SC: max radius {Wd.max():.3e} (d {NAMES33[i]} / d {NAMES33[j]}); beta enclosure "
            f"{blo[33]:.2e}..{bhi[33]:.2e}")
    json.dump(det, open("/tmp/ts_level_cert.json", "w"), indent=1, default=float)
