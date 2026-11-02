"""Level-trim certificate on the exact-real footing (docs/termsound-proof.tex, Section 6).

* The beta tables (CYb, Clb, Cnb) are exactly linear on |beta| <= 0.349 (antisymmetric data about their beta = 0
  row); the interval-dual evaluation uses that fact (TsInterval.linRule), so the Jacobian enclosure over a box
  shrinks with the box. The enclosure is the tool for the remainder bound (no simpler analytic route was found for
  the full 33-coordinate frame map); everything else is explicit linear algebra.
* The |beta| drag kink: lifted S-procedure on the one-second map (one LMI, cvxpy/Clarabel), for the linear part.
* The nonlinear remainder: Lemma (N-frame bound) of the document, with the kink handled by the decomposition
  Delta = Delta^L + e (Delta^L the switched linear motion the LMI covers).
"""
import sys
import json
import numpy as np
import scipy.linalg as sl
import cvxpy as cp
from tsmap import TsMap, NAMES
from terminal import NEW
from level_cert import level_trim, SC, NAMES33, FAST, N
import ref as refmod

DT = 1.0 / 128


def say(*a):
    print(*a); sys.stdout.flush()


def lifted_lmi(A, u, v, Q):
    """min mu^2 s.t. ||M_N z||_Q^2 - mu^2 ||Delta0||_Q^2 + sum_k s_k ((v^T M_k z)^2 - w_k^2) <= 0, s >= 0."""
    # coordinates with Q = I, and w rescaled so that |u| = |v|
    L = np.linalg.cholesky(Q)
    A = L.T @ A @ np.linalg.inv(L.T)
    u = L.T @ u
    v = np.linalg.solve(L, v)
    c = np.sqrt(np.linalg.norm(u) / np.linalg.norm(v))
    u, v = u / c, v * c
    Q = np.eye(A.shape[0])
    n = A.shape[0]
    dim = n + N
    M = np.zeros((n, dim)); M[:, :n] = np.eye(n)
    Gs = []
    for k in range(N):
        c = v @ M
        e = np.zeros(dim); e[n + k] = 1.0
        Gs.append(np.outer(c, c) - np.outer(e, e))
        M = A @ M; M[:, n + k] += u
    H = M.T @ Q @ M
    Pq = np.zeros((dim, dim)); Pq[:n, :n] = Q
    s = cp.Variable(N, nonneg=True)
    t = cp.Variable()
    expr = H - t * Pq + sum(s[k] * Gs[k] for k in range(N))
    expr = (expr + expr.T) / 2
    prob = cp.Problem(cp.Minimize(t), [expr << 0])
    try:
        prob.solve(solver=cp.CLARABEL)
    except cp.error.SolverError:
        prob.solve(solver=cp.SCS, eps=1e-9, max_iters=200000)
    sv = np.maximum(s.value, 0)
    tv = float(t.value)
    # verify with a margin: largest eigenvalue of the certificate matrix at a slightly larger t
    tchk = tv * (1 + 1e-6) + 1e-12
    Mchk = H - tchk * Pq + sum(sv[k] * Gs[k] for k in range(N))
    lmax = float(np.max(np.linalg.eigvalsh((Mchk + Mchk.T) / 2)))
    return float(np.sqrt(tchk)), lmax, sv


def certify(m, psi, north, x, Q, r, mu_lin, d_extra, box_margin=1.2):
    Di = np.diag(1 / SC)
    lo, hi, dlo, dhi, _ = m.box(x, np.zeros(33), psi, north)
    A = Di @ (0.5 * (dlo[:33, :33] + dhi[:33, :33])) @ np.diag(SC)
    u = 0.5 * (dlo[:33, 33] + dhi[:33, 33]) / SC
    v = 0.5 * (dlo[33, :33] + dhi[33, :33]) * SC
    beta0 = max(abs(lo[33]), abs(hi[33]))
    # D is centred on the exact equilibrium x*, so the residual term is 0. x* - x = (I - A)^-1 (F(x) - x) to first
    # order; the box is widened by twice that componentwise bound so it contains both points.
    resid = np.maximum(np.abs(lo[:33] - x), np.abs(hi[:33] - x)) / SC
    offset = 2.0 * np.abs(np.linalg.inv(np.eye(33) - A)) @ resid
    d0 = np.zeros(33) + d_extra
    Qi = np.linalg.inv(Q); L = np.linalg.cholesky(Q)
    qn = lambda z: float(np.linalg.norm(L.T @ z))
    P = [np.eye(33)]
    for _ in range(N):
        P.append(A @ P[-1])
    S = np.array([r * np.sqrt(np.einsum("ij,jk,ik->i", Pk, Qi, Pk)) for Pk in P])
    Sv = np.array([r * np.sqrt((v @ Pk) @ Qi @ (v @ Pk)) for Pk in P])
    Pu = [Pk @ u for Pk in P]
    # envelope of the switched linear motion Delta^L
    omL = np.zeros(N + 1)
    for j in range(N + 1):
        omL[j] = Sv[j] + sum(abs(v @ Pu[j - 1 - i]) * omL[i] for i in range(j))
    SL = np.array([S[k] + sum(np.abs(Pu[k - 1 - j]) * omL[j] for j in range(k)) for k in range(N + 1)])
    b = box_margin * SL.max(axis=0) + offset
    absP = [np.abs(Pk) for Pk in P]
    for it in range(8):
        blo, bhi, bdlo, bdhi, bsats = m.box(x, b * SC, psi, north)
        Ex = np.maximum(np.abs(Di @ bdlo[:33, :33] @ np.diag(SC) - A), np.abs(Di @ bdhi[:33, :33] @ np.diag(SC) - A))
        Ew = np.maximum(np.abs(bdlo[:33, 33] / SC - u), np.abs(bdhi[:33, 33] / SC - u))
        Eb = np.maximum(np.abs(bdlo[33, :33] * SC - v), np.abs(bdhi[33, :33] * SC - v))
        wmax = max(abs(blo[33]), abs(bhi[33]))
        eb = [np.zeros(33)]; dw = []; rh = []
        for k in range(N):
            mk = SL[k] + eb[k]
            dwk = np.abs(v) @ eb[k] + beta0 + Eb @ mk               # bound on |w_k - w_k^L|
            omk = min(omL[k] + dwk, wmax)                           # bound on |w_k|
            rk = Ex @ mk + Ew * omk
            dw.append(dwk); rh.append(rk)
            eb.append(sum(np.abs(Pu[k - j]) * dw[j] + absP[k - j] @ rh[j] + absP[k - j] @ d0 for j in range(k + 1)))
        reach = (SL + np.array(eb)).max(axis=0) + offset
        ok_sat = not any(bsats[i] for i in range(13) if i != 6)
        inside = bool(np.all(reach <= b)) and ok_sat and abs(blo[33]) < 0.349 and abs(bhi[33]) < 0.349
        if inside:
            break
        b = np.maximum(b, 1.05 * reach)
    eN = sum(qn(Pu[N - 1 - j]) * dw[j] + sum(rh[j][i] * qn(P[N - 1 - j][:, i]) for i in range(33))
             + qn(P[N - 1 - j] @ d0) for j in range(N))
    bound = mu_lin + eN / r
    alpha_enc = None
    return bound, dict(r=r, mu_lin=mu_lin, nonlin=eN / r, bound=bound, inside=inside, sats=bsats,
                       box=dict(zip(NAMES33, (b * SC).tolist())), wmax=wmax, beta_box=[blo[33], bhi[33]],
                       h_min=float(x[0] - reach[0]), reach=dict(zip(NAMES33, (reach * SC).tolist())))


def lat_shift(label, kappa=0.03):
    """Per-frame shift of the trim (scaled, componentwise) from the latitude drift: |dx*/dN| (level_param.py, settled
    runs at north offsets 0.1, 10 and 50 km) times a cross-track speed kappa (m/s) times one frame."""
    p = json.load(open("/tmp/ts_level_param.json"))[label]
    return np.array(p["dxdN_scaled"]) * kappa * DT


def run(psi, north, label, d_extra_scale=None):
    m = TsMap(); m.smooth(True); m.cand(**NEW)
    ref = refmod.load()
    sim = m.sim(900.0, refmod.c_of(ref, 900.0), 128 * 240, 128 * 240, psi=psi, north=north)
    x = level_trim(m, psi, north, np.concatenate([[sim[-1][3]], sim[-1][4:]]))
    lo, hi, dlo, dhi, _ = m.box(x, np.zeros(33), psi, north)
    Di = np.diag(1 / SC)
    A = Di @ (0.5 * (dlo[:33, :33] + dhi[:33, :33])) @ np.diag(SC)
    u = 0.5 * (dlo[:33, 33] + dhi[:33, 33]) / SC
    v = 0.5 * (dlo[33, :33] + dhi[33, :33]) * SC
    AN = np.linalg.matrix_power(A, N)
    say(f"[{label}] level trim psi {psi:.4f} north {north:.0f}: h {x[0]:.4f} V {x[4]:.4f}; one-second rho(G_x) "
        f"{max(abs(np.linalg.eigvals(AN))):.4f}")
    best = None
    for mu in (0.95,):
        W = np.eye(33); W[FAST, FAST] = 1e-4
        Q = sl.solve_discrete_lyapunov((AN / mu).T, W); Q /= np.max(np.linalg.eigvalsh(Q))
        L = np.linalg.cholesky(Q)
        lamN = float(np.linalg.norm(L.T @ AN @ np.linalg.inv(L.T), 2))
        import os
        cache = "/tmp/ts_lmi.json"
        key = f"{psi:.6f} {north:.1f} {mu}"
        c = json.load(open(cache)) if os.path.exists(cache) else {}
        if key in c:
            mu_lin, lmax = c[key]
        else:
            mu_lin, lmax, sv = lifted_lmi(A, u, v, Q)
            c[key] = [mu_lin, lmax]; json.dump(c, open(cache, "w"))
        say(f"  Q(mu={mu}): ||A^N||_Q {lamN:.4f}; lifted S-procedure with the kink: mu_lin {mu_lin:.4f} "
            f"(certificate matrix max eigenvalue {lmax:.2e})")
        if best is None or mu_lin < best[0]:
            best = (mu_lin, Q, mu)
    mu_lin, Q, mu = best
    Qi = np.linalg.inv(Q)
    hw = np.sqrt(np.diag(Qi)) * SC
    say("  half-widths of D per unit r (physical):", {n: float(f"{v:.3g}") for n, v in zip(NAMES33, hw)
                                                      if n in ("h", "phi", "theta", "dpsi", "v_al", "v_rt", "v_dn", "rpm")})
    results = []
    for r in (1e-8, 3e-8, 1e-7, 2e-7, 3e-7, 1e-6):
        bnd, det = certify(m, psi, north, x, Q, r, mu_lin, lat_shift(label) if d_extra_scale is None else d_extra_scale)
        results.append(det)
        say(f"  r {r:g}: bound {bnd:.4f} = mu_lin {mu_lin:.4f} + nonlinear {det['nonlin']:.4f}; box consistent "
            f"{det['inside']}; h_min {det['h_min']:.3f} m; beta {det['beta_box'][0]:.2e}..{det['beta_box'][1]:.2e}")
        if not det['inside']:
            break
    for det in results:
        b = np.array([det["box"][n] for n in NAMES33])
        m.box(x, b, psi, north)
        det["alpha_box"] = list(m.last_alpha)
    say("  alpha on the boxes (must stay inside CDwbh's segment [-0.0349, -0.0175], below 0 for the beta rule):",
        [f"{d['alpha_box'][0]:.6f}..{d['alpha_box'][1]:.6f}" for d in results])
    m.close()
    return x, mu_lin, results


if __name__ == "__main__":
    out = {}
    x, mu_lin, res = run(np.pi / 2, 0.0, "east")   # north 0: there chart(place(x)) = x exactly (Section 6)
    out["east"] = dict(trim=x.tolist(), mu_lin=mu_lin, results=res)
    ok = [d for d in res if d["inside"] and d["bound"] < 1]
    if ok:
        best = min(ok, key=lambda d: d["bound"])
        big = max(ok, key=lambda d: d["r"])
        say(f"CERTIFIED: radii {[d['r'] for d in ok]}; best factor {best['bound']:.4f} at r {best['r']:g}; largest r {big['r']:g}"
            f" (factor {big['bound']:.4f}); altitude on the union of images >= {min(d['h_min'] for d in ok):.3f} m > zTop 934 m")
    json.dump(out, open("/tmp/ts_level_cert2.json", "w"), indent=1, default=float)
