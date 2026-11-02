"""Terminal safety by abstraction (docs/termsound-proof.tex, Section 7): level flight above zTop under the law of
docs/escape-law-terminal.md.

Abstraction (per frame, dt = 1/128 s), coordinates e = (h - h*, s, V - V*) with s = v_z + a (h - h*), a = V* K_HOLD,
the tracking error of the climb rate against the level-off command V* gc(h):
    v_z' = v_z + dt (-KG V* K_HOLD (h - h*) - KG v_z)          (flight-path loop on the level-off command)
    h'   = h + dt v_z
    V'   = V + dt (-k_D (V - V*) - g v_z / V*)                   (energy: climbing costs speed; drag restores)
with the law's KG = 2.5, K_HOLD = 0.005 and k_D fitted to JsbExact. Everything else (attitude, rates, alpha, the
engine, the inner loops, tables, the |beta| kink, Coriolis) is the per-frame residual d.

Proved (exact reals, rung 1's q_robust_step): S = {e^T P e <= r^2} is invariant for every |d_i| <= delta_i, where
c = ||A||_P and sqrt(max_{|w_i| <= delta_i} w^T P w) <= (1 - c) r.
Measured: the JsbExact residual over states sampled across S (with off-trim attitude, rates, integrators and
engine within coarse boxes), and 60 s rollouts from them (fast states stay in their boxes; e stays in S).
"""
import sys, json
import numpy as np
import scipy.linalg as sl
from tsmap import TsMap, NAMES
from terminal import NEW

DT = 1.0 / 128
G0 = 9.80665
KG, K_HOLD = 2.5, 0.005
ZTOP = 934.0
PSI, NORTH = np.pi / 2, 0.0
IV, IVR, IVD = NAMES.index("v_al"), NAMES.index("v_rt"), NAMES.index("v_dn")
# coarse boxes for the non-abstracted states (deviation from the level trim)
FAST_BOX = {"phi": 0.02, "theta": 0.02, "dpsi": 0.02, "p_i": 0.05, "q_i": 0.05, "r_i": 0.05, "v_rt": 0.5,
            "ia": 0.02, "ib": 0.02, "iphi": 0.02, "rpm": 50.0}


def say(*a):
    print(*a); sys.stdout.flush()


def coords(h, y, hs, Vs):
    V = float(np.sqrt(y[IV] ** 2 + y[IVR] ** 2 + y[IVD] ** 2))
    return np.array([h - hs, -y[IVD] + Vs * K_HOLD * (h - hs), V - Vs])


def model(Vs, kD):
    a = Vs * K_HOLD
    J = np.array([[-a, 1, 0], [-a * a, -(KG - a), 0], [G0 / Vs * a, -G0 / Vs, -kD]])
    return np.eye(3) + DT * J


def place_state(ys, hs, e, fast):
    """A chart state with abstraction coordinates e and fast-state offsets `fast` (dict) around the trim ys: the
    velocity is rotated to the flight path with climb rate e[1] and speed V* + e[2]; pitch follows the flight path
    (alpha kept at trim) plus the pitch offset."""
    y = ys.copy()
    Vs = float(np.sqrt(ys[IV] ** 2 + ys[IVR] ** 2 + ys[IVD] ** 2))
    V = Vs + e[2]
    vz = e[1] - Vs * K_HOLD * e[0]
    y[IVD] = -vz
    y[IV] = np.sqrt(max(V ** 2 - vz ** 2 - ys[IVR] ** 2, 1.0))
    gam = np.arcsin(vz / V)
    y[NAMES.index("theta")] = ys[NAMES.index("theta")] + gam
    for k, dv in fast.items():
        y[NAMES.index(k)] += dv
    return hs + e[0], y


if __name__ == "__main__":
    m = TsMap(); m.smooth(True); m.cand(**NEW)
    x = np.array(json.load(open("/tmp/ts_level_cert2.json"))["east"]["trim"])
    hs, ys = x[0], x[1:]
    Vs = float(np.sqrt(ys[IV] ** 2 + ys[IVR] ** 2 + ys[IVD] ** 2))
    say(f"level trim (east, latitude 0): h* {hs:.4f} m, V* {Vs:.4f} m/s; slack over zTop {hs - ZTOP:.1f} m")
    # fit k_D from the speed decay of a +3 m/s start (5-60 s)
    h0, y0 = place_state(ys, hs, np.array([0.0, 0.0, 3.0]), {})
    rows = m.sim(h0, y0, 128 * 60, 64)
    eV = np.array([coords(r[3], r[4:], hs, Vs)[2] for r in rows])
    t = rows[:, 0] * DT
    sel = (t > 5) & (np.abs(eV) > 0.05)
    kD = float(-np.polyfit(t[sel], np.log(np.abs(eV[sel])), 1)[0])
    say(f"fitted k_D = {kD:.4f} /s (speed decay of a +3 m/s start)")
    A = model(Vs, kD)
    say("model poles (1/s):", np.round(np.log(np.linalg.eigvals(A)) / DT, 4))
    # the set S: P from the continuous Lyapunov equation in coordinates scaled by (20 m, 2 m/s, 8 m/s)
    Jc = (A - np.eye(3)) / DT
    D = np.diag([1 / 20.0, 1 / 2.0, 1 / 8.0])
    P = D @ sl.solve_continuous_lyapunov((D @ Jc @ np.linalg.inv(D)).T, -np.eye(3)) @ D
    L = np.linalg.cholesky(P)
    c = float(np.linalg.norm(L.T @ A @ np.linalg.inv(L.T), 2))
    Pi = np.linalg.inv(P)
    hw1 = np.sqrt(np.diag(Pi))                                  # half-widths per unit r
    r = 30.0 / hw1[0]                                           # altitude half-width 30 m: 36 m above zTop
    say(f"c = ||A||_P = {c:.8f} per frame; r = {r:.3f}; S half-widths: h {r * hw1[0]:.1f} m, s {r * hw1[1]:.2f} m/s,"
        f" V {r * hw1[2]:.2f} m/s; climb rate up to {r * np.sqrt(np.array([-Vs * K_HOLD, 1, 0]) @ Pi @ np.array([-Vs * K_HOLD, 1, 0])):.2f} m/s")
    # disturbance budget: largest s with delta = s * shape satisfying sqrt(K) <= (1 - c) r
    shape = np.array([1e-4, 1.0, 1.0]) * DT                    # per frame: h 1e-4 m/s, v_z and V in m/s^2 units
    verts = np.array([[a, b, cc] for a in (-1, 1) for b in (-1, 1) for cc in (-1, 1)]) * shape
    Kunit = max(v @ P @ v for v in verts)
    s_max = (1 - c) * r / np.sqrt(Kunit)
    delta = s_max * shape
    say(f"proved budget: invariant for per-frame residual |d_h| <= {delta[0]:.2e} m, |d_vz| <= {delta[1]:.2e} m/s"
        f" ({delta[1] / DT:.3f} m/s^2), |d_V| <= {delta[2]:.2e} m/s ({delta[2] / DT:.3f} m/s^2)")
    # measure the residual over states sampled across S
    rng = np.random.default_rng(7)
    E = []
    for k in range(240):
        w = rng.normal(size=3); w /= np.linalg.norm(w)
        rad = 1.0 if k < 200 else rng.uniform(0, 1) ** (1 / 3)
        e = rad * r * (np.linalg.inv(L.T) @ w)
        fast = {kk: rng.uniform(-b, b) for kk, b in FAST_BOX.items()} if k % 2 == 0 else {}
        E.append((e, fast))
    hs_in, ys_in = zip(*[place_state(ys, hs, e, f) for e, f in E])
    out = m.step_many_full(list(hs_in), list(ys_in), PSI, NORTH)
    res = []
    for (e, f), o in zip(E, out):
        e0 = coords(hs + e[0] if False else o[0] * 0 + (hs + e[0]), place_state(ys, hs, e, f)[1], hs, Vs)
        e1 = coords(o[0], o[1:33], hs, Vs)
        res.append(e1 - A @ e0)
    res = np.abs(np.array(res))
    worst = res.max(axis=0)
    worst_fast = res[0::2].max(axis=0); worst_trimfast = res[1::2].max(axis=0)
    say(f"measured one-frame residual max over {len(E)} states: |d_h| {worst[0]:.2e} m, |d_vz| {worst[1]:.2e} m/s "
        f"({worst[1] / DT:.3f} m/s^2), |d_V| {worst[2]:.2e} m/s ({worst[2] / DT:.3f} m/s^2)")
    say(f"   with fast states at trim: vz {worst_trimfast[1] / DT:.3f} m/s^2, V {worst_trimfast[2] / DT:.3f} m/s^2; "
        f"with fast states off-trim: vz {worst_fast[1] / DT:.3f} m/s^2, V {worst_fast[2] / DT:.3f} m/s^2")
    say(f"ratio residual / budget: h {worst[0] / delta[0]:.3f}, v_z {worst[1] / delta[1]:.3f}, V {worst[2] / delta[2]:.3f}")
    # rollouts: e stays in S and the fast states in their boxes?
    maxq, maxfast, minh = 0.0, {k: 0.0 for k in FAST_BOX}, 1e9
    m2 = TsMap()                                                # plain loop for the rollouts
    m2.cand(**NEW)
    for (e, f) in E[:40]:
        h0, y0 = place_state(ys, hs, e, f)
        rows = m2.sim(h0, y0, 128 * 40, 16, PSI, NORTH)
        for rw in rows:
            ee = coords(rw[3], rw[4:], hs, Vs)
            maxq = max(maxq, float(np.sqrt(ee @ P @ ee)) / r)
            minh = min(minh, rw[3])
            for kk in FAST_BOX:
                maxfast[kk] = max(maxfast[kk], abs(rw[4 + NAMES.index(kk)] - ys[NAMES.index(kk)]) / FAST_BOX[kk])
    say(f"40 rollouts x 40 s (plain loop): max ||e||_P / r = {maxq:.3f}; min altitude {minh:.2f} m; "
        f"max fast-state excursion / box: " + ", ".join(f"{k} {v:.2f}" for k, v in maxfast.items()))
    json.dump(dict(h_star=hs, V_star=Vs, kD=kD, c=c, r=r, half=dict(h=r * hw1[0], vz=r * hw1[1], V=r * hw1[2]),
                   delta=delta.tolist(), residual=worst.tolist(), resid_trimfast=worst_trimfast.tolist(),
                   resid_offfast=worst_fast.tolist(), rollout_max_q=maxq, rollout_min_h=minh, fast_exc=maxfast),
              open("/tmp/ts_abstract.json", "w"), indent=1)
