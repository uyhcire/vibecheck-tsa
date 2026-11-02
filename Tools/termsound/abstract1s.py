"""Variant of abstract.py with one-second maps, residual measured along real-loop trajectories after the inner loop
has settled (docs/termsound-proof.tex, Section 7): e(t+1 s) = A^128 e(t) + d, with S and A as in abstract.py."""
import json
import numpy as np
import scipy.linalg as sl
from tsmap import TsMap
from terminal import NEW
from abstract import coords, model, place_state, IV, IVR, IVD, DT, PSI, NORTH, FAST_BOX, ZTOP

d = json.load(open("/tmp/ts_abstract.json"))
m = TsMap(); m.cand(**NEW)
x = np.array(json.load(open("/tmp/ts_level_cert2.json"))["east"]["trim"])
hs, ys = x[0], x[1:]
Vs = float(np.sqrt(ys[IV] ** 2 + ys[IVR] ** 2 + ys[IVD] ** 2))
A = model(Vs, d["kD"])
Jc = (A - np.eye(3)) / DT
D = np.diag([1 / 20.0, 1 / 2.0, 1 / 8.0])
P = D @ sl.solve_continuous_lyapunov((D @ Jc @ np.linalg.inv(D)).T, -np.eye(3)) @ D
L = np.linalg.cholesky(P)
r = d["r"]
A1 = np.linalg.matrix_power(A, 128)
c1 = float(np.linalg.norm(L.T @ A1 @ np.linalg.inv(L.T), 2))
shape = np.array([0.1, 1.0, 1.0])
verts = np.array([[a, b, cc] for a in (-1, 1) for b in (-1, 1) for cc in (-1, 1)]) * shape
s_max = (1 - c1) * r / np.sqrt(max(v @ P @ v for v in verts))
delta1 = s_max * shape
print(f"one-second map: c1 = {c1:.4f}; budget per second |d_h| <= {delta1[0]:.3f} m, |d_s| <= {delta1[1]:.3f} m/s, "
      f"|d_V| <= {delta1[2]:.3f} m/s", flush=True)
rng = np.random.default_rng(11)
res, minh, settle_exc = [], 1e9, {k: 0.0 for k in FAST_BOX}
for k in range(60):
    w = rng.normal(size=3); w /= np.linalg.norm(w)
    e0 = r * (np.linalg.inv(L.T) @ w) * (1.0 if k % 2 == 0 else rng.uniform(0.3, 1.0))
    fast = {kk: rng.uniform(-b, b) for kk, b in FAST_BOX.items()}
    h0, y0 = place_state(ys, hs, e0, fast)
    rows = m.sim(h0, y0, 128 * 40, 128, PSI, NORTH)
    es = [coords(rw[3], rw[4:], hs, Vs) for rw in rows]
    minh = min(minh, rows[:, 3].min())
    for t in range(3, len(es) - 1):
        if es[t] @ P @ es[t] <= r * r:
            res.append(np.abs(es[t + 1] - A1 @ es[t]))
res = np.array(res)
worst = res.max(axis=0)
print(f"measured one-second residual after 3 s, {len(res)} steps in S: |d_h| {worst[0]:.3f} m, |d_s| {worst[1]:.3f} m/s, "
      f"|d_V| {worst[2]:.3f} m/s; ratio to budget h {worst[0] / delta1[0]:.2f}, s {worst[1] / delta1[1]:.2f}, "
      f"V {worst[2] / delta1[2]:.2f}; min altitude {minh:.2f} m", flush=True)
json.dump(dict(c1=c1, delta1=delta1.tolist(), residual1=worst.tolist(), n=len(res), min_h=minh),
          open("/tmp/ts_abstract1s.json", "w"), indent=1)
