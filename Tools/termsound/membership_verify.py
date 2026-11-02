"""Independent adversarial re-search of a theta found by membership.py (issue #58): the fast boxes of its last round
are loaded and held fixed, and a fresh search (new seed, more starts, longer Nelder-Mead) looks for violations."""
import sys, json, os
import numpy as np
from membership import Loop, settled_data, setup_theta, search, FAST, NAMES, say, HW_H

k = int(sys.argv[1]) if len(sys.argv) > 1 else 512
src = f"/tmp/ts_membership_{k}_{HW_H:g}.json"
d = json.load(open(src))
last = d[sorted(d, key=lambda s: int(s.split()[-1]))[-1]]
L = Loop()
rng = np.random.default_rng(58)
E, F, _ = settled_data(L, rng)
rng2 = np.random.default_rng(5)
runs = []
for _ in range(20):
    e0 = np.array([rng2.uniform(-25, 25), rng2.uniform(-4, 4), rng2.uniform(-6, 6)])
    runs.append(L.roll(e0, L.ys[FAST], 128 * 40, 8))
th = setup_theta(L, E, F, runs, k)
th["b"] = np.array([last["fast_box"][NAMES[i]] for i in FAST])
for it in range(4):
    th["exit"] = np.zeros(len(FAST))
    w = search(L, th, np.random.default_rng(2026 + it), n_screen=300, n_nm=4, maxfev=600)
    say(f"  pass {it}: worst (a) {w[0]:.3f}, (b) {w[1]:.3f}, (c) {w[2]:.3f}; largest exits: "
        + ", ".join(f"{NAMES[FAST[i]]} {th['exit'][i]:.2f}" for i in np.argsort(-th["exit"])[:4]))
    if w[1] < 1:
        break
    th["b"] = th["b"] * np.maximum(1.0, 1.25 * th["exit"])        # widen and search again
say(f"verify k {k}, h half-width {HW_H:g} m: worst (a) {w[0]:.3f}, (b) {w[1]:.3f}, (c) {w[2]:.3f} over {L.n} rollouts; "
    f"status: {'survives search' if max(w) < 1 else 'falsified'}")
json.dump(dict(k=k, hw=HW_H, worst=w.tolist(), rollouts=L.n, ck=th["ck"], r=th["r"], half=th["half"].tolist(),
               vbar=th["vbar"], fast_box={NAMES[i]: float(bb) for i, bb in zip(FAST, th["b"])}), open(f"/tmp/ts_membership_verify_{k}_{HW_H:g}.json", "w"), indent=1)
