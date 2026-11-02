"""`make barrier`: for each k, size (unless --base) R's fast boxes (barrier_size.py), then search C1-C3 adversarially and print the
theta table; results in /tmp/barrier_results_<ks>.json."""
import copy
import json
import sys
import time
import numpy as np
from barrier import THETA0, Pool, say
from barrier_size import size
from barrier_search import run_theta, describe

ARGS = sys.argv[1:]
BASE = "--base" in ARGS
SETS = dict(a.split("=", 1) for a in ARGS if "=" in a and not a.startswith("--"))
KS = [int(a) for a in ARGS if a.isdigit()] or [1, 16, 64, 128, 512]
TAG = next((a[6:] for a in ARGS if a.startswith("--tag=")), "base_" * BASE + "_".join(map(str, KS)))
OUT = f"/tmp/barrier_results_{TAG}.json"


def theta_for(k):
    """THETA0 with k, then key=value overrides; fast=<results.json> takes the sized boxes of that file's k."""
    th = copy.deepcopy(THETA0); th["k"] = k
    for key, v in SETS.items():
        if key == "fast":
            src = json.load(open(v))[str(k)]["theta"]
            th["fast"], th["dalpha"] = src["fast"], src["dalpha"]
        else:
            th[key] = float(v)
    return th

def stopping(pool):
    """Altitude lost before the pull-up arrests a descent, from 945 m at V*, other states at trim (sets wl, wq)."""
    from barrier import YS, VS, IV, IVR, IVD, ITH, PSI, NORTH
    out = {}
    for vz in (5.0, 10.0, 15.0, 20.0):
        y = YS.copy(); y[IVD] = vz; y[IV] = np.sqrt(VS * VS - vz * vz - YS[IVR] ** 2); y[ITH] += np.arcsin(-vz / VS)
        rows = pool.ms[0].sim(945.0, y, 128 * 5, 1, PSI, NORTH)
        out[vz] = 945.0 - float(rows[:, 3].min())
    A = np.array([[v, v * v] for v in out]); tau, c = np.linalg.lstsq(A, np.array(list(out.values())), rcond=None)[0]
    say("altitude lost from a descent at V*: " + ", ".join(f"{v:.0f} m/s {d:.2f} m" for v, d in out.items())
        + f"; fit tau |v_z| + v_z^2 / (2 a): tau {tau:.3f} s, a {1 / (2 * c):.1f} m/s^2")
    return out


if __name__ == "__main__":
    pool = Pool(4)
    stopping(pool)
    out = {}
    for k in KS:
        t = time.time()
        th = theta_for(k)
        if not BASE:
            say(f"== k = {k}: sizing R's fast boxes for C2")
            th, _ = size(pool, th, rounds=5, de_iter=4, nm_fev=150)
        r = run_theta(pool, th, de_iter=8, n_nm=4, nm_fev=250)
        for c in ("c1", "c3"):
            r[c]["worst"] = describe(pool, th, r[c]["u"], th["Delta"] if c == "c1" else None)
        r["c2"]["worst"] = describe(pool, th, r["c2"]["u"])
        out[k] = dict(theta=th, result=r, secs=time.time() - t)
        say(f"k = {k}: C1 band margin {r['c1']['value']:+.3f} m; drop {r['drop']['value']:.3f} m (eps needed, Delta "
            f"{th['Delta']}); C2 margin {r['c2']['value']:+.3f} ({r['c2']['which']}); C3 margin {r['c3']['value']:+.3f} m;"
            f" C4 margin {r['c4']['value']:+.3f} m; {time.time() - t:.0f} s")
        json.dump(out, open(OUT, "w"), indent=1, default=str)
    say("\n| k | C1 min B(f^k x) - b (band) | max drop B(x) - B(f^k x) vs Delta | C2 1 - max excursion | C3 min h - F | C4 b - F |")
    say("|---|---|---|---|---|---|")
    for k, d in out.items():
        r, th = d["result"], d["theta"]
        say(f"| {k} | {r['c1']['value']:+.2f} m | {r['drop']['value']:.2f} m vs {th['Delta']} | {r['c2']['value']:+.3f} "
            f"({r['c2']['which']}) | {r['c3']['value']:+.2f} m | {r['c4']['value']:+.1f} m |")
    pool.close()
