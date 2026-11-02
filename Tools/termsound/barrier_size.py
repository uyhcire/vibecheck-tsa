"""Size R's fast boxes for C2 by fixed-point iteration: widen every box the adversarial search pushes past 0.9."""
import copy
import json
import sys
import numpy as np
from barrier import THETA0, Pool, say
from barrier_search import Search


def size(pool, th, rounds=6, grow=1.15, **kw):
    th = copy.deepcopy(th)
    for it in range(rounds):
        s = Search(pool, th)
        f, u, mg = s.run("c2", **kw)
        bad = {k: v for k, v in s.exmax.items() if v > 0.9}
        say(f"  round {it}: worst C2 margin {f:+.3f} ({mg['c2_which'] if mg else '-'}), {s.nev} evals; over 0.9: "
            + ", ".join(f"{k} {v:.2f}" for k, v in sorted(bad.items(), key=lambda kv: -kv[1])[:8]))
        if f >= 0.05:
            return th, f
        for k, v in bad.items():
            if k in th["fast"]:
                th["fast"][k] *= max(1.0, v * grow)
            elif k == "dalpha":
                th["dalpha"] *= max(1.0, v * grow)
    return th, f


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    pool = Pool(4)
    th = copy.deepcopy(THETA0); th["k"] = k
    th, f = size(pool, th, de_iter=4, nm_fev=150)
    json.dump(th, open(f"/tmp/barrier_theta_k{k}.json", "w"), indent=1)
    say(json.dumps(th["fast"]), th["dalpha"])
    pool.close()
