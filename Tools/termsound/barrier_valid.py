"""Reach of `tsmap B` on R-sized boxes; a Lean panic returns a default value, so stderr output marks an unsound box."""
import os
import subprocess
import tempfile
import numpy as np
import tsmap
from barrier import TRIM, NAMES, PSI, NORTH, FAST0, say
from terminal import NEW


class Probe(tsmap.TsMap):
    def __init__(self):
        self.err = tempfile.NamedTemporaryFile("w+", suffix=".err", delete=False)
        self.p = subprocess.Popen(["nice", "-n", "10", tsmap.EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=self.err, text=True, bufsize=1)

    def clean(self, bw):
        n0 = os.path.getsize(self.err.name)
        lo, hi, _, _, sats = self.box(TRIM, bw, PSI, NORTH)
        self.err.flush()
        ok = os.path.getsize(self.err.name) == n0 and np.isfinite(lo).all() and np.isfinite(hi).all()
        return ok, lo, hi, sum(sats)


def col(name):
    return 0 if name == "h" else 1 + NAMES.index(name)


if __name__ == "__main__":
    m = Probe(); m.cand(**NEW)
    for name in ("h", "v_al", "v_dn", "theta", "q_i", "rpm", "map", "a0_dn"):
        for w in (10.0, 1.0, 0.1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
            bw = np.zeros(33); bw[col(name)] = w
            if m.clean(bw)[0]:
                say(f"{name}: clean at half-width {w:g}"); break
        else:
            say(f"{name}: not clean down to 1e-6")
    base = np.zeros(33)
    for n, w in FAST0.items():
        if n in NAMES:
            base[col(n)] = w
    base[col("theta")], base[col("v_al")], base[col("v_dn")], base[0] = 0.12, 18.0, 30.0, 60.0
    for sc in (1.0, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        ok, lo, hi, ns = m.clean(base * sc)
        say(f"R's boxes x {sc:g}: {'clean' if ok else 'NOT clean'}, saturation flags {ns}, "
            f"v_dn' half-width {(hi[col('v_dn')] - lo[col('v_dn')]) / 2:.3g}, theta' half-width "
            f"{(hi[col('theta')] - lo[col('theta')]) / 2:.3g}")
    bw = np.zeros(33); bw[0], bw[col("v_al")], bw[col("v_dn")], bw[col("theta")] = 60.0, 18.0, 1.0, 0.05
    say(f"slow coordinates only (h 60, v_al 18, v_dn 1, theta 0.05): {'clean' if m.clean(bw)[0] else 'NOT clean'}")
    m.close()
