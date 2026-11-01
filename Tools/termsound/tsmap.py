"""Python side of `tsmap` (Tools/termsound/TsMap.lean): a persistent pipe to the Lean frame map.

Floats cross the pipe as decimal bit patterns, so values are exact doubles in both directions.
"""
import os
import struct
import subprocess

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "tsmap")
NY = 32
NAMES = ["phi", "theta", "dpsi", "v_al", "v_rt", "v_dn", "p_i", "q_i", "r_i",
         "dv0_al", "dv0_rt", "dv0_dn", "dv1_al", "dv1_rt", "dv1_dn",
         "a0_al", "a0_rt", "a0_dn", "a1_al", "a1_rt", "a1_dn",
         "pdot_i", "qdot_i", "rdot_i", "udot", "vdot", "wdot", "rpm", "map", "ia", "ib", "iphi"]


def b(x):
    return str(struct.unpack("<Q", struct.pack("<d", float(x)))[0])


def f(s):
    return struct.unpack("<d", struct.pack("<Q", int(s)))[0]


class TsMap:
    def __init__(self):
        self.p = subprocess.Popen(["nice", "-n", "10", EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1)

    def smooth(self, on=True):
        """Use the smoothed loop (unit quaternion before every frame) for M and S commands."""
        self._send("Z 1" if on else "Z 0")

    def _send(self, line):
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()

    def step(self, h, y, psi=0.0, north=0.0):
        """One frame: (h', y')."""
        self._send(" ".join(["M", b(psi), b(north), b(h)] + [b(v) for v in y]))
        r = [f(s) for s in self.p.stdout.readline().split()]
        return r[0], np.array(r[1:1 + NY])

    def step_full(self, h, y, psi=0.0, north=0.0):
        """One frame: (h', y', east, north) with the CG displacement over the frame."""
        self._send(" ".join(["M", b(psi), b(north), b(h)] + [b(v) for v in y]))
        r = [f(s) for s in self.p.stdout.readline().split()]
        return r[0], np.array(r[1:1 + NY]), r[1 + NY], r[2 + NY]

    def step_many(self, hs, ys, psi=0.0, north=0.0):
        """Batched frames, pipelined."""
        lines = [" ".join(["M", b(psi), b(north), b(h)] + [b(v) for v in y]) for h, y in zip(hs, ys)]
        out = []
        chunk = 256
        for i in range(0, len(lines), chunk):
            self.p.stdin.write("\n".join(lines[i:i + chunk]) + "\n")
            self.p.stdin.flush()
            for _ in lines[i:i + chunk]:
                r = [f(s) for s in self.p.stdout.readline().split()]
                out.append(r)
        out = np.array(out)
        return out[:, 0], out[:, 1:1 + NY]

    def step_many_full(self, hs, ys, psi=0.0, north=0.0):
        """Batched frames: array of rows [h', y'(32), east, north]."""
        lines = [" ".join(["M", b(psi), b(north), b(h)] + [b(v) for v in y]) for h, y in zip(hs, ys)]
        out = []
        for i in range(0, len(lines), 256):
            self.p.stdin.write("\n".join(lines[i:i + 256]) + "\n")
            self.p.stdin.flush()
            for _ in lines[i:i + 256]:
                out.append([f(s) for s in self.p.stdout.readline().split()])
        return np.array(out)

    def sim(self, h, y, n, k, psi=0.0, north=0.0):
        """n frames of the real closed loop from `place`; rows [frame, east, north, h, y...] every k frames."""
        self._send(" ".join(["S", b(psi), b(north), b(h)] + [b(v) for v in y] + [str(n), str(k)]))
        return self._rows()

    def run(self, x, y, z, v, gam, psi, phi, n_load, thr, n, k):
        """The straight escape from `startPlane`: rows [frame, turning, east, north, h, y...]."""
        self._send(" ".join(["R"] + [b(a) for a in (x, y, z, v, gam, psi, phi, n_load, thr)] + [str(n), str(k)]))
        return self._rows()

    def obs_check(self, x, y, z, v, gam, psi, phi, n_load, thr, n):
        self._send(" ".join(["O"] + [b(a) for a in (x, y, z, v, gam, psi, phi, n_load, thr)] + [str(n)]))
        out = []
        while True:
            ln = self.p.stdout.readline().strip()
            if ln == "END":
                return out
            out.append(ln)

    def _rows(self):
        rows = []
        while True:
            ln = self.p.stdout.readline().strip()
            if ln == "END":
                return np.array(rows)
            w = ln.split()
            rows.append([float(w[0])] + [f(s) for s in w[1:]] if len(w) > 1 else [])

    def close(self):
        self.p.stdin.close()
        self.p.wait()


def _stepn_many(self, hs, ys, n, psi=0.0, north=0.0):
    """Batched n-frame maps: rows [east, north, h_n, y_n(32)] after n frames from each place(h, y)."""
    out = []
    lines = [" ".join(["S", b(psi), b(north), b(h)] + [b(v) for v in y] + [str(n), str(n)]) for h, y in zip(hs, ys)]
    for i in range(0, len(lines), 64):
        self.p.stdin.write("\n".join(lines[i:i + 64]) + "\n")
        self.p.stdin.flush()
        for _ in lines[i:i + 64]:
            rows = self._rows()
            out.append(rows[-1][1:])
    return np.array(out)


TsMap.stepn_many = _stepn_many
