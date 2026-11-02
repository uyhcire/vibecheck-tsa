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


# A Lean panic (e.g. an out-of-range `arr[i]!`) prints, returns a default value and carries on, which silently
# corrupts results; with this set the Lean runtime aborts instead, and the pipe read fails loudly.
ENV = dict(os.environ, LEAN_ABORT_ON_PANIC="1")


class InvalidEnclosure(RuntimeError):
    """`tsmap B` returned an enclosure marked invalid (`TsInterval.BoxResult.valid`): its numbers are not bounds."""


class TsMap:
    def __init__(self):
        self.p = subprocess.Popen(["nice", "-n", "10", EXE], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  text=True, bufsize=1, env=ENV)

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
        chunk = 32
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
        for i in range(0, len(lines), 32):                  # small chunks: both pipes must not fill at once
            self.p.stdin.write("\n".join(lines[i:i + 32]) + "\n")
            self.p.stdin.flush()
            for _ in lines[i:i + 32]:
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


DIAG = ["alpha", "beta", "vt_fps", "mach", "p_psf", "rho", "h_over_b", "J", "tipMach", "fuel_air", "rpm", "map",
        "thrust", "hp", "elev", "ail", "rud", "gc_raw", "n_raw", "acmd_raw", "elev_raw", "ail_raw", "rud_raw",
        "phiT_raw", "sc", "adot", "stall"]


def _diag(self, h, y, psi=0.0, north=0.0):
    self._send(" ".join(["D", b(psi), b(north), b(h)] + [b(v) for v in y]))
    return dict(zip(DIAG, [f(s) for s in self.p.stdout.readline().split()]))


def _wind(self, wn, we, wd):
    """Constant wind (NED, ft/s) for following M, S and D commands."""
    self._send(" ".join(["W", b(wn), b(we), b(wd)]))


def _keys(self):
    self._send("K")
    out = {}
    while True:
        ln = self.p.stdout.readline().strip()
        if ln == "END":
            return out
        w = ln.split()
        out[w[0]] = [float(x) for x in w[1:]]


TsMap.diag = _diag
TsMap.wind = _wind
TsMap.keys = _keys


def _hold(self, h_ref):
    """Candidate level-off at h_ref (m) for following M and S commands; None restores the gate's law."""
    self._send("H " + b(float("nan") if h_ref is None else h_ref))


TsMap.hold = _hold


GATE = dict(hLevel=float("nan"), kHold=0.005, vRefE=float("nan"), kv=0.02, kg=2.5, kpsi=1.0, kphi=2.5, kp=0.8,
            kiPhi=1.0, kiA=2.0, gcLo=0.05, gcHi=0.35, terminalOnly=True)


def _cand(self, **kw):
    """Candidate law (TsMap.lean `Cand`) for following M, S, R commands; keys as in GATE, missing keys from GATE."""
    p = dict(GATE); p.update(kw)
    self._send(" ".join(["P"] + [b(p[k]) for k in ("hLevel", "kHold", "vRefE", "kv", "kg", "kpsi", "kphi", "kp",
                                                     "kiPhi", "kiA", "gcLo", "gcHi")]
                            + ["1" if p["terminalOnly"] else "0"]))


def _gate(self):
    self._send("G")


TsMap.cand = _cand
TsMap.gate = _gate


def _reftraj(self, x, y, z, v, gam, psi, phi, n_load, thr, n, k):
    self._send(" ".join(["V"] + [b(a) for a in (x, y, z, v, gam, psi, phi, n_load, thr)] + [str(n), str(k)]))
    out = []
    while True:
        ln = self.p.stdout.readline().strip()
        if ln == "END":
            return out
        out.append(ln)


TsMap.reftraj = _reftraj


def _box(self, c, bw, psi=0.0, north=0.0):
    """Interval-dual frame over the box c ± bw (33 inputs): (lo, hi) arrays of shape (34,) for the values
    (h', y', beta) and (34, 34) for the derivatives, plus the saturation flags (1 = can be active).
    Raises InvalidEnclosure when the Lean side marks the enclosure invalid (reasons in the message)."""
    self._send(" ".join(["B", b(psi), b(north)] + [b(v) for v in c] + [b(v) for v in bw]))
    vals, ders = [], []
    for _ in range(34):
        ln = self.p.stdout.readline()
        if not ln:
            raise RuntimeError("tsmap exited during B (a Lean panic aborts it; see stderr)")
        r = [f(s) for s in ln.split()]
        vals.append(r[:2]); ders.append(np.array(r[2:]).reshape(34, 2))
    sats = [int(x) for x in self.p.stdout.readline().split()]
    self.last_alpha = [f(s) for s in self.p.stdout.readline().split()]
    status = self.p.stdout.readline().strip()
    self.last_valid = status == "VALID"
    if not self.last_valid:
        raise InvalidEnclosure(status if status else "tsmap gave no validity line")
    vals = np.array(vals); ders = np.array(ders)
    return vals[:, 0], vals[:, 1], ders[:, :, 0], ders[:, :, 1], sats


TsMap.box = _box
