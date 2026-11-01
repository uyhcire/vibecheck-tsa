"""Fine-resolution CBF: Eric Yu and Luis Pabon's gatekeeper filter (libgate) with JsbExact as the plant.

The gate verifies escapes on JsbExact, a bit-exact Lean copy of JSBSim 1.3.3's c172p, and needs that aircraft's
full private state every tick. The pip jsbsim module cannot export it, so in this mode the aircraft the pilot
flies IS JsbExact (libcityjsb), stepped at 1/128 s with the surfaces the gate returns; by main's validation it
computes the same doubles JSBSim would. `ExactPlant` presents it to the sidecar with the JSBSim property names
the sidecar reads. The plant flies at latitude/longitude 0 (where cityjsb_new starts); the gate's map origin is
set so that point is the scenario's map start, and the display puts map metres on the Bay with gridmap.py.

Build the libraries on main: `make gate` -> dist/{libgate,libcityjsb}.dylib (GATE_DIST or --gate-dist points there).

usage: .venv/bin/python -I sidecar/gate.py --selftest
"""
import ctypes as C
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gridmap  # noqa: E402

FT, KT = 0.3048, 0.5144
A_WGS, E2_WGS = 6378137.0, 6.69437999014e-3
DIST = os.environ.get("GATE_DIST") or os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                                                   "vibecheck-tsa-worktrees", "main", "dist")
NOBS, MAX_FRAMES = 22, 16
ESCAPE, PILOT = 1, 0


class GateConfig(C.Structure):
    _fields_ = [("abi_version", C.c_uint32), ("size", C.c_uint32), ("map_seed", C.c_uint64), ("map_path", C.c_char_p),
                ("origin_lat_deg", C.c_double), ("origin_lon_deg", C.c_double), ("origin_alt_m", C.c_double),
                ("pilot_kind", C.c_uint32), ("tick_frames", C.c_uint32), ("budget_frames", C.c_uint32), ("time_cap_ms", C.c_uint32)]


class GatePilot(C.Structure):
    _fields_ = [("abi_version", C.c_uint32), ("size", C.c_uint32), ("kind", C.c_uint32), ("reserved", C.c_uint32),
                ("elevator", C.c_double), ("aileron", C.c_double), ("rudder", C.c_double), ("throttle", C.c_double),
                ("nz", C.c_double), ("roll_rate", C.c_double)]


class GateResult(C.Structure):
    _fields_ = [("abi_version", C.c_uint32), ("size", C.c_uint32), ("mode", C.c_int32), ("escape", C.c_int32),
                ("verified", C.c_uint32), ("frames", C.c_uint32), ("surfaces", (C.c_double * 4) * MAX_FRAMES),
                ("path", C.POINTER(C.c_double)), ("path_len", C.c_uint32), ("check_frames", C.c_uint32),
                ("cpu_ms", C.c_double), ("wall_ms", C.c_double), ("map_pos", C.c_double * 3), ("clearance", C.c_double)]


def load(dist=DIST):
    jsb = C.CDLL(os.path.join(dist, "libcityjsb.dylib"))
    g = C.CDLL(os.path.join(dist, "libgate.dylib"))
    jsb.cityjsb_new.restype = C.c_void_p
    jsb.cityjsb_new.argtypes = [C.c_double] * 6
    jsb.cityjsb_step.argtypes = [C.c_void_p, C.c_double, C.c_double, C.c_double, C.c_double, C.POINTER(C.c_double)]
    jsb.cityjsb_step_dump.argtypes = [C.c_void_p, C.c_double, C.c_double, C.c_double, C.c_double, C.POINTER(C.c_double)]
    jsb.cityjsb_obs_from_dump.argtypes = [C.POINTER(C.c_double), C.c_size_t, C.POINTER(C.c_double)]
    jsb.cityjsb_dump_len.restype = C.c_size_t
    jsb.cityjsb_free.argtypes = [C.c_void_p]
    g.gate_new.restype = C.c_void_p
    g.gate_new.argtypes = [C.POINTER(GateConfig), C.POINTER(C.c_int)]
    g.gate_tick.argtypes = [C.c_void_p, C.POINTER(C.c_double), C.c_size_t, C.POINTER(GatePilot), C.POINTER(GateResult)]
    g.gate_free.argtypes = [C.c_void_p]
    g.gate_reset.argtypes = [C.c_void_p]
    g.gate_escape_name.restype = C.c_char_p
    g.gate_escape_name.argtypes = [C.c_int32]
    g.gate_map_surface.restype = C.c_double
    g.gate_map_surface.argtypes = [C.c_void_p, C.c_double, C.c_double]
    return jsb, g


class ExactPlant:
    """JsbExact as the sidecar's aircraft, at map start (sx, sy), reading like a JSBSim FGFDMExec."""

    DT = 1.0 / 128

    def __init__(self, libs, sx, sy, alt_m, v_ms, psi_rad, throttle=0.75, gam=0.0):
        self.jsb, self.gate_lib = libs
        self.sx, self.sy = sx, sy
        self.n = self.jsb.cityjsb_dump_len()
        self.dump = (C.c_double * self.n)()
        self.obs = (C.c_double * NOBS)()
        self.p = self.jsb.cityjsb_new(alt_m, v_ms, gam, psi_rad, 0.0, 0.06)
        if not self.p:
            raise RuntimeError("cityjsb_new failed (Lean runtime)")
        self.cmd = [0.0, 0.0, 0.0, throttle]        # elevator, aileron, rudder, throttle the pilot set
        self.queue = []                              # per-frame rows the gate wants applied instead
        self.frames = 0
        self.surface = 0.0                           # map surface under us (from the gate), for AGL
        self._step(*self.cmd)                        # one frame so the dump exists

    def _step(self, el, ai, ru, th):
        self.jsb.cityjsb_step_dump(self.p, el, ai, ru, th, self.dump)
        self.jsb.cityjsb_obs_from_dump(self.dump, self.n, self.obs)
        self.frames += 1

    def run(self):
        row = self.queue.pop(0) if self.queue else self.cmd
        self._step(*row)
        self.applied = list(row)

    def get_sim_time(self):
        return self.frames * self.DT

    def map_xy(self):
        o = self.obs
        return self.sx + o[1], self.sy + o[0]       # east, north from the lat/lon 0 start

    def __setitem__(self, key, value):
        i = {"fcs/elevator-cmd-norm": 0, "fcs/aileron-cmd-norm": 1, "fcs/rudder-cmd-norm": 2, "fcs/throttle-cmd-norm": 3}.get(key)
        if i is not None:
            self.cmd[i] = float(value)

    def __getitem__(self, key):
        o = self.obs
        x, y = self.map_xy()
        if key == "position/lat-geod-deg":
            return gridmap.to_geo(x, y)[0]
        if key == "position/long-gc-deg":
            return gridmap.to_geo(x, y)[1]
        if key == "position/h-sl-meters":
            return o[2]
        if key == "position/h-sl-ft":
            return o[2] / FT
        if key == "position/h-agl-ft":
            return (o[2] - self.surface) / FT
        if key == "attitude/phi-rad":
            return o[7]
        if key == "attitude/phi-deg":
            return math.degrees(o[7])
        if key == "attitude/theta-deg":
            return math.degrees(o[8])
        if key == "attitude/psi-deg":
            return math.degrees(o[9]) % 360
        if key == "velocities/vt-fps":
            return o[6] / FT
        if key == "velocities/vc-kts":
            return math.sqrt(max(0.0, 2 * o[17] / 1.225)) / KT
        if key == "velocities/v-north-fps":
            return o[3] / FT
        if key == "velocities/v-east-fps":
            return o[4] / FT
        if key == "velocities/v-down-fps":
            return o[5] / FT
        if key == "velocities/p-rad_sec":
            return o[10]
        if key == "velocities/q-rad_sec":
            return o[11]
        if key == "velocities/r-rad_sec":
            return o[12]
        if key == "accelerations/Nz":
            return o[15]
        if key == "accelerations/udot-ft_sec2":
            return 0.0
        if key == "propulsion/engine/engine-rpm":
            return o[18]
        if key == "propulsion/engine/power-hp":
            return 160.0 * self.cmd[3] * o[18] / 2700.0   # ponytail: not in the observation; a shape for the gauge
        if key in ("propulsion/engine/thrust-lbs", "propulsion/engine/fuel-flow-rate-pps"):
            return 0.0
        if key == "fcs/throttle-pos-norm":
            return self.cmd[3]
        if key == "fcs/throttle-cmd-norm":
            return self.cmd[3]
        if key == "gear/unit/WOW":
            return 1.0 if o[16] < 1.0 else 0.0
        return 0.0                                    # manifold pressure, fuel flow: not in the observation

    def close(self):
        self.jsb.cityjsb_free(self.p)


class GateFilter:
    """The gate as the sidecar's filter object (same tick/status/close/clear surface as Bcbf)."""

    def __init__(self, libs, plant, tick_frames=3):
        self.jsb, self.lib = libs
        self.plant = plant
        cfg = GateConfig(1, C.sizeof(GateConfig), 1337, None,
                         -plant.sy / (A_WGS * (1 - E2_WGS)) * 180 / math.pi, -plant.sx / A_WGS * 180 / math.pi, 0.0,
                         1, tick_frames, 0, 0)
        err = C.c_int(0)
        self.g = self.lib.gate_new(C.byref(cfg), C.byref(err))
        if not self.g:
            raise RuntimeError(f"gate_new failed: {err.value}")
        self.r = GateResult()
        self.on = False
        self.mode, self.escape, self.verified, self.clear, self.cpu = PILOT, -1, 0, float("inf"), 0.0
        self.tick_frames = tick_frames

    def tick(self, fdm, pitch, roll, throttle, on, dt, kamikaze=False, hostile=False):
        """One tick = tick_frames plant frames. Returns the surfaces the loop should set (the gate's rows win)."""
        self.on = on
        el, ai, ru, th = -pitch, roll, fdm.cmd[2], throttle
        if hostile or kamikaze:            # test pilot: fly at the tallest tower (63, 63) at 150 m, full power
            o = fdm.obs
            x, y = fdm.map_xy()
            e = (math.atan2(63.0 - x, 63.0 - y) - o[9] + math.pi) % (2 * math.pi) - math.pi
            bank = max(-0.6, min(0.6, 2.0 * e))
            ai = max(-1.0, min(1.0, 2.0 * (bank - o[7]) - 0.3 * o[10]))
            pitch_c = max(-0.15, min(0.15, 0.01 * (150.0 - o[2])))
            el = max(-1.0, min(1.0, 1.5 * (o[8] - pitch_c) + 0.5 * o[11]))
            th = 1.0
        p = GatePilot(1, C.sizeof(GatePilot), 1, 0, el, ai, ru, th, 0.0, 0.0)
        rc = self.lib.gate_tick(self.g, fdm.dump, fdm.n, C.byref(p), C.byref(self.r))
        if rc != 0:
            raise RuntimeError(f"gate_tick: {rc}")
        r = self.r
        self.mode, self.escape, self.verified, self.clear, self.cpu = r.mode, r.escape, r.verified, r.clearance, r.cpu_ms
        x, y = fdm.map_xy()
        fdm.surface = self.lib.gate_map_surface(self.g, x, y)
        if on:
            fdm.queue = [list(r.surfaces[i]) for i in range(r.frames)]
            el, ai, ru, th = fdm.queue[0]
        else:
            fdm.queue = []
        return el, ai, th

    def status(self):
        name = self.lib.gate_escape_name(self.escape).decode() if self.escape >= 0 else "none"
        mode = "ESCAPE" if (self.on and self.mode == ESCAPE) else "pilot"
        return (f"gate {'ON ' if self.on else 'off'} {mode:6s} esc {name:8s} {'verified' if self.verified else 'UNVERIFIED'} "
                f"clear {self.clear:6.1f} m  {self.cpu:4.1f} ms")

    def close(self):
        self.lib.gate_free(self.g)


def selftest():
    libs = load()
    for on in (True, False):
        # 600 m west of the tallest tower (63, 63, 459 m) at 150 m, heading east, hands off: into the tower in ~12 s.
        plant = ExactPlant(libs, -540.0, 63.0, 150.0, 45.0, math.pi / 2)
        gate = GateFilter(libs, plant)
        t, min_clear, crashed = 0.0, float("inf"), False
        while t < 120.0:
            el, ai, th = gate.tick(plant, 0.0, 0.0, 0.75, on, 3 / 128)
            plant["fcs/elevator-cmd-norm"], plant["fcs/aileron-cmd-norm"], plant["fcs/throttle-cmd-norm"] = el, ai, th
            for _ in range(3):
                plant.run()
            t += 3 / 128
            min_clear = min(min_clear, gate.clear)
            if gate.clear < 0:
                crashed = True
                break
        x, y = plant.map_xy()
        print(f"gate {'on ' if on else 'off'}: {'CRASHED' if crashed else 'flew'} {t:.1f} s, min clearance {min_clear:.1f} m, "
              f"at map ({x:.0f}, {y:.0f}), {plant['velocities/vc-kts']:.0f} kt, last: {gate.status()}")
        if on:
            assert not crashed and min_clear > 0, (crashed, min_clear)
        else:
            assert crashed, "the hostile pilot should crash without the gate"
        gate.close()
        plant.close()
    print("gate selftest ok")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
