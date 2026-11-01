"""Backup-CBF guard for the JSBSim plant.

Drives `flight/target/release/filterd` (the bcbf-city-flight fly-by-wire pilot and filter, one line
per tick) and turns its load-factor / roll-rate / throttle demand into JSBSim elevator, aileron and
throttle with two proportional-integral inner loops. The filter predicts with the crate's point-mass
model, not with JSBSim: its Phase 3 margins (`robust`) exist for that mismatch, but the guarantee
the crate proves for its own model does not transfer. The state frame is the crate's map frame
(UTM 10N metres from Kearny & Market, x east, y grid north, z NAVD88 metres).

usage: .venv/bin/python -I sidecar/bcbf.py --selftest     # inner-loop step responses on the c172p
"""
import math
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "flight", "data", "sf"))
import geo  # noqa: E402  (the crate's projection, so both sides agree to the millimetre)

FILTERD = os.path.join(ROOT, "flight", "target", "release", "filterd")
FT = 0.3048
R_EARTH = 6_371_000.0
# Inner-loop gains (per g, per g-second, per rad/s). ponytail: hand-tuned on the c172p step test below.
KN, KI, KQ = 0.8, 0.6, 0.25
KA, KAI = 2.5, 4.0


def from_local(x, y):
    """Inverse of geo.to_local by Newton iteration with a numeric Jacobian (nanometre round trip)."""
    lon, lat = geo.ORIGIN_LON, geo.ORIGIN_LAT
    for _ in range(6):
        ex, ny = geo.to_local(lon, lat)
        d = 1e-6
        dxl, dyl = geo.to_local(lon + d, lat)
        dxa, dya = geo.to_local(lon, lat + d)
        j11, j12, j21, j22 = (dxl - ex) / d, (dxa - ex) / d, (dyl - ny) / d, (dya - ny) / d
        det = j11 * j22 - j12 * j21
        rx, ry = x - ex, y - ny
        lon += (j22 * rx - j12 * ry) / det
        lat += (-j21 * rx + j11 * ry) / det
    return lon, lat


def local_velocity(lon, lat, vn, ve):
    """Map-frame velocity (m/s) from north/east velocity, via the projection's Jacobian."""
    d = 1e-6
    ex, ny = geo.to_local(lon, lat)
    dxl, dyl = geo.to_local(lon + d, lat)
    dxa, dya = geo.to_local(lon, lat + d)
    dlon = ve / (R_EARTH * math.cos(math.radians(lat))) / d * (180 / math.pi)
    dlat = vn / R_EARTH / d * (180 / math.pi)
    return (dxl - ex) * dlon + (dxa - ex) * dlat, (dyl - ny) * dlon + (dya - ny) * dlat


def model_state(fdm):
    """JSBSim -> the crate's State: [x, y, z, v, gamma, psi, phi, p, n, thr]."""
    lat, lon = fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"]
    x, y = geo.to_local(lon, lat)
    vn, ve, vd = (fdm[f"velocities/v-{d}-fps"] * FT for d in ("north", "east", "down"))
    vt = max(fdm["velocities/vt-fps"] * FT, 1.0)
    vx, vy = local_velocity(lon, lat, vn, ve)
    return [x, y, fdm["position/h-sl-meters"], vt,
            math.asin(max(-1.0, min(1.0, -vd / vt))),     # flight-path angle
            math.atan2(vy, vx),                            # heading of the velocity, CCW from +x
            -fdm["attitude/phi-rad"],                      # crate: + = left wing down
            -fdm["velocities/p-rad_sec"],
            fdm["accelerations/Nz"],
            fdm["fcs/throttle-pos-norm"]]


class InnerLoops:
    """Load-factor and roll-rate demands -> JSBSim elevator and aileron commands."""

    def __init__(self):
        self.ei = 0.0
        self.ep = 0.0

    def controls(self, fdm, nc, pc, thrc, dt):
        nz, q, p = fdm["accelerations/Nz"], fdm["velocities/q-rad_sec"], fdm["velocities/p-rad_sec"]
        e = nc - nz
        self.ei = max(-1.0, min(1.0, self.ei + e * dt))
        elevator = -(KN * e + KI * self.ei) + KQ * q     # JSBSim: negative elevator = nose up
        ep = -pc - p                                     # crate roll rate + = left; JSBSim p + = right
        self.ep = max(-0.3, min(0.3, self.ep + ep * dt))
        aileron = KA * ep + KAI * self.ep
        return (max(-1.0, min(1.0, elevator)), max(-1.0, min(1.0, aileron)), max(0.0, min(1.0, thrc)))


class Bcbf:
    def __init__(self, robust=True, map_name="sf"):
        if not os.path.exists(FILTERD):
            sys.exit(f"{FILTERD} missing: cd flight && cargo build --release --no-default-features --bin filterd")
        self.proc = subprocess.Popen([FILTERD, "--map", map_name] + ([] if robust else ["--nominal"]),
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.loops = InnerLoops()
        self.on = False
        self.mode, self.lam, self.h, self.inv_ok, self.clear = 0, 0.0, 0.0, 1, 0.0
        self.applied = (1.0, 0.0, 0.0)
        self.kamikaze = False

    MODES = ["off", "free", "BLEND", "COMMIT"]

    def tick(self, fdm, pitch, roll, throttle, on, dt, kamikaze=False):
        """One filter tick. Sticks in -1..1 (pitch + = back), throttle 0..1. Returns (elevator, aileron, throttle)."""
        self.on = on
        s = model_state(fdm)
        self.kamikaze = kamikaze
        self.proc.stdin.write(" ".join(f"{v:.6f}" for v in s) + f" {pitch:.4f} {roll:.4f} {throttle:.4f} {int(on)} {int(kamikaze)}\n")
        f = self.proc.stdout.readline().split()
        nc, pc, thrc = float(f[0]), float(f[1]), float(f[2])
        self.mode, self.lam, self.h, self.inv_ok, self.clear = int(f[3]), float(f[4]), float(f[5]), int(f[6]), float(f[7])
        self.applied = (nc, pc, thrc)
        return self.loops.controls(fdm, nc, pc, thrc, dt)

    def status(self):
        h = "NO ESCAPE" if self.on and self.h == float("-inf") else f"h {self.h:5.0f} m"
        return (f"cbf {'ON ' if self.on else 'off'} {self.MODES[self.mode]:6s} {h} clear {self.clear:5.0f} m"
                + (" KAMIKAZE" if self.kamikaze else ""))

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=5)


def selftest():
    import jsbsim
    lon, lat = from_local(2700.0, 134.0)
    assert abs(geo.to_local(lon, lat)[0] - 2700) < 1e-6
    vx, vy = local_velocity(lon, lat, 50.0, 0.0)
    assert abs(vy - 50) < 0.5 and abs(vx) < 0.5, (vx, vy)      # north -> +y
    fdm = jsbsim.FGFDMExec(None)
    fdm.set_debug_level(0)
    fdm.load_model("c172p")
    fdm["ic/h-sl-ft"], fdm["ic/vc-kts"], fdm["ic/psi-true-deg"] = 2000, 90, 90
    fdm["ic/lat-geod-deg"], fdm["ic/long-gc-deg"] = lat, lon
    fdm["propulsion/set-running"] = -1
    dt = 1 / 120
    fdm.set_dt(dt)
    fdm.run_ic()
    fdm["fcs/mixture-cmd-norm"] = 0.9
    fdm["simulation/do_simple_trim"] = 0
    s = model_state(fdm)
    assert abs(s[5] - 0.0) < 0.05, f"heading east should be psi ~ 0, got {s[5]:.3f}"
    loops = InnerLoops()
    for nc, pc, secs, check in [(1.0, 0.0, 2, None), (1.4, 0.0, 3, "nz"), (1.0, 0.4, 2.5, "p")]:
        for _ in range(int(secs / dt)):
            el, ai, th = loops.controls(fdm, nc, pc, fdm["fcs/throttle-pos-norm"], dt)
            fdm["fcs/elevator-cmd-norm"], fdm["fcs/aileron-cmd-norm"], fdm["fcs/throttle-cmd-norm"] = el, ai, th
            fdm.run()
        nz, p = fdm["accelerations/Nz"], -fdm["velocities/p-rad_sec"]
        print(f"demand n={nc} p={pc:+.1f}: after {secs}s Nz={nz:.2f} roll rate={p:+.2f} rad/s  bank={-math.degrees(fdm['attitude/phi-rad']):+.0f} deg")
        if check == "nz":
            assert abs(nz - nc) < 0.15, "load-factor loop not tracking"
        if check == "p":
            assert abs(p - pc) < 0.15, "roll-rate loop not tracking"
    print("bcbf selftest ok")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
