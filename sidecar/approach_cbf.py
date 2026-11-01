"""Approach CBF: keeps the pilot inside a glideslope cone and a speed band on final to KPAO runway 31.

Safe set (all with respect to the runway 31 threshold, apex 50 ft above it):
  2 deg <= elevation angle <= 4 deg      (3 deg glideslope, +/-1 deg)
  |lateral angle| <= 3 deg               (floored at 5 m near the threshold)
  v_min(d) <= KIAS <= v_max(d)           80 +/-10 on final, 75 +/-5 at the threshold, 65 +/-5 to touchdown
The cone is written in distances, y_max = tan(3 deg) * d and u in [tan(2 deg) d, tan(4 deg) d], so each bound is
an exponential (higher-order) CBF with a closed-form clamp: load factor for the vertical cone (relative degree 2),
roll rate for the lateral cone (degree 3) and the bank limit (degree 1), throttle for speed (degree 2 through the
engine's spool-up, with the load factor taking over when the throttle saturates). The pilot's stick becomes a load-factor and
roll-rate demand, the filter clamps those demands, and bcbf.InnerLoops turns them into elevator and aileron.
Inside the set every input passes through unchanged. ponytail: d'' = 0 and v' sin(gamma) are dropped in the
derivatives; the gains absorb it, the selftest checks it.

usage: .venv/bin/python -I sidecar/approach_cbf.py --selftest
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bcbf import InnerLoops  # noqa: E402

G, FT, KT = 9.81, 0.3048, 0.5144
# KPAO runway 31 (X-Plane apt.dat): threshold and far end, field elevation.
THR_LAT, THR_LON = 37.4584919, -122.1124379
END_LAT, END_LON = 37.4637511, -122.1176553
FIELD_FT, TCH_FT = 7.0, 50.0          # threshold crossing height: standard 50 ft (set 0 for a path into the threshold)
HALF_WIDTH = 10.5                     # m, runway is 21 m wide
LAT_FLOOR = 5.0                       # m, the lateral cone never gets tighter than this (keeps the wheels on the pavement)
GS_DEG, GS_TOL_DEG, LAT_TOL_DEG = 3.0, 1.0, 3.0
D_FLARE = 550.0                       # m before the threshold where the vertical cone hands over to the flare barrier (~0.3 NM)
# Flare barrier: sink rate may not exceed SINK_MIN + SINK_K * wheel height (capped), so the round-out is exponential and
# the wheels touch at ~SINK_MIN. Active all the way down; above the cone it never binds (a 3 deg slope at 80 kt is 2.2 m/s).
SINK_MIN, SINK_K, SINK_CAP = 0.9, 0.12, 5.0   # m/s, 1/s, m/s: 180 ft/min at touchdown, shaping the last ~110 ft
GEAR_H = 1.3                          # m from the c172p CG to the wheels
K_F = 1.0                             # 1/s, flare CBF gain
V_FINAL, V_FINAL_TOL = 80.0, 10.0     # KIAS, Cirrus-style final
V_THRESH, V_THRESH_TOL = 75.0, 5.0
V_TOUCH, V_TOUCH_TOL = 65.0, 5.0
D_SLOW = 700.0                        # m: the band slides from final to threshold values over this distance
V_MARGIN = 1.5                        # kt enforced inside the stated band: the throttle ECBF settles ~1.3 kt past its edge
# ECBF gains (1/s) and limits
K_V1, K_V2 = 0.6, 1.5
K_L1, K_L2, K_L3 = 0.4, 1.0, 2.0
K_PHI, PHI_MAX = 2.0, math.radians(30)
K_S1, K_S2 = 0.5, 0.8                 # speed ECBF gains (1/s)
TAU_T = 1.5                           # s, engine/prop spool-up seen on the c172p
MASS = 1050.0                         # kg, c172p as flown
K_T = 2000.0                          # N at full throttle around 70-90 kt (JSBSim c172p: ~470 lb)
N_STICK, PHI_STICK = 1.0, math.radians(30)  # full stick = +1 g / 30 deg of bank (stick centred = wings level)


def _enu(lat, lon):
    """Flat-earth metres east/north of the threshold."""
    return ((lon - THR_LON) * math.radians(1) * 6_371_000 * math.cos(math.radians(THR_LAT)),
            (lat - THR_LAT) * math.radians(1) * 6_371_000)


_EX, _NX = _enu(END_LAT, END_LON)
COURSE = math.atan2(_EX, _NX)                      # runway 31 true course, rad (~322 deg)
_AE, _AN = -math.sin(COURSE), -math.cos(COURSE)    # unit vector from the threshold back along the approach
_RE, _RN = math.cos(COURSE), -math.sin(COURSE)     # unit vector to the right of the approach course


def speed_band(d):
    """(v_min, v_max) KIAS at along-track distance d (m before the threshold)."""
    if d <= 0:
        return V_TOUCH - V_TOUCH_TOL, V_TOUCH + V_TOUCH_TOL
    t = min(1.0, d / D_SLOW)
    lo = V_THRESH - V_THRESH_TOL + t * ((V_FINAL - V_FINAL_TOL) - (V_THRESH - V_THRESH_TOL))
    hi = V_THRESH + V_THRESH_TOL + t * ((V_FINAL + V_FINAL_TOL) - (V_THRESH + V_THRESH_TOL))
    return lo, hi


def start_point(nm, gs_deg=GS_DEG):
    """(lat, lon, alt_ft, true heading) on the glideslope `nm` miles out."""
    d = nm * 1852.0
    e, n = d * _AE, d * _AN
    lat = THR_LAT + n / 6_371_000 / math.radians(1)
    lon = THR_LON + e / (6_371_000 * math.cos(math.radians(THR_LAT))) / math.radians(1)
    alt_ft = FIELD_FT + TCH_FT + d * math.tan(math.radians(gs_deg)) / FT
    return lat, lon, alt_ft, math.degrees(COURSE) % 360


def v_ms(fdm):
    return max(fdm["velocities/vt-fps"] * FT, 20.0)


class ApproachCbf:
    def __init__(self):
        self.loops = InnerLoops()
        self.on = False
        self.clear = 1.0            # the sidecar reads this for the city-crash check; never a crash here
        self.geom = (0.0, 0.0, 0.0)
        self.eps = self.delta = 0.0
        self.band = (0.0, 0.0)
        self.active = ""

    def geometry(self, fdm):
        e, n = _enu(fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"])
        u = fdm["position/h-sl-meters"] - (FIELD_FT + TCH_FT) * FT
        d, y = e * _AE + n * _AN, e * _RE + n * _RN
        vn, ve, vd = (fdm[f"velocities/v-{a}-fps"] * FT for a in ("north", "east", "down"))
        return d, y, u, ve * _AE + vn * _AN, ve * _RE + vn * _RN, -vd

    def tick(self, fdm, pitch, roll, throttle, on, dt, kamikaze=False, hostile=False):
        """One tick. Sticks -1..1 (pitch + = back, roll + = right), throttle 0..1. Returns (elevator, aileron, throttle)."""
        self.on = on
        if hostile:                      # test pilot: nose down, left, idle
            pitch, roll, throttle = -0.5, -0.4, 0.0
        d, y, u, dd, yd, ud = self.geometry(fdm)
        self.geom = (d, y, u)
        self.eps = math.degrees(math.atan2(u, max(d, 1.0)))
        self.delta = math.degrees(math.atan2(y, max(d, 1.0)))
        gam = math.asin(max(-1.0, min(1.0, ud / max(fdm["velocities/vt-fps"] * FT, 1.0))))
        phi, p = fdm["attitude/phi-rad"], fdm["velocities/p-rad_sec"]
        cphi, cgam = max(math.cos(phi), 0.5), math.cos(gam)
        n_c = 1.0 + N_STICK * pitch
        p_c = K_PHI * (PHI_STICK * roll - phi)      # bank-angle stick, so letting go rolls out
        thr = throttle
        self.active = ""
        if on:
            # Vertical cone, relative degree 2 in load factor: h = r_max d - u (until the flare) and h = u - r_min d (until
            # the threshold, so the wheels cannot touch short: at d = 0 the floor is the 50 ft apex and the flare takes over).
            r_hi, r_lo = math.tan(math.radians(GS_DEG + GS_TOL_DEG)), math.tan(math.radians(GS_DEG - GS_TOL_DEG))
            n_hi, n_lo = 2.0, 0.0
            if d > D_FLARE:
                h, hd = r_hi * d - u, r_hi * dd - ud
                n_hi = (cgam + (K_V1 * hd + K_V2 * (hd + K_V1 * h)) / G) / cphi
            if d > 0.0:
                h, hd = u - r_lo * d, ud - r_lo * dd
                n_lo = (cgam - (K_V1 * hd + K_V2 * (hd + K_V1 * h)) / G) / cphi
            n_f = max(min(n_c, n_hi), n_lo)        # infeasible -> stay high
            if n_f != n_c:
                self.active += "n" + ("+" if n_f > n_c else "-")
            n_c = max(0.0, min(2.0, n_f))
            # Lateral cone, degree 3 in roll rate: h = y_max - y and h = y + y_max, y'' = g tan(phi), y''' = g sec^2(phi) p.
            s = math.tan(math.radians(LAT_TOL_DEG))
            ymax, ymaxd = (s * d, s * dd) if s * d > LAT_FLOOR else (LAT_FLOOR, 0.0)
            ydd = G * math.tan(phi)
            h, hd, hdd = ymax - y, ymaxd - yd, -ydd
            p_hi = math.cos(phi) ** 2 / G * (K_L1 * hdd + K_L2 * (hdd + K_L1 * hd) + K_L3 * (hdd + K_L1 * hd + K_L2 * (hd + K_L1 * h)))
            h, hd, hdd = y + ymax, yd + ymaxd, ydd
            p_lo = -math.cos(phi) ** 2 / G * (K_L1 * hdd + K_L2 * (hdd + K_L1 * hd) + K_L3 * (hdd + K_L1 * hd + K_L2 * (hd + K_L1 * h)))
            # Bank limit, degree 1.
            p_hi, p_lo = min(p_hi, K_PHI * (PHI_MAX - phi)), max(p_lo, -K_PHI * (PHI_MAX + phi))
            p_f = 0.5 * (p_hi + p_lo) if p_lo > p_hi else max(min(p_c, p_hi), p_lo)
            if abs(p_f - p_c) > 1e-6:
                self.active += " p" + ("+" if p_f > p_c else "-")
            p_c = p_f
            # Speed band. Thrust spools, T' = (K_T thr - T)/tau_T, so speed has relative degree 2 in throttle:
            # h = v - v_lo, h' = udot (measured), h'' = T'/m - g cos(gam) gam'. Throttle first; when it saturates,
            # the load factor takes the rest (a pull at full power still bleeds speed).
            if not fdm["gear/unit/WOW"]:
                v = fdm["velocities/vc-kts"]
                lo, hi = speed_band(d)
                self.band = (lo, hi)
                t_now = fdm["propulsion/engine/thrust-lbs"] * 4.448
                udot = fdm["accelerations/udot-ft_sec2"] * FT
                gdot = G / max(fdm["velocities/vt-fps"] * FT, 20.0) * (n_c * cphi - cgam)
                # need_lo: h'' must be at least this; need_hi: h'' of (v_hi - v) must be at least this.
                h, hd = (v - lo - V_MARGIN) * KT, udot
                need_lo = -(K_S1 * hd + K_S2 * (hd + K_S1 * h))
                h, hd = (hi - V_MARGIN - v) * KT, -udot
                need_hi = -(K_S1 * hd + K_S2 * (hd + K_S1 * h))
                thr_lo = (t_now + MASS * TAU_T * (need_lo + G * cgam * gdot)) / K_T
                thr_hi = (t_now - MASS * TAU_T * (need_hi - G * cgam * gdot)) / K_T
                if thr_lo > 1.0 and d > D_FLARE:      # full power is not enough: cap the pull (not in the flare: no nose-down near the ground)
                    n_cap = cgam / cphi + v_ms(fdm) * ((K_T - t_now) / (MASS * TAU_T) - need_lo) / (G * G * cgam * cphi)
                    if n_cap < n_c:
                        n_c, self.active = max(0.0, n_cap), self.active + " n-v"
                if thr_hi < 0.0:      # idle is not enough: make them pull
                    n_floor = cgam / cphi - v_ms(fdm) * ((t_now - 0.0) / (MASS * TAU_T) + need_hi) / (G * G * cgam * cphi)
                    if n_floor > n_c:
                        n_c, self.active = min(2.0, n_floor), self.active + " n+v"
                thr_f = max(0.0, min(1.0, max(min(thr, thr_hi), thr_lo)))   # infeasible -> fast, not slow
                if abs(thr_f - thr) > 1e-3:
                    self.active += " thr" + ("+" if thr_f > thr else "-")
                thr = thr_f
            # Flare barrier, degree 1 in load factor: h_b = u' + s(h_w) >= 0, s = min(cap, s0 + k h_w), h_b' = u'' + k u'.
            if not fdm["gear/unit/WOW"]:
                hw = max(fdm["position/h-agl-ft"] * FT - GEAR_H, 0.0)
                smax = SINK_MIN + SINK_K * hw
                smax_d = SINK_K * ud if smax < SINK_CAP else 0.0
                smax = min(SINK_CAP, smax)
                hb = ud + smax
                n_floor = (cgam + (-K_F * hb - smax_d) / G) / cphi
                if n_floor > n_c:
                    n_c, self.active = min(2.0, n_floor), self.active + " n+f"
        return self.loops.controls(fdm, n_c, -p_c, thr, dt)   # InnerLoops wants the crate's roll sign (+ = left)

    def status(self):
        d, y, u = self.geom
        lo, hi = self.band
        if d < D_FLARE:
            return f"gs {'ON ' if self.on else 'off'} FLARE {d:5.0f} m  band {lo:.0f}-{hi:.0f} kt" + (f"  [{self.active.strip()}]" if self.active.strip() else "")
        return (f"gs {'ON ' if self.on else 'off'} {d / 1852:4.2f} NM  elev {self.eps:4.2f} deg  lat {self.delta:+5.2f} deg  "
                f"band {lo:.0f}-{hi:.0f} kt" + (f"  [{self.active.strip()}]" if self.active.strip() else ""))

    def close(self):
        pass


def selftest():
    import jsbsim
    lat, lon, alt, hdg = start_point(2.0)
    assert abs(hdg - 322) < 1.0, hdg
    for pilot in ("benign", "hostile"):
        fdm = jsbsim.FGFDMExec(None)
        fdm.set_debug_level(0)
        fdm.load_model("c172p")
        fdm["ic/lat-geod-deg"], fdm["ic/long-gc-deg"], fdm["ic/h-sl-ft"] = lat, lon, alt
        fdm["ic/psi-true-deg"], fdm["ic/vc-kts"], fdm["ic/gamma-deg"] = hdg, 80, -3
        fdm["ic/terrain-elevation-ft"] = FIELD_FT
        fdm["propulsion/set-running"] = -1
        dt = 1 / 120
        fdm.set_dt(dt)
        fdm.run_ic()
        fdm["fcs/flap-cmd-norm"], fdm["fcs/mixture-cmd-norm"] = 0.67, 0.9
        fdm["simulation/do_simple_trim"] = 0
        thr0 = fdm["fcs/throttle-cmd-norm"]
        cbf = ApproachCbf()
        d, y, u, *_ = cbf.geometry(fdm)
        assert abs(math.degrees(math.atan2(u, d)) - 3) < 0.05 and abs(y) < 5, (d, y, u)
        worst = [0.0, 0.0, 0.0]
        t_sim, sink_td = 0.0, None
        while t_sim < 200:
            el, ai, th = cbf.tick(fdm, 0.0, 0.0, thr0, True, dt, hostile=(pilot == "hostile"))
            fdm["fcs/elevator-cmd-norm"], fdm["fcs/aileron-cmd-norm"], fdm["fcs/throttle-cmd-norm"] = el, ai, th
            fdm.run()
            t_sim += dt
            d, y, u = cbf.geom
            if fdm["gear/unit/WOW"]:
                sink_td = fdm["velocities/v-down-fps"] * FT
                break
            if d > D_FLARE:
                lo, hi = cbf.band
                v = fdm["velocities/vc-kts"]
                worst[0] = max(worst[0], abs(cbf.eps - GS_DEG))
                worst[1] = max(worst[1], abs(cbf.delta))
                worst[2] = max(worst[2], lo - v, v - hi)
        v_td = fdm["velocities/vc-kts"]
        print(f"{pilot:7s}: cone max |elev-3| {worst[0]:.2f} deg, max |lat| {worst[1]:.2f} deg, speed excursion {worst[2]:.1f} kt;  "
              f"touchdown {'none' if sink_td is None else f'{sink_td * 196.85:.0f} ft/min at {v_td:.0f} kt, {-d:+.0f} m past the threshold, {y:+.1f} m off centre'}")
        assert worst[0] < GS_TOL_DEG + 0.2 and worst[1] < LAT_TOL_DEG + 0.2 and worst[2] < 3.0, worst
        assert sink_td is not None and sink_td < 1.5 and abs(y) < HALF_WIDTH and 55 < v_td < 72, (sink_td, y, v_td)
    print("approach_cbf selftest ok")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
