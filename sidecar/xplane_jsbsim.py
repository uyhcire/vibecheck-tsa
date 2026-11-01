"""JSBSim flies, X-Plane 12 displays.

Runs a JSBSim model in real time, reads the pilot's stick and throttle back out
of X-Plane over UDP (so a joystick set up in X-Plane just works), and pushes the
aircraft pose to X-Plane with VEHX packets, which switches X-Plane's own flight
model off for the user aircraft. Packet layouts are from
"<X-Plane 12>/Instructions/Exchanging Data with X-Plane.rtfd".

usage: .venv/bin/python -I sidecar/xplane_jsbsim.py [--model c172p] [--pilot hid|xplane] [--viewer xplane|none]
       .venv/bin/python -I sidecar/xplane_jsbsim.py --selftest
"""
import argparse
import json
import os
import select
import signal
import socket
import struct
import sys
import time

XP_PORT = 49000
M2FT = 3.280839895
PILOT = [
    "sim/joystick/yoke_pitch_ratio",                   # +1 = stick back
    "sim/joystick/yoke_roll_ratio",                    # +1 = stick right
    "sim/joystick/yoke_heading_ratio",                 # +1 = right rudder
    "sim/cockpit2/engine/actuators/throttle_ratio_all",  # 0..1
]
POSE = [
    "sim/flightmodel/position/latitude",
    "sim/flightmodel/position/longitude",
    "sim/flightmodel/position/elevation",   # m MSL
    "sim/flightmodel/position/psi",         # deg true
    "sim/flightmodel/position/y_agl",       # m
]


def rref_request(idx, name, freq):
    """RREF: ask X-Plane to send dataref `name` `freq` times a second, tagged `idx`."""
    return b"RREF\0" + struct.pack("<ii", freq, idx) + name.encode().ljust(400, b"\0")


def rref_parse(data, into):
    """Unpack one RREF reply packet (header + repeated int index, float value) into `into`."""
    if data[:4] != b"RREF":
        return
    for off in range(5, len(data) - 7, 8):
        idx, val = struct.unpack_from("<if", data, off)
        into[idx] = val


def vehx(lat, lon, ele_m, psi, theta, phi):
    """VEHX: place the user aircraft (index 0) and stop X-Plane's flight model."""
    return b"VEHX\0" + struct.pack("<idddfff", 0, lat, lon, ele_m, psi, theta, phi)


def dref_set(name, value):
    """DREF: write one float dataref."""
    return b"DREF\0" + struct.pack("<f", value) + name.encode().ljust(500, b"\0")


# Pilot-side gauges X-Plane lets us write while its flight model is overridden.
GAUGES = {
    "sim/cockpit2/gauges/indicators/airspeed_kts_pilot": "velocities/vc-kts",
    "sim/flightmodel/position/indicated_airspeed": "velocities/vc-kts",
    "sim/cockpit2/gauges/indicators/altitude_ft_pilot": "position/h-sl-ft",
    "sim/cockpit2/gauges/indicators/vvi_fpm_pilot": "velocities/v-down-fps",   # negated below
    "sim/flightmodel/position/vh_ind_fpm": "velocities/v-down-fps",
    "sim/cockpit2/gauges/indicators/pitch_AHARS_deg_pilot": "attitude/theta-deg",
    "sim/cockpit2/gauges/indicators/roll_AHARS_deg_pilot": "attitude/phi-deg",
    "sim/cockpit2/gauges/indicators/heading_AHARS_deg_mag_pilot": "attitude/psi-deg",
    "sim/cockpit2/engine/indicators/MPR_in_hg[0]": "propulsion/engine/map-inhg",
    "sim/flightmodel/engine/ENGN_tacrad[0]": "propulsion/engine/engine-rpm",  # rad/s, scaled below
    "sim/flightmodel/engine/ENGN_power[0]": "propulsion/engine/power-hp",     # W, scaled below
    "sim/cockpit2/engine/indicators/fuel_flow_kg_sec[0]": "propulsion/engine/fuel-flow-rate-pps",
}
RATED_HP = {"c172p": 160, "c172r": 160, "c172x": 160, "c182": 230, "pa28": 160}

# Towers from "X-Plane Landmarks - San Francisco" (placements decoded from its DSF, sizes from the .obj files):
# name, lat, lon, radius m (half-diagonal of the footprint), height m above its base.
OBSTACLES = [
    ("Salesforce Tower", 37.789774, -122.396925, 38.0, 327.5),
    ("Transamerica Pyramid", 37.795166, -122.402785, 38.0, 260.0),
    ("Coit Tower", 37.802469, -122.405934, 20.0, 66.0),
]
# Fallback when sf_buildings.json (OpenStreetMap footprints, see fetch_osm_buildings.py) is missing.
BUILDINGS_JSON = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sf_buildings.json")


class Buildings:
    """Building footprints with heights; point-in-polygon on lat/lon with a bounding-box prefilter."""

    def __init__(self, path=BUILDINGS_JSON):
        self.items = []   # (name, height_m, polygon, (minlat, minlon, maxlat, maxlon), (clat, clon))
        if os.path.exists(path):
            for b in json.load(open(path))["buildings"]:
                poly = b["polygon"]
                lats, lons = [q[0] for q in poly], [q[1] for q in poly]
                self.items.append((b["name"], b["height_m"], poly, (min(lats), min(lons), max(lats), max(lons)),
                                   (sum(lats) / len(lats), sum(lons) / len(lons))))

    @staticmethod
    def inside(poly, lat, lon):
        hit = False
        j = len(poly) - 1
        for i in range(len(poly)):
            (lat_i, lon_i), (lat_j, lon_j) = poly[i], poly[j]
            if (lon_i > lon) != (lon_j > lon) and lat < (lat_j - lat_i) * (lon - lon_i) / (lon_j - lon_i) + lat_i:
                hit = not hit
            j = i
        return hit

    def hit(self, lat, lon, agl_m):
        """Name of the building whose footprint and height contain this point, else None."""
        if not self.items:
            return hit_obstacle(lat, lon, agl_m)
        for name, h, poly, (a, b, c, d), _ in self.items:
            if a <= lat <= c and b <= lon <= d and agl_m <= h and self.inside(poly, lat, lon):
                return name
        return None

    def nearest(self, lat, lon):
        """(name, distance m, height m) of the closest building centroid."""
        best = None
        for name, h, _, _, (clat, clon) in self.items:
            d = ((lat - clat) * 111_200.0) ** 2 + ((lon - clon) * 111_200.0 * 0.791) ** 2
            if best is None or d < best[1]:
                best = (name, d, h)
        return (best[0], best[1] ** 0.5, best[2]) if best else None


def hit_obstacle(lat, lon, agl_m):
    """Landmark fallback: name of the tower whose footprint and height contain this point, else None."""
    for name, olat, olon, r, h in OBSTACLES:
        dn = (lat - olat) * 111_200.0
        de = (lon - olon) * 111_200.0 * 0.791   # cos(37.8 deg)
        if dn * dn + de * de <= r * r and agl_m <= h:
            return name
    return None


# Airborne start states: lat, lon, true heading, altitude ft MSL, knots, flight-path angle deg, flaps 0..1.
# KPAO runway 31 threshold is ~37.4583,-122.1123 (heading 322 true); 3 NM out on the 142 radial, 3 deg slope.
SCENARIOS = {
    "final-kpao31": dict(lat=37.4189, lon=-122.0735, hdg=322.0, alt_ft=1000.0, kts=75.0, gamma=-3.0, flaps=0.33,
                         terrain_ft=7.0, note="3 NM final to Palo Alto runway 31, flaps 10, on a 3 deg slope"),
    "sf-downtown": dict(lat=37.792049, lon=-122.374326, hdg=262.0, alt_ft=600.0, kts=100.0, gamma=0.0, flaps=0.0,
                        terrain_ft=0.0, note="over the Bay 1.1 NM east of downtown San Francisco, pointed at the Salesforce Tower at 600 ft"),
}


def gauge_packets(fdm):
    for dref, prop in GAUGES.items():
        v = fdm[prop]
        if prop == "velocities/v-down-fps":
            v = -v * 60
        elif dref.startswith("sim/flightmodel/engine/ENGN_tacrad"):
            v = v * 0.10472
        elif dref.startswith("sim/flightmodel/engine/ENGN_power"):
            v = v * 745.7
        elif dref.endswith("fuel_flow_kg_sec[0]"):
            v = v * 0.4536
        yield dref_set(dref, v)


def deadzone(v, dz):
    """Zero inside the dead zone, then rescale so the full travel still reaches 1."""
    return 0.0 if abs(v) < dz else (abs(v) - dz) / (1 - dz) * (1 if v > 0 else -1)


def selftest():
    assert deadzone(0.1, 0.15) == 0 and deadzone(1.0, 0.15) == 1 and abs(deadzone(-0.575, 0.15) + 0.5) < 1e-9
    assert hit_obstacle(37.789774, -122.396925, 100) == "Salesforce Tower"
    assert hit_obstacle(37.789774, -122.396925, 400) is None          # above the roof
    assert hit_obstacle(37.7920, -122.3650, 100) is None              # over the Bay
    bl = Buildings()
    if bl.items:
        assert bl.hit(37.789774, -122.396925, 100) == "Salesforce Tower"
        assert bl.hit(37.789774, -122.396925, 400) is None
        assert bl.hit(37.7920, -122.3650, 100) is None
        t0 = time.perf_counter()
        for _ in range(600):
            bl.hit(37.7905, -122.3990, 50)
        print(f"{len(bl.items)} buildings loaded; hit test {1000 * (time.perf_counter() - t0) / 600:.2f} ms each")
    p = vehx(47.79, 13.0, 430.5, 150.0, 2.5, -1.0)
    assert len(p) == 5 + 4 + 24 + 12
    assert struct.unpack_from("<idddfff", p, 5)[:4] == (0, 47.79, 13.0, 430.5)
    got = {}
    rref_parse(b"RREF," + struct.pack("<if", 3, 0.25) + struct.pack("<if", 7, -1.0), got)
    assert got == {3: 0.25, 7: -1.0}
    assert len(rref_request(1, "sim/x", 60)) == 5 + 8 + 400
    assert len(dref_set("sim/x", 0.0)) == 5 + 4 + 500
    fake = {v: 1.0 for v in GAUGES.values()}   # gauge_packets only needs fdm[prop]
    fake.update({"velocities/v-down-fps": -10.0, "propulsion/engine/engine-rpm": 2400.0})
    pk = list(gauge_packets(fake))
    assert len(pk) == len(GAUGES)
    by = {d: struct.unpack_from("<f", k, 5)[0] for d, k in zip(GAUGES, pk)}
    assert by["sim/cockpit2/gauges/indicators/vvi_fpm_pilot"] == 600.0        # 10 ft/s up = 600 fpm
    assert abs(by["sim/flightmodel/engine/ENGN_tacrad[0]"] - 251.3) < 0.1   # 2400 rpm in rad/s
    assert abs(by["sim/flightmodel/engine/ENGN_power[0]"] - 745.7) < 0.1    # 1 hp
    print("selftest ok")


def crashed(fdm, vals, AGL, ELE, have_xplane, buildings):
    """Why the flight just ended, or None: a tower, X-Plane's terrain, or a touchdown that is too hard."""
    lat, lon = fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"]
    if have_xplane and AGL in vals and ELE in vals:
        agl_m = fdm["position/h-sl-meters"] - (vals[ELE] - vals[AGL])   # our altitude over X-Plane's ground
    else:
        agl_m = fdm["position/h-agl-ft"] / M2FT
    name = buildings.hit(lat, lon, agl_m)
    if name:
        return f"hit the {name}"
    vdown_fps = fdm["velocities/v-down-fps"]
    if have_xplane and agl_m < 0.0 and fdm["velocities/vc-kts"] > 20:
        return "flew into the terrain"
    if fdm["gear/unit/WOW"] and vdown_fps > 10.0:
        return f"hit the ground at {vdown_fps * 60:.0f} ft/min"
    return None


def hand_back_crashing(sock, xp, fdm):
    """Give X-Plane its physics back right here, moving fast and nose down, so its damage model breaks the plane."""
    vn, ve, vd = (fdm[f"velocities/v-{d}-fps"] / M2FT for d in ("north", "east", "down"))
    for _ in range(3):
        sock.sendto(dref_set("sim/flightmodel/position/local_vx", ve), xp)     # OpenGL: x east
        sock.sendto(dref_set("sim/flightmodel/position/local_vz", -vn), xp)    # z south
        sock.sendto(dref_set("sim/flightmodel/position/local_vy", -max(30.0, vd)), xp)  # y up: slam it down
        time.sleep(0.02)
    sock.sendto(dref_set("sim/operation/override/override_planepath[0]", 0.0), xp)
    sock.sendto(dref_set("sim/operation/override/override_engines", 0.0), xp)


def wait_for_pose(sock, xp, vals, timeout=5.0):
    for i, n in enumerate(POSE):
        sock.sendto(rref_request(i, n, 5), xp)
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline and not all(i in vals for i in range(len(POSE))):
        if select.select([sock], [], [], 0.2)[0]:
            rref_parse(sock.recv(4096), vals)
    for i, n in enumerate(POSE):
        sock.sendto(rref_request(i, n, 0), xp)
    if not all(i in vals for i in range(len(POSE))):
        sys.exit(f"no answer from X-Plane at {xp[0]}:{xp[1]} (is a flight loaded?)")
    return [vals[i] for i in range(len(POSE))]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--model", default="c172p",
                    help="JSBSim aircraft (default c172p: tracks straight on the ground; c182 and pa28 ground-loop)")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--hz", type=int, default=60, help="frames per second sent to X-Plane")
    ap.add_argument("--pilot", choices=["hid", "xplane"], default="hid",
                    help="hid: read the HOTAS directly (macOS); xplane: X-Plane joystick datarefs")
    ap.add_argument("--viewer", choices=["xplane", "none"], default="xplane",
                    help="none: run JSBSim alone and just print the status line")
    ap.add_argument("--at", metavar="LAT,LON,HDG[,ELEV_M]",
                    help="start here on the ground instead of where X-Plane's aircraft is (e.g. KPAO rwy 13: "
                         "37.46358,-122.11749,142,2)")
    ap.add_argument("--scenario", choices=sorted(SCENARIOS), help="airborne start: " + "; ".join(f"{k}: {v['note']}" for k, v in SCENARIOS.items()))
    ap.add_argument("--filter", choices=["none", "bcbf"], default="none",
                    help="bcbf: guard the pilot with the bcbf-city-flight backup CBF (flight/target/release/filterd)")
    ap.add_argument("--filter-on", action="store_true", help="start with the filter active")
    ap.add_argument("--toggle-button", type=int, default=2, help="HOTAS button that toggles the filter (1 = trigger)")
    ap.add_argument("--kamikaze-button", type=int, default=3, help="HOTAS button that toggles the kamikaze autopilot")
    ap.add_argument("--kamikaze", action="store_true", help="start with the kamikaze autopilot flying (tests)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt))

    import jsbsim

    xp = (args.host, XP_PORT)
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("", 0))
    vals = {}
    sc = SCENARIOS.get(args.scenario)
    if sc:
        lat, lon, psi, ele, agl = sc["lat"], sc["lon"], sc["hdg"], sc["alt_ft"] / M2FT, (sc["alt_ft"] - sc["terrain_ft"]) / M2FT
    elif args.at:
        parts = [float(x) for x in args.at.split(",")]
        lat, lon, psi = parts[:3]
        ele, agl = (parts[3] if len(parts) > 3 else 2.0), 0.0
    elif args.viewer == "xplane":
        lat, lon, ele, psi, agl = wait_for_pose(sock, xp, vals)
        print(f"X-Plane aircraft at {lat:.5f} {lon:.5f}  {ele:.0f} m MSL  hdg {psi:.0f}  agl {agl:.1f} m")
    else:
        lat, lon, ele, psi, agl = 37.46358, -122.11749, 2.0, 142.0, 0.0   # KPAO runway 13
    bcbf = None
    if args.filter == "bcbf":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I drops the script dir
        from bcbf import Bcbf
        bcbf = Bcbf()
        bcbf_on = args.filter_on
        kamikaze = args.kamikaze
        print(f"backup CBF loaded; button {args.toggle_button} toggles it (starts {'ON' if bcbf_on else 'off'})")
    buildings = Buildings()
    print(f"{len(buildings.items)} building footprints loaded" if buildings.items else "no sf_buildings.json: landmark towers only")
    hotas = None
    trim_thr = 0.0
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I drops the script dir
    if args.pilot == "hid":
        from hotas_hid import Hotas
        hotas = Hotas()

    fdm = jsbsim.FGFDMExec(None)
    fdm.set_debug_level(0)
    fdm.load_model(args.model)
    fdm["ic/lat-geod-deg"] = lat
    fdm["ic/long-gc-deg"] = lon
    fdm["ic/terrain-elevation-ft"] = (ele - agl) * M2FT
    fdm["ic/psi-true-deg"] = psi
    if sc:
        fdm["ic/h-sl-ft"] = sc["alt_ft"]
        fdm["ic/vc-kts"] = sc["kts"]
        fdm["ic/gamma-deg"] = sc["gamma"]
    else:
        fdm["ic/h-agl-ft"] = 4.0       # JSBSim settles the gear onto the terrain from here
        fdm["ic/vc-kts"] = 0.0
    dt = 1.0 / 120
    fdm.set_dt(dt)
    if sc:
        fdm["propulsion/set-running"] = -1   # airborne: engine already running (works for the c172p)
    fdm.run_ic()
    if sc:
        fdm["fcs/flap-cmd-norm"] = sc["flaps"]
        fdm["fcs/mixture-cmd-norm"] = 0.9
        fdm["simulation/do_simple_trim"] = 0   # longitudinal trim: pitch trim + throttle for this speed and slope
        for _ in range(int(1 / dt)):
            fdm.run()
        print(f"scenario {args.scenario}: {sc['note']}")
        trim_thr = fdm["fcs/throttle-cmd-norm"]
        print(f"trimmed: throttle {100 * fdm['fcs/throttle-cmd-norm']:.0f}% (set your lever near this), "
              f"pitch trim {fdm['fcs/pitch-trim-cmd-norm']:+.2f}")
    fdm["fcs/mixture-cmd-norm"] = 0.9
    fdm["fcs/advance-cmd-norm"] = 1.0   # prop full fine (constant-speed models)
    if not sc:
        # Ground start. The c182 ignores propulsion/set-running; crank it like a pilot would,
        # brakes on, throttle open (it does not catch at idle), then hand the throttle over.
        for b in ("left", "right", "center"):
            fdm[f"fcs/{b}-brake-cmd-norm"] = 1.0
        fdm["fcs/throttle-cmd-norm"] = 1.0
        fdm["propulsion/magneto_cmd"] = 3
        fdm["propulsion/starter_cmd"] = 1
        for _ in range(int(3 / dt)):
            fdm.run()
        fdm["propulsion/starter_cmd"] = 0
        for b in ("left", "right", "center"):
            fdm[f"fcs/{b}-brake-cmd-norm"] = 0.0
    sub = max(1, round(1.0 / (args.hz * dt)))

    pilot_base = len(POSE)
    if args.pilot == "xplane":
        for i, n in enumerate(PILOT):
            sock.sendto(rref_request(pilot_base + i, n, args.hz), xp)
    AGL, ELE = 20, 21   # X-Plane's terrain under the plane, used for crashes (hills JSBSim does not know)
    if args.viewer == "xplane":
        sock.sendto(rref_request(AGL, "sim/flightmodel/position/y_agl", 20), xp)
        sock.sendto(rref_request(ELE, "sim/flightmodel/position/elevation", 20), xp)
    print(f"flying {args.model} under JSBSim at {args.hz} Hz; Ctrl-C hands X-Plane its physics back")

    if args.viewer == "xplane":
        sock.sendto(dref_set("sim/operation/override/override_engines", 1.0), xp)  # lets ENGN_tacrad stick
    frame = 1.0 / args.hz
    last_buttons = 0
    next_t = time.monotonic()
    last_print = 0.0
    try:
        while True:
            while select.select([sock], [], [], 0)[0]:
                rref_parse(sock.recv(4096), vals)
            if hotas:
                pitch, roll, yaw, thr = hotas.poll()
            else:
                pitch, roll, yaw = (vals.get(pilot_base + i, 0.0) for i in range(3))
                thr = vals.get(pilot_base + 3, trim_thr)
            pitch, roll, yaw = deadzone(pitch, 0.1), deadzone(roll, 0.1), deadzone(yaw, 0.15)
            if fdm["gear/unit/WOW"]:
                yaw *= 0.5   # ponytail: nosewheel gain; a twist grip at taxi speed loops the plane otherwise
            if bcbf:
                pressed = hotas.buttons if hotas else 0
                if pressed & ~last_buttons & (1 << (args.toggle_button - 1)):
                    bcbf_on = not bcbf_on
                    print(f"\n*** BACKUP CBF {'ON' if bcbf_on else 'OFF'} ***", flush=True)
                if pressed & ~last_buttons & (1 << (args.kamikaze_button - 1)):
                    kamikaze = not kamikaze
                    print(f"\n*** KAMIKAZE AUTOPILOT {'ON' if kamikaze else 'OFF'} ***", flush=True)
                last_buttons = pressed
                el, ai, th = bcbf.tick(fdm, pitch, roll, thr, bcbf_on, frame, kamikaze)
                fdm["fcs/elevator-cmd-norm"], fdm["fcs/aileron-cmd-norm"], fdm["fcs/throttle-cmd-norm"] = el, ai, th
                fdm["fcs/rudder-cmd-norm"] = -yaw
            else:
                fdm["fcs/elevator-cmd-norm"] = -pitch   # X-Plane +1 = stick back, JSBSim +1 = elevator down
                fdm["fcs/aileron-cmd-norm"] = roll
                fdm["fcs/rudder-cmd-norm"] = -yaw   # twist right must yaw right; JSBSim's sign is the other way
                fdm["fcs/throttle-cmd-norm"] = thr
            for _ in range(sub):
                fdm.run()
            if args.viewer == "xplane":
                sock.sendto(vehx(fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"],
                                 fdm["position/h-sl-meters"], fdm["attitude/psi-deg"],
                                 fdm["attitude/theta-deg"], fdm["attitude/phi-deg"]), xp)
                for pk in gauge_packets(fdm):
                    sock.sendto(pk, xp)
                sock.sendto(dref_set("sim/cockpit2/engine/actuators/throttle_ratio[0]", thr), xp)  # cockpit lever
            why = crashed(fdm, vals, AGL, ELE, args.viewer == "xplane", buildings)
            if bcbf and bcbf.clear < 0 and not why:
                why = "hit the city (bcbf world)"
            if why:
                print(f"\nCRASHED: {why} at {fdm['velocities/vc-kts']:.0f} kt")
                if args.viewer == "xplane":
                    hand_back_crashing(sock, xp, fdm)
                return
            now = time.monotonic()
            if now - last_print >= 1.0:
                last_print = now
                print(f"t={fdm.get_sim_time():6.1f}s  {fdm['velocities/vc-kts']:5.1f} kt  "
                      f"{fdm['position/h-agl-ft']:6.0f} ft AGL  pitch {fdm['attitude/theta-deg']:5.1f}  "
                      f"roll {fdm['attitude/phi-deg']:5.1f}  rpm {fdm['propulsion/engine/engine-rpm']:4.0f}  "
                      f"pwr {fdm['propulsion/engine/power-hp']:3.0f}hp "
                      f"{100 * fdm['propulsion/engine/power-hp'] / RATED_HP.get(args.model, 160):3.0f}%  "
                      f"hdg {fdm['attitude/psi-deg']:3.0f}  thr {thr:.2f} stick {pitch:+.2f} roll {roll:+.2f} "
                      f"yaw {yaw:+.2f} wow {fdm['gear/unit/WOW']:.0f}"
                      + (f"  {bcbf.status()}" if bcbf else "")
                      + (f"  near: {nb[0]} {nb[1]:.0f} m, {nb[2]:.0f} m tall" if (nb := buildings.nearest(
                          fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"])) and nb[1] < 400 else ""), flush=True)
            next_t += frame
            time.sleep(max(0.0, next_t - now))  # ponytail: wall-clock pacing, no record logging yet
    except KeyboardInterrupt:
        pass
    finally:
        if bcbf:
            bcbf.close()
        if args.viewer == "xplane":
            for i in range(len(PILOT)):
                sock.sendto(rref_request(pilot_base + i, PILOT[i], 0), xp)
            sock.sendto(dref_set("sim/operation/override/override_planepath[0]", 0.0), xp)
            sock.sendto(dref_set("sim/operation/override/override_engines", 0.0), xp)
            print("\nX-Plane physics re-enabled")


if __name__ == "__main__":
    main()
