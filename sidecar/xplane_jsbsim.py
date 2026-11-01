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
}


def gauge_packets(fdm):
    for dref, prop in GAUGES.items():
        v = fdm[prop]
        if prop == "velocities/v-down-fps":
            v = -v * 60
        elif dref.startswith("sim/flightmodel/engine/ENGN_tacrad"):
            v = v * 0.10472
        yield dref_set(dref, v)


def deadzone(v, dz):
    """Zero inside the dead zone, then rescale so the full travel still reaches 1."""
    return 0.0 if abs(v) < dz else (abs(v) - dz) / (1 - dz) * (1 if v > 0 else -1)


def selftest():
    assert deadzone(0.1, 0.15) == 0 and deadzone(1.0, 0.15) == 1 and abs(deadzone(-0.575, 0.15) + 0.5) < 1e-9
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
    assert struct.unpack_from("<f", pk[3], 5)[0] == 600.0      # 10 ft/s up = 600 fpm
    assert abs(struct.unpack_from("<f", pk[-1], 5)[0] - 251.3) < 0.1  # 2400 rpm in rad/s
    print("selftest ok")


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
    if args.viewer == "xplane":
        lat, lon, ele, psi, agl = wait_for_pose(sock, xp, vals)
        print(f"X-Plane aircraft at {lat:.5f} {lon:.5f}  {ele:.0f} m MSL  hdg {psi:.0f}  agl {agl:.1f} m")
    else:
        lat, lon, ele, psi, agl = 37.46358, -122.11749, 2.0, 142.0, 0.0   # KPAO runway 13
    hotas = None
    if args.pilot == "hid":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I drops the script dir
        from hotas_hid import Hotas
        hotas = Hotas()

    fdm = jsbsim.FGFDMExec(None)
    fdm.set_debug_level(0)
    fdm.load_model(args.model)
    fdm["ic/lat-geod-deg"] = lat
    fdm["ic/long-gc-deg"] = lon
    fdm["ic/terrain-elevation-ft"] = (ele - agl) * M2FT
    fdm["ic/h-agl-ft"] = 4.0           # JSBSim settles the gear onto the terrain from here
    fdm["ic/psi-true-deg"] = psi
    fdm["ic/vc-kts"] = 0.0
    dt = 1.0 / 120
    fdm.set_dt(dt)
    fdm.run_ic()
    fdm["fcs/mixture-cmd-norm"] = 0.9
    fdm["fcs/advance-cmd-norm"] = 1.0   # prop full fine (constant-speed models)
    # The c182 ignores propulsion/set-running; crank it like a pilot would, brakes on,
    # throttle open (it does not catch at idle), then hand the throttle to the pilot.
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
    print(f"flying {args.model} under JSBSim at {args.hz} Hz; Ctrl-C hands X-Plane its physics back")

    if args.viewer == "xplane":
        sock.sendto(dref_set("sim/operation/override/override_engines", 1.0), xp)  # lets ENGN_tacrad stick
    frame = 1.0 / args.hz
    next_t = time.monotonic()
    last_print = 0.0
    try:
        while True:
            while select.select([sock], [], [], 0)[0]:
                rref_parse(sock.recv(4096), vals)
            if hotas:
                pitch, roll, yaw, thr = hotas.poll()
            else:
                pitch, roll, yaw, thr = (vals.get(pilot_base + i, 0.0) for i in range(4))
            pitch, roll, yaw = deadzone(pitch, 0.1), deadzone(roll, 0.1), deadzone(yaw, 0.15)
            if fdm["gear/unit/WOW"]:
                yaw *= 0.5   # ponytail: nosewheel gain; a twist grip at taxi speed loops the plane otherwise
            fdm["fcs/elevator-cmd-norm"] = -pitch   # X-Plane +1 = stick back, JSBSim +1 = elevator down
            fdm["fcs/aileron-cmd-norm"] = roll
            fdm["fcs/rudder-cmd-norm"] = yaw
            fdm["fcs/throttle-cmd-norm"] = thr
            for _ in range(sub):
                fdm.run()
            if args.viewer == "xplane":
                sock.sendto(vehx(fdm["position/lat-geod-deg"], fdm["position/long-gc-deg"],
                                 fdm["position/h-sl-meters"], fdm["attitude/psi-deg"],
                                 fdm["attitude/theta-deg"], fdm["attitude/phi-deg"]), xp)
                for pk in gauge_packets(fdm):
                    sock.sendto(pk, xp)
            now = time.monotonic()
            if now - last_print >= 1.0:
                last_print = now
                print(f"t={fdm.get_sim_time():6.1f}s  {fdm['velocities/vc-kts']:5.1f} kt  "
                      f"{fdm['position/h-agl-ft']:6.0f} ft AGL  pitch {fdm['attitude/theta-deg']:5.1f}  "
                      f"roll {fdm['attitude/phi-deg']:5.1f}  rpm {fdm['propulsion/engine/engine-rpm']:4.0f}  "
                      f"hdg {fdm['attitude/psi-deg']:3.0f}  thr {thr:.2f} stick {pitch:+.2f} roll {roll:+.2f} "
                      f"yaw {yaw:+.2f} wow {fdm['gear/unit/WOW']:.0f}", flush=True)
            next_t += frame
            time.sleep(max(0.0, next_t - now))  # ponytail: wall-clock pacing, no record logging yet
    except KeyboardInterrupt:
        pass
    finally:
        if args.viewer == "xplane":
            for i in range(len(PILOT)):
                sock.sendto(rref_request(pilot_base + i, PILOT[i], 0), xp)
            sock.sendto(dref_set("sim/operation/override/override_planepath[0]", 0.0), xp)
            sock.sendto(dref_set("sim/operation/override/override_engines", 0.0), xp)
            print("\nX-Plane physics re-enabled")


if __name__ == "__main__":
    main()
