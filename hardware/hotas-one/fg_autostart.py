"""Start the FlightGear c172p engine over the telnet property server (no Nasal needed).

Replays the aircraft's own Autostart sequence (Aircraft/c172p/Nasal/c172p.nas) as property writes.
usage: python3 -I fg_autostart.py [--port 5401] [--wait SECONDS]
"""
import argparse
import socket
import sys
import time


def connect(port, wait):
    end = time.monotonic() + wait
    while True:
        try:
            s = socket.create_connection(("127.0.0.1", port), timeout=8)
            time.sleep(0.3)
            s.sendall(b"data\r\n")
            time.sleep(0.2)
            return s
        except OSError:
            if time.monotonic() > end:
                sys.exit(f"FlightGear telnet server not reachable on port {port}")
            time.sleep(2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=5401)
    ap.add_argument("--wait", type=float, default=600, help="seconds to wait for FlightGear to come up")
    args = ap.parse_args()
    s = connect(args.port, args.wait)

    def cmd(c, wait=0.12):
        s.sendall((c + "\r\n").encode())
        time.sleep(wait)
        s.settimeout(0.4)
        out = b""
        try:
            while True:
                ch = s.recv(65536)
                if not ch:
                    break
                out += ch
        except socket.timeout:
            pass
        return out.decode(errors="replace").strip()

    # The FDM publishes its properties a while after the telnet port opens.
    end = time.monotonic() + args.wait
    while cmd("get /sim/fdm-initialized") != "true":
        if time.monotonic() > end:
            sys.exit("FDM never initialized")
        time.sleep(2)
    if cmd("get /engines/active-engine/running") == "true":
        print("engine already running")
        return
    mix = cmd("get /fdm/jsbsim/engine/auto-mixture") or "1.0"
    for p, v in [("/fdm/jsbsim/damage/repairing", "0"), ("/controls/switches/magnetos", "3"),
                 ("/controls/engines/engine[0]/throttle", "0.2"), ("/controls/engines/current-engine/mixture", mix),
                 ("/controls/engines/engine[0]/mixture", mix), ("/controls/switches/master-bat", "1"),
                 ("/controls/switches/master-alt", "1"), ("/controls/switches/master-avionics", "1"),
                 ("/controls/flight/flaps", "0"), ("/sim/model/c172p/cockpit/control-lock-placed", "0"),
                 ("/controls/gear/brake-parking", "0"), ("/sim/model/c172p/securing/chock", "0"),
                 ("/engines/active-engine/carb_ice", "0"), ("/consumables/fuel/tank[0]/selected", "1"),
                 ("/consumables/fuel/tank[1]/selected", "1"), ("/controls/fuel/tank-selector", "2"),
                 ("/controls/engines/engine[0]/primer-lever", "0"), ("/controls/engines/engine/primer", "3"),
                 ("/controls/switches/starter", "1"), ("/engines/active-engine/auto-start", "1")]:
        cmd(f"set {p} {v}")
    for _ in range(10):
        time.sleep(1)
        if cmd("get /engines/active-engine/running") == "true":
            break
    cmd("set /controls/switches/starter 0")
    cmd("set /engines/active-engine/auto-start 0")
    time.sleep(1)
    print("engine running:", cmd("get /engines/active-engine/running"), "rpm:", cmd("get /engines/engine/rpm"))


if __name__ == "__main__":
    main()
