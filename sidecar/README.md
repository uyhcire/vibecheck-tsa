# Sidecar: JSBSim flies, X-Plane 12 displays

`xplane_jsbsim.py` is the first piece of the sidecar sketched in `docs/filter-interface.md`: JSBSim owns the physics, the viewer only renders. Here the viewer is X-Plane 12 and the pilot is a Thrustmaster T.Flight HOTAS One read straight over HID (`hotas_hid.py`, macOS, no packages).

```
python3 -m venv .venv && .venv/bin/pip install -r sysid/requirements.txt
.venv/bin/python -I sidecar/xplane_jsbsim.py            # c172p, HOTAS over HID, X-Plane on this machine
.venv/bin/python -I sidecar/xplane_jsbsim.py --viewer none        # JSBSim alone, status line only
.venv/bin/python -I sidecar/xplane_jsbsim.py --pilot xplane --host 192.168.1.20   # stick via X-Plane datarefs
.venv/bin/python -I sidecar/xplane_jsbsim.py --selftest  # packet layouts
```

Start X-Plane first with a flight loaded on a runway (the Cirrus SR22 looks the part). The sidecar:

1. asks X-Plane for the aircraft's position and heading (`RREF` on `sim/flightmodel/position/*`) and starts JSBSim there, on the ground, engine running;
2. reads the HOTAS (stick pitch/roll, twist = rudder and nosewheel, lever = throttle) with a 10% dead zone, nosewheel gain halved on the ground;
3. every frame runs JSBSim, sends one `VEHX` packet (lat, lon, elevation, heading, pitch, roll) and writes the pilot-side gauges (`sim/cockpit2/gauges/indicators/*_pilot`: airspeed, altitude, VSI, attitude, heading) plus engine RPM and manifold pressure, so the panel follows JSBSim. The first `VEHX` stops X-Plane's own flight model for the user aircraft.

`--pilot xplane` instead subscribes to `sim/joystick/yoke_*_ratio` and the throttle actuator dataref. In testing X-Plane stopped updating those once its flight model was overridden, hence the HID default.

Ctrl-C (or SIGTERM) clears `sim/operation/override/override_planepath[0]` and `override_engines` so X-Plane's physics takes over again from wherever JSBSim left the plane.

## Which JSBSim model

X-Plane's SR22: 2300 lb empty, 3600 lb max, 310 hp injected piston, constant-speed prop, low wing, fixed gear, Vne 205 kt. On paper JSBSim 1.3.3's **c182** (230 hp, constant-speed prop, 2950 lb) is the closest stock single. On the ground it is not usable from a stick: with zero rudder it swings 150° left under takeoff power, and the pa28 spins. The **c172p** (160 hp, the model `Jsb/` ports to Lean) rolls straight and lifts off at ~65 kt, so it is the default. Pick another with `--model`. An "sr22ish" copy of `c182.xml` with the SR22's engine, weights and 144.9 ft² wing, plus a tamer nosewheel, is the next step.

## Limits

- Only the pilot-side gauges, RPM and manifold pressure are written; control surfaces, the cockpit yoke and lever, and the G1000's derived readouts stay frozen. The sidecar's status line is the ground truth.
- JSBSim's terrain is flat at the elevation X-Plane reported under the aircraft at start. Taxi far from the runway and the two worlds disagree.
- The sidecar paces itself with the wall clock; it drops behind on a slow frame rather than catching up.
