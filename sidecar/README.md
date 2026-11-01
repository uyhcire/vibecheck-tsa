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

## Scenarios

`--scenario NAME` starts airborne, trimmed for the speed and slope, engine running; the first position packet moves the X-Plane aircraft there, wherever it was. Set the throttle lever near the percentage the sidecar prints before you take the controls.

| name | where | state |
| --- | --- | --- |
| `final-kpao31` | 3 NM final to Palo Alto runway 31 | 1000 ft MSL, 75 kt, flaps 10, 3° slope |
| `sf-downtown` | over the Bay 2 NM east of downtown San Francisco, heading west | 600 ft, 100 kt, level |

`--at LAT,LON,HDG[,ELEV_M]` starts on the ground somewhere else.

## Crashes

JSBSim has a flat world, so the sidecar checks three things every frame and ends the flight on the first hit:

- every building in `sf_buildings.json`: 743 downtown San Francisco footprints 20 m and taller with their heights, from OpenStreetMap (`fetch_osm_buildings.py` refreshes it or fetches another box); without the file, the three landmark towers decoded from the landmarks pack's DSF (`OBSTACLES`);
- X-Plane's terrain under the aircraft (`sim/flightmodel/position/y_agl`), so hills JSBSim cannot see still count;
- a touchdown faster than 600 ft/min.

On a crash it prints why, writes the aircraft's velocity into X-Plane with a hard downward component, and hands X-Plane its physics back at that spot, so X-Plane's own damage model breaks the airplane and shows its crash. The status line names the nearest building within 400 m. The same footprints are the obstacle set for a safety filter.

### Drawing the obstacles in X-Plane

X-Plane's own downtown is procedural autogen and does not match the footprints, so `build_xplane_scenery.py` writes a custom scenery pack, `Custom Scenery/OSM Obstacles - SF Downtown`, straight from `sf_buildings.json`: each polygon becomes a facade extruded to its height, and X-Plane's objects, facades, autogen, forests, draped polygons and strings are excluded inside the obstacle box. What X-Plane draws there is then exactly what the sidecar can crash into. The script encodes the DSF tile itself (no DSFTool); rebuild it after refreshing the JSON and restart X-Plane. The downtown scenario is aimed at the Salesforce Tower: hands off, you hit it.

## Backup CBF guard (`--filter bcbf`)

`--filter bcbf` puts the `bcbf-city-flight` backup control barrier function between the stick and JSBSim. `flight/src/bin/filterd.rs` runs the crate's fly-by-wire pilot and filter as a line protocol; `sidecar/bcbf.py` converts the JSBSim state into the crate's map frame (`flight/data/sf/geo.py`), sends the sticks, and turns the returned load-factor / roll-rate / throttle demand into elevator, aileron and throttle with two PI loops. Build the bridge once: `cd flight && cargo build --release --no-default-features --bin filterd`.

- The stick button labelled 2 (USB button 4) toggles the filter in flight (`--toggle-button`; the filter starts active, `--filter-off` starts it off); USB button 3 toggles the crate's kamikaze autopilot (`--kamikaze-button`), which dives at the nearest tall building.
- The status line shows `cbf ON/off`, the filter mode (free, BLEND, COMMIT), the barrier `h` (clearance of the best escape) and the true clearance from the crate's world.
- The obstacle set is the crate's `flight/data/sf/sf_world.bin` (41,000 convex prisms, terrain, Bay Bridge, viaducts). `build_xplane_scenery.py --world flight/data/sf/sf_world.bin` renders exactly that in X-Plane. The flight ends when the crate's true clearance goes negative.
- The filter predicts with the crate's point-mass model, not JSBSim. Its Phase 3 margins (`robust`, the default; `--nominal` in `filterd` turns them off) exist for that mismatch, but the crate's guarantee does not transfer. `--predictor c172p` makes the predictor assume a Cessna (25 deg/s roll, 2 g, slow lags, less thrust) instead.
- Measured offline, 150 s runs, hands off (`--hostile` = the crate's random nose-down pilot, `--kamikaze` = dives at buildings):

  | pilot | filter | predictor | result |
  | --- | --- | --- | --- |
  | hostile | off | | crashed at 10 s |
  | hostile | on | crate | survived, 3 m minimum clearance |
  | hostile | on | c172p | survived, 4 m minimum clearance |
  | kamikaze | off | | crashed at 12 s |
  | kamikaze | on | crate | survived 125 s, 3 m minimum clearance |
  | kamikaze | on | c172p | crashed at 62 s |

  A human diving at 127 kt to 60 ft down a street crashed with the filter on: from there no escape the predictor believes in is flyable by the Cessna. The filter stops you reaching such states only if it is on before you get there, and only as far as the plant follows its model; switching it on late shows `NO ESCAPE`.
- The downtown scenario starts inside the crate's 6 km map (`x = 2700 m`), 1.1 NM east of downtown.

## Approach CBF (`--filter approach`)

    .venv/bin/python -I sidecar/xplane_jsbsim.py --scenario final-kpao31-2nm --filter approach --daytime

`final-kpao31-2nm` puts you 2 NM out on the 3 deg slope to KPAO runway 31 at 80 kt, flaps 20. The filter
(`sidecar/approach_cbf.py`) keeps you inside a cone fixed to the runway 31 threshold (apex 50 ft above it,
standard threshold crossing height): elevation angle 2 to 4 deg, lateral angle within 3 deg (never tighter
than 5 m), and a speed band of 80 +/-10 KIAS on final that slides to 75 +/-5 at the threshold and 65 +/-5
over the runway. Inside the cone and the band your inputs pass through unchanged; at an edge the filter
clamps the load factor, bank/roll rate or throttle (status line shows `[n+ p- thr+]`). The stick commands
load factor (centre = hold the flight path) and bank angle (centre = wings level).

From 0.3 NM the upper wall of the cone switches off and the **flare barrier** takes over: the sink rate may
not exceed 180 ft/min plus 0.12 per second of wheel height, so the round-out is exponential and the wheels
touch at about 180 ft/min. The lower wall stays on to the threshold, so you cannot land short; the speed band
stays on until the wheels touch. Hands off with the lever at idle, it lands itself 300 m past the threshold
at 60-69 kt. The same stick button toggles it. `--selftest` flies a hands-off and a hostile (nose-down,
left, idle) pilot headless to touchdown and checks the cone, the band, the sink rate and the centreline.

## Which JSBSim model

X-Plane's SR22: 2300 lb empty, 3600 lb max, 310 hp injected piston, constant-speed prop, low wing, fixed gear, Vne 205 kt. On paper JSBSim 1.3.3's **c182** (230 hp, constant-speed prop, 2950 lb) is the closest stock single. On the ground it is not usable from a stick: with zero rudder it swings 150° left under takeoff power, and the pa28 spins. The **c172p** (160 hp, the model `Jsb/` ports to Lean) rolls straight and lifts off at ~65 kt, so it is the default. Pick another with `--model`. An "sr22ish" copy of `c182.xml` with the SR22's engine, weights and 144.9 ft² wing, plus a tamer nosewheel, is the next step.

## Limits

- Only the pilot-side gauges, RPM and manifold pressure are written; control surfaces, the cockpit yoke and lever, and the G1000's derived readouts stay frozen. The sidecar's status line is the ground truth.
- JSBSim's terrain is flat at the elevation X-Plane reported under the aircraft at start. Taxi far from the runway and the two worlds disagree.
- The sidecar paces itself with the wall clock; it drops behind on a slow frame rather than catching up.
