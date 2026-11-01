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

The buildings are dressed like main's photoreal renderer (`flight/src/photo.rs`): the same six CC0 facade
textures and two roof textures (`flight/assets/textures`, pulled from `origin/main` with `git show` when
this branch lacks them), chosen per building by the same height rule and seed, as twelve X-Plane facade
types. Needs `pillow` in the venv. Per-building tint is not reproduced. After rebuilding, X-Plane has to
reload the scenery (Developer > Reload scenery, or restart).

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
standard threshold crossing height) and a speed band. **The pilot's authority shrinks with distance**: beyond
1.6 NM the cone is 2-4 deg in elevation and +/-3 deg laterally with a 30 deg bank limit and full rudder; from
there to 0.3 NM it narrows linearly to 2.5-3 deg and +/-1 deg (never thinner than +/-3 m vertically or 3 m
laterally), 10 deg of bank and 30 % rudder, and stays there to the threshold. The speed band is 80 +/-10 KIAS
on final, sliding to 75 +/-5 at the threshold and 65 +/-5 over the runway until the wheels touch. Inside the
set your inputs pass through unchanged; at an edge the filter clamps load factor, roll rate or throttle (the
status line shows `[n+ p- thr+]` and the current tolerances). The stick commands load factor (centre = hold
the flight path) and bank angle (centre = wings level).

Each bound is a closed-form exponential CBF: load factor for the vertical walls (relative degree 2), roll
rate for the lateral walls (degree 3) and the bank limit (degree 1), throttle for speed (degree 2 through the
engine spool-up, with the load factor taking over when the throttle saturates, never below a floor).

**Flare.** Inside 0.3 NM climbing is barred and the sink rate may not exceed 180 ft/min plus 0.12 per second
of wheel height, so the round-out is exponential and the wheels touch at about 150-250 ft/min; the cone's
floor holds to the threshold, so a dive cannot land short; over the runway the sink must be at least 85 % of
that limit, so a float cannot last. Hands off at idle it lands itself about 300 m past the threshold.
`--selftest` flies a hands-off pilot, a hostile one (nose-down, left, idle) and a floating one (full back
stick, right roll, full power, rudder) headless to touchdown: all three land on the runway, on speed, within
3 m of the centreline. The same stick button toggles the filter.

## City CBF: coarse or fine dynamics (`--dynamics coarse|fine`)

Two models can build the city CBF; both run on the gate's procedural city (map seed 1337, Luis Pabon's generator,
identical on this branch and on main), placed on the south Bay by `sidecar/gridmap.py`:

    .venv/bin/python -I sidecar/build_xplane_scenery.py --grid city-map/      # once: the "Grid City - Gate Map" pack
    .venv/bin/python -I sidecar/xplane_jsbsim.py --scenario grid-city --filter bcbf --daytime                  # coarse
    .venv/bin/python -I sidecar/xplane_jsbsim.py --scenario grid-city --filter bcbf --daytime --dynamics fine  # fine

`city-map/` comes from main's `cargo run --release --manifest-path Tools/city-export/Cargo.toml -- map city-map`;
the pack draws the 2,145 boxes with the photoreal facades and the 301 x 301 terrain as one mesh object.

- **coarse**: the point-mass backup CBF of `bcbf-city-flight` (`filterd --map grid`) guards the pip JSBSim c172p,
  as in the downtown scenario. Fast; no guarantee for the JSBSim plant (see the stress table above).
- **fine**: Eric Yu and Luis Pabon's gatekeeper filter (`libgate`, main) verifies escapes on `JsbExact`, a
  bit-exact Lean copy of JSBSim 1.3.3's c172p. It needs that aircraft's full private state every tick, which the
  pip module cannot export, so in this mode the aircraft you fly **is** `JsbExact` (`libcityjsb`), stepped at
  1/128 s with the surfaces the gate returns (`sidecar/gate.py`). Every 3 frames it checks whether your command,
  held one tick, still leaves a verified escape (straight climb, 30/40 deg climbing turns, a climb along the
  street); if not it flies the escape it verified last tick and hands back when yours verifies again. Status:
  `gate ON pilot|ESCAPE esc <name> verified clear <m> <ms>`. The libraries come from main: `make gate` there,
  then point `--gate-dist` (or `GATE_DIST`) at its `dist/` (default: `../vibecheck-tsa-worktrees/main/dist`).
  Flaps stay up and the stick maps straight to JSBSim's surfaces (`GATE_PILOT_SURFACES`); the rudder is yours.

`sidecar/gate.py --selftest`: hands off at 150 m, 540 m west of the 459 m tower: gate on flies 120 s with 3.9 m
minimum clearance, gate off hits the tower at 14 s. The same stick button toggles either filter.

## Which JSBSim model

X-Plane's SR22: 2300 lb empty, 3600 lb max, 310 hp injected piston, constant-speed prop, low wing, fixed gear, Vne 205 kt. On paper JSBSim 1.3.3's **c182** (230 hp, constant-speed prop, 2950 lb) is the closest stock single. On the ground it is not usable from a stick: with zero rudder it swings 150° left under takeoff power, and the pa28 spins. The **c172p** (160 hp, the model `Jsb/` ports to Lean) rolls straight and lifts off at ~65 kt, so it is the default. Pick another with `--model`. An "sr22ish" copy of `c182.xml` with the SR22's engine, weights and 144.9 ft² wing, plus a tamer nosewheel, is the next step.

## Limits

- Only the pilot-side gauges, RPM and manifold pressure are written; control surfaces, the cockpit yoke and lever, and the G1000's derived readouts stay frozen. The sidecar's status line is the ground truth.
- JSBSim's terrain is flat at the elevation X-Plane reported under the aircraft at start. Taxi far from the runway and the two worlds disagree.
- The sidecar paces itself with the wall clock; it drops behind on a slow frame rather than catching up.
