# The safety objective

This page states what "the filter is safe" means for the city flight demo. Every proof, test and competition
in this repository is measured against it. A Lean version (`Spec/CitySafety.lean`) is being drafted; until it
lands, this page is the reference, and the Lean file will replace it as the authoritative statement.

## The definition

A filter `F` is **safe** when no state that the closed-loop system can reach from an allowed starting state is a
crash:

```lean
inductive Reach (F : Filter) : State × F.σ → Prop
  | init : Init s → Reach (s, F.start s)
  | step (u : PilotCmd) : ¬ Landed p.1 → Reach p → Reach (F.frame p u)   -- any pilot command until landed

def Safe (F : Filter) : Prop := ∀ p, Reach F p → ¬ Crash map p.1
```

`Crash map s` is contact at state `s` other than a gentle landing: the convex hull of the airframe's body points
touches terrain or a building, or a wheel touches anything but the runway, or touches the runway sinking faster than
3 m/s (see "Contact is checked at each frame" and "Landing" below). `Landed` (stopped on the runway) ends the flight.

- **The plant** is `JsbExact`, the bit-exact Lean port of JSBSim 1.3.3's c172p, stepped one JSBSim frame
  (1/128 s) at a time. JSBSim is the ground truth for this simulator.
- **The pilot** is arbitrary: any control-surface, throttle and wheel-brake input within its physical range, chosen
  afresh every frame. The demo's keyboard pilot, fly-by-wire and 50 Hz control loop are special cases.
- **The filter** is abstract: its own memory, a starting memory, and a per-frame map from (memory, aircraft state,
  pilot command) to the input actually applied, which is clamped to the physical ranges.
- **Allowed starting states** (`Init`) are a small, conservative, explicit set: for example, steady level flight
  well clear of everything. They carry 8 lb of fuel per tank, so every flight has to end in a landing. Leaving out any starting state that is inconvenient is fine. Because the pilot is
  arbitrary, close calls (flying deliberately into a street canyon, say) are still reachable from such starts.
- **Crash** means actual contact between the airframe and terrain or a building. There is **no clearance margin** in
  the definition; a margin is a design choice inside a filter.
- **Landing.** The map has a runway (on the demo map `[-100, 1100] × [-1360, -1320]`, surface 9 m, landing east).
  Only the three wheels may touch, only the runway, at most 0.5 m below its surface (the strut compressed), sinking
  at most 3 m/s. The plant's ground plane (0 ft) is placed at the map's floor and runway surface (`CityMap.datum`),
  and terrain below the floor is raised to it, so the plant's gear and the map agree.

## What is deliberately not in the definition

These belong to particular proofs or filter designs, not to the objective:
- **Terminal sets T**, "safe forever" sets, escape laws and inductive invariants. A proof of `Safe F` may use them,
  and a state that is hard to prove safe can be handled by proving it unreachable.
- **"Eventually climbing" requirements.** These made safe-forever claims testable on a flat-ground model.
- **Flight-envelope limits** (angle of attack, load factor, minimum airspeed, stall). JSBSim decides what happens;
  breaching a limit is not a crash. If a separate model-validity condition is wanted later (for claims about a real
  aircraft rather than the simulator), it gets its own name and is not folded into `Safe`.

## What counts as a result

- **A proof:** a Lean theorem `Safe F`, checked by the kernel, with its axioms audited
  (`propext`, `Classical.choice`, `Quot.sound`, plus any native-computation axioms explicitly accepted).
- **A counterexample:** an allowed start and a sequence of pilot commands under which `F` lets the aircraft crash,
  replayable exactly on `JsbExact`.

Nothing else is authoritative. In particular, the CI referee's scores and its "valid" verdicts
(`eric/ci-scoreboard`: `TSafeR`, `TInvariantR`, the falsifier) concern terminal-set claims on the longitudinal
fixed-point model. They are search aids and proof-route milestones, not safety results. A counterexample to a
terminal-set claim (for example an envelope breach after entering T) is not a counterexample to `Safe F` unless it
leads to a reachable crash.

## Decisions for the Lean version

`Spec/CitySafety.lean` states these; `Spec/CitySafetyChecks.lean` checks them on a hand-made map.

- **Airframe shape for contact.** The convex hull of the 7 contact points in the stock JSBSim c172p file (nose and
  main gear, propeller hub, tail skid, both wingtips) and the 13 contact points FlightGear's c172p (FGData 2024.1)
  has in its default configuration: its gear, tail skid, wingtips, broken-gear points, nose, nose top, cockpit top
  and fin top. FlightGear decides crashes at exactly these points. They are shifted into the stock file's structural
  frame by the mean offset of the three gear points both files share (0.56 in RMS residual) and kept separate in
  the Lean file (`contactPoints ++ flightGearPoints`). FlightGear's wingtips (±232 in) are wider than the stock
  file's and the published span (35.8 ft, ±214.8 in), and its nose points lie about 2 m ahead of the propeller
  hub; both make the hull larger, which is conservative.
- **Beyond the 6 km map, terrain continues the edge profile** (the clamp in `World::terrain`, 731 to 927 m on the
  demo map). Leaving the map is neither a crash nor an escape. The current gate filter treats leaving the map as
  clear, which is not sound under this definition.
- **Contact is checked at each frame.** A state crashes if the convex hull of its airframe points touches terrain
  or a building. Frames are 1/128 s apart (0.39 m at 50 m/s), so contact strictly between two frames is not counted:
  a thin obstacle passed between frames is missed (`Spec/CitySafetyChecks.lean` shows a 2 cm ledge). Chosen over a
  swept hull for simplicity; with buildings metres thick the gap is negligible.
- **A NaN or infinite pose counts as a crash.**
- **Touching counts as a crash:** terrain and buildings are closed sets.
- **The map frame is the demo's, and positions are the plant's reported ones.** The aircraft's reported CG position
  (`CitySafety.report`) gives east and north as ECEF y and z (the demo's `MapFrame` axes at latitude and longitude 0)
  and up as altitude above sea level, as `CityJsb.obs` reports them. Airframe points are placed from it with the
  reported body-to-local rotation matrix `Tb2l`, in the local north-east-down frame at the CG; over the ±3000 m map
  that frame turns by at most 0.03° against the map axes, under 6 mm across the airframe.
- **Numbers.** Plant states are `Float`. The reported pose (CG location and altitude, `Tb2l`) is the plant's own
  `Float` computation, read exactly; airframe points, hulls, terrain and buildings are exact rational arithmetic from
  there.
