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
  | step (u : PilotCmd) : Reach p → Reach (F.frame p u)   -- any pilot command; F decides what is applied

def Safe (F : Filter) : Prop := ∀ p u, Reach F p → u.Valid → ¬ SweptCrash map p.1 (F.frame p u).1
```

`SweptCrash map s s'` is contact during the frame from `s` to `s'` (see "Contact is checked over each frame's
sweep" below). `Safe F` also rules out `Crash` (contact at a single state) at every reachable state.

- **The plant** is `JsbExact`, the bit-exact Lean port of JSBSim 1.3.3's c172p, stepped one JSBSim frame
  (1/128 s) at a time. JSBSim is the ground truth for this simulator.
- **The pilot** is arbitrary: any control-surface and throttle input within its physical range, chosen afresh every
  frame. The demo's keyboard pilot, fly-by-wire and 50 Hz control loop are special cases.
- **The filter** is abstract: its own memory, a starting memory, and a per-frame map from (memory, aircraft state,
  pilot command) to the input actually applied, which is clamped to the physical ranges.
- **Allowed starting states** (`Init`) are a small, conservative, explicit set: for example, steady level flight
  well clear of everything. Leaving out any starting state that is inconvenient is fine. Because the pilot is
  arbitrary, close calls (flying deliberately into a street canyon, say) are still reachable from such starts.
- **Crash** means actual contact between the airframe and terrain or a building. There is **no clearance margin** in
  the definition; a margin is a design choice inside a filter. `Crash` is its own predicate so that a later version
  can treat benign landing-gear contact with a runway as a landing, not a crash (landing is out of scope for now).

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

- **Airframe shape for contact.** The convex hull of the 7 c172p contact points in the JSBSim aircraft file (nose
  and main gear, propeller hub, tail skid, both wingtips) plus 5 outline points from FlightGear's c172p visual model
  (FGData 2024.1): the top of the fin and the leading and trailing edge of each wingtip. They are placed in the
  JSBSim structural frame as that aircraft's model file places them, and are kept separate in the Lean file
  (`contactPoints ++ outlinePoints`).
- **Beyond the 6 km map, terrain continues the edge profile** (the clamp in `World::terrain`, 731 to 927 m on the
  demo map). Leaving the map is neither a crash nor an escape. The current gate filter treats leaving the map as
  clear, which is not sound under this definition.
- **Contact is checked over each frame's sweep.** A frame crashes if the convex hull of the airframe points at its
  two ends touches terrain or a building. That hull contains every point's straight-line path between the frames;
  the plant has no state between frames that would define a curved path. A thin obstacle passed between two frames
  therefore counts, though neither frame touches it.
- **A NaN or infinite pose counts as a crash.**
- **Touching counts as a crash:** terrain and buildings are closed sets.
- **The map frame is the demo's.** East and north are ECEF y and z (the demo's `MapFrame` axes at latitude and
  longitude 0) and up is altitude above sea level, computed for each airframe point with the plant's own formula
  for the aircraft's altitude. Hulls are taken in these map coordinates, which follow the Earth's curvature; for the
  12 m airframe a straight segment there differs from a straight segment in space by at most L²/8R, about 3 µm.
- **Numbers.** Plant states are `Float`. Each airframe point's map position is the plant's own `Float` computation
  (the same placement JSBSim uses for gear contact points), read exactly; hulls, terrain and buildings are exact
  rational arithmetic from there.
