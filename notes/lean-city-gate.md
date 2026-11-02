# The city gate in Lean, proved safe (note for agents picking this up)

**What exists.** The exact-rollout gatekeeper of `flight/src/envfilter.rs` is now also a Lean program (`CityGate/`). It flies `JsbExact` over the exact city map. `CityGate.city_safe` proves it never crashes, in the shape of `docs/safety-objective.md`:

```lean
theorem city_safe (hT : TermSound cityGate Crash) : Safe cityGate Crash Init
```

From an allowed start, whatever surfaces and throttle the pilot gives each JSBSim frame, no reachable state is a `Crash`. The one assumption, `hT`, is that the end-of-escape test means safe forever. Axioms: `propext`, `Classical.choice`, `Quot.sound` (`Tools/CityGateAudit.lean`).

**How the proof works** (`GateSafety/`, generic and short). The gate always holds a controller that is safe forever from the current state. Each frame it flies the first proposed candidate whose rollout checks out (clear at every frame until the end-of-escape test passes), or else the controller it holds. Rollouts fly the same plant the aircraft flies, so a checked candidate is safe forever, and so is the next frame of a safe controller. Induction over reachable states finishes it. The escape law, the end-of-escape test and the proposal layer (hold, resume, ordering) are never looked inside. Any code there keeps the theorem.

**Files.**

| File | Role | Trusted? |
|---|---|---|
| `GateSafety/Spec.lean` | Abstract gate, `Reach`, `Safe`, the three assumptions | Yes |
| `GateSafety/Proofs.lean`, `Parallel.lean` | `safe`; `chooseR`, which checks candidates in parallel rounds (`Task.spawn`) and drops those behind one that verified, proven equal to `choose` | No |
| `CityGate/Map.lean` + `CityGate/data/` | `GateMap`, a map as the gate sees it (terrain grid, boxes); the city (seed 1337) as exported by `Tools/city-export`, parsed exactly (`gridMap`) | Yes |
| `CityGate/Plant.lean` | `JsbExact` as the plant, one frame per step, placed on the map | Yes |
| `CityGate/Geometry.lean` | `CrashOn M` (`Crash` is `CrashOn gridMap`): a 6 m half-size cube around the exact position touches a box or the terrain of `M`. The position is the spec's: `CitySafety.report`'s CG (ECEF y, z, altitude, ft) read exactly and converted to metres in `Rat`, plus the map offset. `clearAtOn G`: integer keep-out test, 8.5 m + `extra`, against `G`, the map with its boxes rounded outward and indexed (`GateGeo`). `clear_sound_on` proves `clearAtOn G → ¬ CrashOn G.map` on every map | `CrashOn` only |
| `CityGate/ClearFast.lean` | `clearAt` in scalar `Nat`/`Int` only (the reported doubles decoded from their bits and scaled exactly by `ft`), proven equal and swapped in by `@[csimp]` | No |
| `CityGate/Law.lean`, `Terminal.lean`, `Gate.lean` | Port of the escape law, end-of-escape test (on a map's raster, `EMap`) and proposal layer. `gateOn S` is the gate on map `S` (`Site`: `GateGeo` and `EMap`); `cityGate` is `gateOn gridSite` | No |
| `CityGate/Ffi.lean`, `c/citygate.h` | `citygate_*` C ABI in `libcityjsb`. `frameOut_fst` proves the exported frame is `(gateOn S).frame`, for every map and parallelism setting. `citygate_map_new` takes a map from the host (`siteOf`) | No |
| `CityGate/Safety.lean` | `city_safe`; `site_safe`, the same on any map | No |
| `flight/src/covering.rs` | Boxes containing San Francisco's prisms, and the check that they do | Covering only |

**Running it.**
- `--safety-filter exact-rollout-lean` in the demo and in `crashes` flies the Lean gate. `--safety-filter exact-rollout` is still the Rust gate.
- `lake build CityGate libcityjsb`, then `cargo build --release --features jsb`.
- `crashes OUT N --secs S` shortens episodes.
- `lake exe citygatespot` is the spot check: the street escape for 8 s is bit-identical to Rust.
- Candidates are checked one after another, stopping at the first that verifies. `CITYGATE_PAR=N` checks up to N at once in rounds of `CITYGATE_ROUND` frames (default 64); the frame is the same.
- `crashes` with `--safety-filter exact-rollout-lean` prints per-tick CPU. `CITYGATE_TRACE=1` writes each episode's per-frame trace (`OUT/<episode>.trace`) for comparing two builds with `cmp`. `CITYGATE_COUNT=1` also prints plant frames per tick (it runs every check twice). `CITYGATE_PROBE=1` writes `OUT/<episode>.probe`: per tick the gate's CPU, and per check each candidate's frames, why its rollout ended, and the time and work in `fly`, `clear` and `term` (it also runs every check twice).

**Other maps: San Francisco.** The gate's map is a value: `gateOn S` flies map `S` (`Site`): its exact geometry (`GateMap`: terrain grid with its own corner and size, boxes) and Rust's raster of it for the end-of-escape test and the street escape (`EMap`). `cityGate` is `gateOn gridSite`, the city built in; its traces are byte-identical to before (`CITYGATE_TRACE`, 11 episodes) and every audit prints the same. San Francisco is not built in: the host passes it (`citygate_map_new`, `flight/src/leangate.rs`), once per process, from `World::load(MapId::SanFrancisco)`: the terrain, the raster, and boxes for the buildings.
- **Boxes, not prisms.** San Francisco's buildings are convex prisms, 132,958 of them, and only 65 are axis-aligned, so they cannot be the gate's boxes as they are. `flight/src/covering.rs` covers each with boxes: the footprint is cut into equal strips across x or across y, each covered by the box of its extent, adding strips until every box point is within 1 m of the footprint. The strip extents are computed in interval arithmetic, so the boxes contain the prism exactly; the host re-checks it before handing them over, and so does `city-export check-sf`. That gives 1,204,183 boxes. The extra caution: they cover 28.85 km² against the footprints' 26.50 km² (+8.8%; one bounding box per building would be +57%), and a box point lies at most 1.04 m beyond its footprint at p99 (median 0.82 m, max 3.69 m where 64 strips were not enough). A 2 m bound would need 480,000 boxes for +15.3%.
- **What `site_safe` says about it.** `site_safe S` is `city_safe` on any map, with crashes judged against `S`'s boxes and terrain, under the same `TermSound` assumption. Since the boxes contain the prisms, no crash there means no contact with San Francisco's buildings. The spec-level theorem (`CitySafety.Safe cityMap specFilter`, `CityGate/SpecBridge.lean`) is only for the default city.
- **Map building** takes about 3 s at start (1-2 s of it the covering). Peak memory of a one-episode `crashes` run on San Francisco is 1.36 GB, against 0.59 GB with the Rust gate (0.28 GB on the default city): the raster is held again as doubles, plus the boxes and their 16 m index.
- **Agreement with Rust** (`make leanspot`, `flight/src/bin/leanspot.rs`): every escape from the 4 San Francisco scenario starts and 20 random starts, flown by both gates (`citygate_rollout`, `envfilter::rollout`): 144 escapes, every path bit-identical at every 8th frame (so the law, including the street escape's helix test on San Francisco's raster, is the same), and where both end tests pass, they pass on the same frame (119 escapes). The verdicts differ on 2: the Lean gate's clearance fails where Rust's passes, as its 8.5 m cube on covering boxes is more cautious than Rust's sphere and wing capsule on the prisms. Rust alone failed none. On the default city (4 random starts) all 54 agree.
- **CPU per tick** (`crashes OUT 12 --map sf --secs 30`, thread CPU of the gate's frames): SF_CPU_LINE

**The Lean gate is not the Rust gate.** Only the Lean one is proved.
- **Clearance:** a cube in exact arithmetic, checked every frame, including the pilot's frames. Rust uses a sphere plus a wing capsule in floating point, every 8 frames.
- **Cadence:** checks every 3 frames, up to 4 candidates per check in order, stopping at the first that verifies.
- **Rust's default law** is `LAW_CEGIS2`, which is what was ported.

Rust's clearance can't be certified as is. Lean has no theorems about float rounding, and nothing bounds what happens between the 8-frame samples.

**Open.**
1. **Speed.** Per-tick CPU, checking one candidate after another, is now about the Rust gate's: median 7.3 ms against 8.3 ms, p99 30 ms against 24 ms (main before this: 74 ms median). Both gates spend 90-97% of it stepping `JsbExact`, about half of that allocating and freeing boxed floats. Lean has no per-tick frame budget, so ticks where every candidate fails run every candidate in full (p99.9 291 ms); Rust stops at 2,200 frames. One full-horizon rollout is about 2,050 frames, which sets the floor for parallel checking.
2. **Conservativeness against Rust.** The cube corners, per-square terrain maxima and 4 candidates may intervene more. The 4 m margin was there for the 8-frame gaps and could shrink now that every frame is checked. A ball or capsule test in integer squared distances needs no square roots.
3. **`TermSound`** remains an assumption. Two known holes are fixed: leaving the map no longer ends a rollout (`Ctl.term`, `rayClear`), and the straight ending needs a settled climb (windows' mean vz within 1 m/s) with the ray gradient capped at 0.11. These changes make the Lean gate differ from the Rust one.
4. **`Init`** is "the initial escape checks out", which is computed, not a fixed set.

**Against the reviewed spec.** `CityGate/SpecBridge.lean` proves `cityGate_spec_safe_R : CitySafety.Safe cityMap specFilter` (the per-frame spec) from `TermSoundR cityGate (CrashH h) GInit` (the end-of-escape test on the gate's own rollouts, for the h m cube, h ≤ 8.5), `InitChecked cityGate GInit` (`lake exe specbridgeinit` checks it) and `AirframeNear h` (airframe points within h m of the reported position). `TermSoundR` is false as stated while `JsbExact` burns fuel. Audit: `lake env lean Tools/SpecBridgeAudit.lean`.
