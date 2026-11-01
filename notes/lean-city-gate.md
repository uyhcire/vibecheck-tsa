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
| `GateSafety/Proofs.lean`, `Parallel.lean` | `safe`; `frameP`, which checks candidates in parallel (`Task.spawn`) and is proven equal to `frame` | No |
| `CityGate/Map.lean` + `CityGate/data/` | The city (seed 1337) as exported by `Tools/city-export`, parsed exactly | Yes |
| `CityGate/Plant.lean` | `JsbExact` as the plant, one frame per step, placed on the map | Yes |
| `CityGate/Geometry.lean` | `Crash`: a 6 m half-size cube around the exactly decoded position touches a box or the terrain. `clearAt`: integer keep-out test, 8.5 m + `extra`. `clear_sound` proves `clearAt → ¬ Crash` | `Crash` only |
| `CityGate/Law.lean`, `Terminal.lean`, `Gate.lean` | Port of the escape law, end-of-escape test and proposal layer | No |
| `CityGate/Ffi.lean`, `c/citygate.h` | `citygate_*` C ABI in `libcityjsb`. `frameOut_fst` proves the exported frame is `cityGate.frame` | No |
| `CityGate/Safety.lean` | `city_safe` | No |

**Running it.**
- `--env lean` in the demo and in `crashes` flies the Lean gate. `--env gate` is still the Rust gate.
- `lake build CityGate libcityjsb`, then `cargo build --release --features jsb`.
- `crashes OUT N --secs S` shortens episodes.
- `lake exe citygatespot` is the spot check: the street escape for 8 s is bit-identical to Rust.

**The Lean gate is not the Rust gate.** Only the Lean one is proved.
- **Clearance:** a cube in exact arithmetic, checked every frame, including the pilot's frames. Rust uses a sphere plus a wing capsule in floating point, every 8 frames.
- **Cadence:** checks every 3 frames, and up to 4 candidates per check, each run to the end.
- **Rust's default law** is `LAW_CEGIS2`, which is what was ported.

Rust's clearance can't be certified as is. Lean has no theorems about float rounding, and nothing bounds what happens between the 8-frame samples.

**Open.**
1. **Speed.** About 65 ms CPU per 20 ms tick against about 10 ms for Rust. `clearAt` still uses `Rat` for decoding and terrain squares, and there is no early stop once a candidate verifies.
2. **Conservativeness against Rust.** The cube corners, per-square terrain maxima and 4 candidates may intervene more. The 4 m margin was there for the 8-frame gaps and could shrink now that every frame is checked. A ball or capsule test in integer squared distances needs no square roots.
3. **`TermSound`** remains an assumption, including the rule that leaving the map counts as clear.
4. **`Init`** is "the initial escape checks out", which is computed, not a fixed set.
