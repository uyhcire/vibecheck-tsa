# CI referee: the escape-filter scoreboard

`ciscore` is the fixed scoreboard for the escape-filter research effort. Each competitor submits escape laws
and terminal sets for the longitudinal c172p model (`Jsb/Model.lean`, `Fx` instance). The scoreboard flies them
on that model, attacks the terminal sets, audits the claimed Lean proofs, and prints one headline number.
Everything that affects the headline is deterministic: exact `Fx` arithmetic, a committed benchmark and fixed
seeds.

## 1. The problem being scored

The runtime filter decides, every tick, whether the pilot may continue. It flies each candidate escape on the
formal model itself, for at most `horizon` ticks, from the state the pilot's input would lead to. It accepts
that state when some escape's rollout:

1. stays inside the envelope at every 1/128 s substep;
2. keeps the clearance: h ≥ 5 m above flat terrain at h = 0 (the model's ground effect is referenced to h = 0);
3. enters the escape's terminal set T at a tick boundary within `horizon` ticks (T is checked from tick 0).

The rollout is the model, so it needs no certificate. Two things remain to be certified:

- **T is safe forever** (`Ci.Goals.TSafe`). From every (state, law memory) in T, the escape stays in the
  envelope and above the clearance at every substep forever, and from some tick on it climbs at every tick.
  This is the open proof obligation. T may be any set for which an offline certificate proves this:
  - a small box around the steady climb;
  - an "interior" such as h ≥ H_cert(state), where H_cert is a conservative bound proved offline;
  - a union of such sets.

  Exact simulation handles the tight cases near the boundary. The certificate handles everything comfortably
  inside T, so the rollout stops early there.
- **The filter induction**: "the current state always has an accepted escape". It is generic. When a check
  fails, the previous tick's accepted escape is flown: its rollout is safe up to T, and TSafe covers the rest.
  This induction is not formalised here.

### Fixed safety definition (`Ci/Rules.lean`)

| item | definition | value |
|---|---|---|
| inputs | clamped every tick by `clampInput`: elevator [-1, 1], throttle [0, 1], sideslip 0 and bank 0 (wings level). No rate limit is imposed; a law may impose its own. | |
| stall | α = atan2(w, u) from the state's body velocity, checked exactly as `w·2^16 ≤ tan(α_max)·u`, with u > 0 required | α_max = 0.28 rad, the CL peak of `C172.tbl_x_5` (the envelope study's value) |
| load factor | body-normal specific force over g: ((au + g)·cos θ − ah·sin θ)/g, from the substep's evaluated world accelerations, with g = 9.80665 | ≤ 3.8. Neglecting Earth rotation and gravity's height dependence changes n by about 3e-4. |
| airspeed floor | vx² + vz² ≥ V_floor² | 27 m/s, about 1.05 × the 1-g stall speed. Trims converge down to 30 m/s, and α at trim extrapolates to 0.28 near 26 m/s. |
| stall bit | must stay 0 | |
| clearance | h ≥ clearance at every substep | 5 m |
| climbing (inside T) | at every substep: vz ≥ 2 m/s and h rising | |
| T test window (adversary) | 640 ticks (40 s), all substeps safe, every tick in the last 160 (10 s) climbing; long tests use 1920 ticks (120 s) | |
| real-time budget | horizon × number of laws ≤ 640 rollout ticks per check. At about 30 µs per `Fx` tick this is about 19 ms, under a third of the 62.5 ms tick. | |

A substep is `Jsb.step 7 true`. Eight substeps are exactly `Jsb.tickAB`, the formal model's tick.

## 2. What a competitor submits

### 2.1 `Ci/Agent.lean` defines `Ci.Agent.submission : Ci.Submission`

The interface is in `Ci/Interface.lean`:

```lean
structure Commit where s : State; pilot : Input          -- state and last pilot input at commit
structure Law where
  σ : Type                                               -- law memory
  name : String
  init : Commit → σ                                      -- memory at commit (e.g. last elevator)
  step : σ → State → Input × σ                           -- one 1/16 s tick; scoreboard clamps + tickAB
  inT : State × σ → Bool                                 -- terminal set T (may depend on h and memory)
  enc : σ → Array Int                                    -- memory encoding, used by the adversary
  dec : Array Int → Option σ
structure Submission where name : String; laws : List Law; horizon : Nat
```

- **Several laws are allowed.** The filter tries them in list order and accepts on the first accepted rollout.
- **`horizon`** is the rollout limit in ticks, per law.
- **The law sees only the state at tick boundaries and its own memory.** `Commit.pilot` is the only elevator
  position there is, because the model has no actuator state.

### 2.2 `Ci/Audit.lean` defines `Ci.Audit.claimed : List Lean.Name`

The scoreboard reports every claimed theorem with its axioms. A theorem counts as proved only if its axioms
are a subset of {`propext`, `Classical.choice`, `Quot.sound`}. So `sorry`, `native_decide` and new axioms do
not count.

A law's T is **proved** when a claimed, proved theorem has one of these types, with `L` definitionally equal to
an element of `Ci.Agent.submission.laws`:

- `Ci.Goals.TSafe L`;
- `Ci.Goals.TInvariant L`, the one-tick sufficient condition. `Ci.Goals.tSafe_of_tInvariant` is already proved.

The proof component counts only when **every** law of the submission is proved. Other claimed lemmas are
listed but earn nothing. For the one-tick obligation, the repo already has interval machinery for one-tick
facts over boxes: `Jsb/Conformance.lean` (`checkRec`, `region_sound`) and `Jsb/EscapeRegion.lean`.

### 2.3 Static rule R4, checked at build time by `Ci/Report.lean`

`init`, `step` and `inT` must not use the model's dynamics. Everything reachable from the submission constant
is scanned, through definition bodies and `implemented_by` targets. The scan fails on:

- `Jsb.integrate`, `evaluate`, `step`, `tickAB`, `tickEuler`, `probe`, `Escape.tick`;
- any constant whose type mentions the aerodynamic input `Jsb.C172.AeroIn`, i.e. the aero functions.

Why: the runtime filter is the only place where simulation is allowed, and its cost is bounded by `horizon`.
A T that simulates would hide unbounded cost and could not be proved.

## 3. The benchmark (`Ci/data/bench.csv`, fixed)

Each row holds a family, an id, the generating parameters, and the raw `Fx` fields of the commit state (19
state fields) plus the last pilot input. `ciscore` checks the file's 64-bit FNV-1a hash against
`Ci.benchHash`; a mismatch makes the score invalid. The file is regenerated (identically) by
`cigen gen Ci/data/bench.csv 250` (`Tools/CiGen.lean`).

- Trims are solved on the `Fx` model (`trimFx`, the `EnvConf.trim` scheme). Histories are made consistent with
  `EnvConf.consistent`. A trim whose normal-acceleration or pitch-acceleration residual exceeds 0.01 is
  rejected.
- In the hard families, pilot programs are flown in `Fx` with `tickAB`, after 16 settling ticks at trim.
- Each family draws from a splitmix64 PRNG with a fixed seed.
- Every commit must pass `commitOk`: envelope satisfied, h in [500, 2000] m, V ≤ 80 m/s, pilot input within
  limits.

| family | n | generation | commit ranges (V m/s, γ rad, other) |
|---|---|---|---|
| typical | 264 | trims on V ∈ {30, 33, …, 60} × γ ∈ {−0.5, −0.4, …, 0.2} × throttle {0, 0.6, 1}, at h = 1000 m | q = 0 |
| push | 250 | pilot pushes the elevator 0.2–0.8 below trim, ramped over 1–4 ticks; commit after 3–16 ticks; q < 0 required | V 32.7–59.1, γ −0.34–0.09, α down to −0.27, q −0.94 to −0.07 |
| zoom | 250 | throttle to idle, attitude hold at θ 0.3–0.55 until V drops to 31–40; γ > 0 required | V 31–40, γ 0.06–0.46, idle |
| fastdive | 250 | attitude hold 0–0.2 rad below the trim attitude for 1–4 s from steep trims; V ≥ 52 and γ ≤ −0.25 required | V 52.6–77, γ −0.49 to −0.25 |
| slowidle | 250 | idle trims at 30–38 m/s, vz hold until V drops to 28–33; V ≤ 34 and \|γ\| ≤ 0.1 required | V 28–33, near level, idle |
| elevtrans | 250 | elevator stepped to a value at least 0.4 from trim for 1–4 ticks | pilot elevator anywhere in [−1, 1], q −1.1 to 1.7 |

Commit heights are about 1000 m (zoom 1024–1111 m, fastdive 864–978 m).

## 4. Metrics and the headline

For every benchmark state `ciscore` runs the filter's check at the stored altitude, then finds h\*. Per state:

- **accepted**: the check accepts at the stored altitude. **Coverage** is the accepted fraction.
- **h\***: the lowest commit height on a 0.25 m grid at which the same state is accepted. The search starts
  1 m below clearance + (loss at the stored altitude), climbs 12 m, then doubles. If nothing is accepted below
  the stored altitude, h\* is the stored altitude. This happens for a few fast states: denser low air raises
  the load factor above 3.8.
- **rollout ticks to T** at the stored altitude and at h\*, plus the ticks spent per check (summed over the laws
  tried) and the wall-clock per check.
- **loss until T**: commit h minus the lowest h before entering T. This is informational. With an interior
  T it is often 0, because the rollout stops at once.

The headline components:

- **Q** (coverage × generosity) = mean over all benchmark states of `10 / (10 + (h* − clearance))`, counting 0
  when a state is not accepted. Lower h\* means the filter can intervene later.
- **R** (short rollouts, i.e. a large certified interior) = mean over all states of `16 / (16 + ticks to T at
  the stored altitude)`, counting 0 when not accepted.
- **B** (budget) = min(1, 640 / (horizon × laws)).
- **P** = 1 when every law's T is proved (§2.2), else 0.

**Validity** requires all of:

- the benchmark hash matches;
- no R4 violations;
- zero T counterexamples;
- at least one law, and horizon > 0.

```
headline = 0                                        if not valid
         = 1 + P + 0.5·Q + 0.4·R + 0.1·B             otherwise
```

So the headline rewards, in order:

1. validity, which is worth 1;
2. a proved T, which is worth 1;
3. coverage, generosity and short rollouts, which are together worth up to 0.9;
4. staying inside the real-time budget, which is worth 0.1.

Wall-clock times are reported but are not part of the headline, because they are not deterministic.

### 4.1 The terminal-set adversary

The adversary works per law. Its seeds are the (state, memory) pairs at which the benchmark rollouts entered
T, at the stored altitude and at h\*. Candidates are encoded as the 19 raw state fields plus `enc` of the
memory:

- dz is perturbed, and dx is re-derived as √(1 − dz²);
- x, dx and stall are not perturbed directly;
- the scale per field is half the seeds' range, with a floor for each state field.

Every candidate must satisfy `inT`. Each candidate is tested with the 640-tick T test. The budget is 2000
candidate draws, cycling over these modes:

0. random perturbation of a seed, at amplitude 0.05, 0.2, 0.5 or 1 × scale;
1. bisection on h alone, down to the lowest h still in T. This attacks h ≥ H_cert(state) sets;
2. bisection along a random direction to the boundary of T;
3. a random sample of T, from the seeds' bounding box widened by half its width;
4. a one-tick image: perturb a seed (ignoring T), fly up to 8 ticks, and take the first state that is in T.
   This catches memories that make T accept only states the law has "seen".

In addition:

- every seed on a stride is tested ("entry");
- 64 seeds get a 120 s long test.

All draws come from splitmix64 with seed 0xC172 + law index. `--seed N` overrides the seed for unofficial
probing. Counterexamples go to `ci-out/<sub>/t-counterexamples.csv`, one row each: the mode, the failure
(`alpha|load|speed|stall|clearance@tickK` or `no-climb@tickK`) and the raw vector.

The adversary judges T as a set of full model states. If T admits states with inconsistent derivative or
history fields, those states are in scope. A T meant to be proved should constrain them, as the baseline box
does.

## 5. Rules for competitors (the ratchet)

- **R1. Fixed files.** These may not change in a competing branch: `Ci/Interface.lean`, `Ci/Rules.lean`,
  `Ci/Goals.lean`, `Ci/Bench.lean`, `Ci/Report.lean`, `Ci/data/bench.csv`, `Tools/Score.lean`,
  `Tools/CiGen.lean`, `Jsb/Model.lean` and everything it imports, `lakefile.lean`, `lean-toolchain`. The check
  is `git diff <scoreboard commit> -- <those paths>`, which must be empty. The model, the safety definition and
  the physical limits are fixed. The laws, the terminal sets, the certificates and the methods are free.
  Competitors edit `Ci/Agent.lean`, `Ci/Audit.lean` and their own new modules.
- **R2. Ratchet.** Every iteration must be valid and must strictly improve the headline of the competitor's
  previous iteration. It appends one line to `docs/ci/log-<agent>.md`:
  `date | commit | headline | P Q R B | coverage | median h* | median ticks to T | one-line change`.
- **R3. Official score.** The official score is a full run (no `--quick`) with the default seed, on the
  committed benchmark. Competitors may add private tests, but only this run counts.
- **R4.** The static rule of §2.3.
- **R5. Honest memory and honest T.** T may depend on the state, h and law memory. The memory must be a state
  the law genuinely needs: integrators, the last elevator, a tick counter. Memory that exists to make T
  unreachable to the adversary is forbidden. Examples are a hash or signature of the state, a "trusted" flag,
  or a `dec` that rejects perturbed values. `inT` runs on every rollout tick, so it must be cheap: a table
  lookup or a few comparisons.
- **R6.** The benchmark and the adversary seeds never change within a competition. Maintainers may run extra
  seeds (`--seed`) or larger budgets. A counterexample found that way invalidates the iteration it was found
  in, even when the official run is clean.

### Anti-gaming notes

- **No hidden certification.** Acceptance is computed by the scoreboard's own rollout. A submission cannot
  report its own success, so there is no H to fit to the benchmark.
- **The only empirical soundness lever is T.** The adversary attacks T away from the benchmark's own
  trajectories (modes 0–4). Validity needs zero counterexamples. A proved T removes reliance on the adversary,
  and is worth more than any coverage gain.
- **Vacuous T.** An empty T is trivially "proved" but accepts nothing, so Q = R = 0.
- **Simulation inside T is ruled out statically (R4)**, together with copying the model under a new name (R1
  reviewers). The real-time budget is static (horizon × laws), so it cannot be gamed by timing tricks.
- **Wall-clock is reported, not scored.** An iteration whose median check exceeds a quarter of a tick on the
  reference machine should be questioned at review.
- **The benchmark cannot drift silently** because of the hash check, and its generator is deterministic.

## 6. How to run

Build one target at a time, and never run two `lake` processes at once.

```
lake build ciscore
.lake/build/bin/ciscore                     # official score of Ci.Agent.submission -> ci-out/agent/
.lake/build/bin/ciscore --sub box           # reference: steady-climb box
.lake/build/bin/ciscore --sub interior      # reference: box + crude interior
.lake/build/bin/ciscore --quick             # every 10th state, smaller adversary (not official)
.lake/build/bin/ciscore --seed 7            # extra adversary seed (maintainers)
.lake/build/bin/ciscore --trace I N         # print the first law's rollout from benchmark row I
.lake/build/bin/ciscore --fit               # regenerate the interior baseline's loss table
lake build cigen && .lake/build/bin/cigen gen Ci/data/bench.csv 250   # regenerate the benchmark
```

The program prints a human summary followed by one JSON line, also written to `ci-out/<sub>/score.json`. Its
exit code is 0 iff the score is valid. Per-state results are in `ci-out/<sub>/states.csv`, with the rejection
reason, e.g. `load@tick11`. A full run takes about 45–52 s on the development laptop (Apple silicon).

## 7. Reference scores (scoreboard commit)

Both references use the current law (`Jsb/Escape.lean`: full throttle, attitude target, elevator rate limit
1/16 per tick) with horizon 640. They are defined in `Ci/Baseline.lean`; `Ci/Agent.lean` starts as `interior`.

- **box**: T is a raw-unit box around the steady climb. It requires:
  - vx 39.7–41.2 m/s, vz 5.2–7.2 m/s, sin θ 0.175–0.237;
  - |q| ≤ 0.03 rad/s, elevator memory in [−0.46, 0];
  - rpm 2400–3000, h ≥ clearance;
  - AB history fields consistent.
- **interior**: box ∪ {h ≥ 2 × (worst box-baseline loss over the 4 typical-grid nodes around the current
  (V, γ)) + 30 m + clearance}, guarded by:
  - all 4 nodes accepted, V < 48 m/s;
  - α ≤ 0.2 rad, |q| ≤ 0.3 rad/s, rpm ≥ 600;
  - history fields consistent.

  A first version without the rpm guard was broken with adversary seeds 3 and 7 (not the default): a
  perturbed state with the engine stopped (rpm 0) never climbs.

| | valid | headline | Q | R | B | coverage | median h\* (m) | p90 h\* (m) | ticks to T, median / max | T tests, counterexamples |
|---|---|---|---|---|---|---|---|---|---|---|
| box | yes | 1.373 | 0.486 | 0.076 | 1 | 0.745 | 11.75 | 23.5 | 174 / 224 | 1302 + 64 long, 0 (also 0 with seeds 3 and 7) |
| interior | yes | 1.500 | 0.487 | 0.391 | 1 | 0.745 | 11.25 | 28.0 | 22 / 175 | 1227 + 64 long, 0 (also 0 with seeds 3, 7 and 11) |

- **Every rejection is the law's own envelope violation**, not a failure to reach T: 373 load-factor and 13 α
  violations.
- **fastdive is 2/250 accepted, because the current law pulls above 3.8 g** in fast steep dives. typical,
  push and elevtrans lose their fast, steep members for the same reason.
- **zoom and slowidle are fully accepted.** slowidle has the largest median h\* (17.5 m), from the law's
  low-speed sag.

So the next gains for competitors are, in order:

1. a load-limited or α-limited law, which raises coverage;
2. a proved T, which is worth +1;
3. a certified interior that is larger and lower, which raises R and lowers h\*.

## 8. Judgement calls and limitations

- **H is in metres above flat terrain at h = 0, and the rollout checks h ≥ 5 m directly.** Benchmark states sit
  near 1000 m. h\* moves the same state down, so it includes the density change and ground effect.
- **The load factor is the body-normal specific force.** The envelope study used the path-normal load factor;
  the two differ by thrust and drag terms of a few percent at most.
- **The 27 m/s floor sits below every benchmark commit** (the minimum is 28.0 m/s). α ≤ 0.28 is the binding
  stall guard.
- **T is checked only at tick boundaries.** Laws act once per tick, so substep membership has no meaning.
- **The adversary is empirical.** The interior baseline passes seeds 0xC172 (the default), 3, 7 and 11. An
  earlier version passed the default seed but failed on seeds 3 and 7, which is why R6 exists. Memory perturbation relies on `enc`/`dec`.
- **The model has no disturbances**, as the problem brief allows. The benchmark is generated, not flown by
  humans.
- **The filter induction (§1) is not formalised.** Only the T obligation carries proof credit.
