# Ansatz `envelope`: performance-envelope filter with commit-referenced escape bounds

Option owner: this branch (`eric/ansatz-envelope`). The design being made conformant is Luis's envelope filter
(`Envelope/` on `main`, `Envelope3D/` on `eric/envelope-3d`, fitted c172p numbers on `eric/envelope-params`).
The filter's safety proof is done for any trajectory satisfying the one-tick relation `Allowed`. This document
covers the missing half, **conformance**: does our fixed-point longitudinal model (`Jsb/Model.lean`), flown by
the escape law (`Jsb/Escape.lean`), satisfy the escape clauses of `Allowed`?

## 0. Verdict

- **Clause form.** Escape clauses have to be **referenced to the commit state** (the Envelope3D form), with
  parameters looked up by **commit cell (V_ref, γ_ref)**. Per-tick clauses fail on two counts. Parameters
  tuned separately for each commit state still give a bound 33 to 50 % above the actual loss on steep descents. With the fitted
  per-tick numbers the bound is 900 to 20 000 m, against an actual loss of 0 to 16 m. Among
  commit-referenced forms, path coordinates (a flight-path schedule driven by a load-factor floor) and
  Cartesian coordinates (a vertical-speed ramp) give nearly the same margins. Over the cells with γ_ref ≤ −0.1,
  the required height H is 12 % (path) or 9 % (Cartesian) above the worst sampled loss in the cell (median).
  The **proof** is easier in path coordinates. The transient becomes a nearly constant drop in flight path:
  0.014 to 0.019 rad over the descending cells, up to 0.052 rad from nose-high commits that are pushing over. The pull clause then needs exactly one lemma: a floor on the load
  factor. Recommendation: prove in path coordinates and keep Envelope3D's vertical-speed schedule as the
  monitored interface, with the schedule *generated* from path quantities (σ_k = V⁺·sin Γ_k, §1).
- **Margins.** Take the reference states, with parameters shared across each commit cell. H is within
  0.1 to 3.5 m of the worst actual loss in the cell, against actual losses of 0.2 to 17 m. The fitted μ=0.25
  envelope gives 6 to 470 m at the same states. Those parameters were fitted to a different plant and autopilot
  (JSBSim with the Python autopilot in `sysid/envelope/sim.py`), and our escape does not satisfy them in 1936 of
  2772 sampled runs (§5.3). Their size mainly reflects the clause form: a 35-tick delay, a pull band of
  0.187 m/s² below 42 m/s, and bands indexed by speed.
- **Conformance proof.** Several lemmas hold pointwise on honest regions: kinematics, rounding, the algebraic
  lift bound, the speed floor near the quasi-steady manifold, and the altitude comparison. One lemma is
  **open**: a *pitch-loop funnel*, an invariant set coupling (γ, α, q, elevator) with V. It must keep α above a
  floor during the pull (which gives the load-factor floor), below stall, and bound the transient.
  Numerically: a bounding box of the pull-phase states fails the one-tick pull clause at 3.2 % of samples. A
  data-fitted polytope with linear bands is not inductive: up to 29 % of its face points leave it in one tick.
  Multi-tick interval propagation reaches `top` within 4 ticks, even from a commit cell 0.01 m/s wide. So the
  invariant must be quadratic (or of higher degree) in the fast states. This is the same object the funnel
  option needs; the envelope option does not avoid it.
- **The escape law as written breaks two envelope obligations.** (1) The load factor reaches 5.1 (limit 3.8)
  for commits at V ≥ 51 m/s. (2) From V ≤ 35 m/s near level flight the law sinks first: speed has priority
  over attitude, so the loss is up to 6.4 m even from γ = +0.1. A load/α limiter and a floor on the attitude
  command would make the pull and load clauses pointwise-provable. These law changes are proposed, not
  evaluated.

## 1. The certificate

### 1.1 Escape clauses (replacing `ModeOK .escape` of Envelope3D)

Commit cells c are a table over (V_ref, γ_ref) (here 2 m/s × 0.05 rad). Each cell carries:

| parameter | meaning | typical value (§5) |
|---|---|---|
| `K_c` | transient length, ticks | 6 to 10 (32 to 48 for low-speed near-level cells) |
| `δγ_c` | flight-path drop allowed during the transient, rad | 0.014 to 0.019 for descending cells (all variants); up to 0.18 for low-speed near-level cells, whose long flat window absorbs the law's initial sink |
| `n_c` | path-normal load-factor floor after the transient, while γ < 0 | 1.08 (V=35, γ=0) to 3.4 (V=59, γ=−0.3) |
| `V⁺_c`, `V⁻_c` | airspeed band during the descent part of the escape | V⁺ = V_ref + 0 to 6 m/s; V⁻ = min(V_ref − 1.6, 40.8) m/s, and never below 31.4 |
| climb-out | terminal band: V ∈ [40.8, 41.1], vz ≥ 6.1 (shared by all cells) | |

Flight-path schedule (the law's guaranteed flight path, computed offline per cell):

    Γ_0 = γ_ref − δγ_c,   Γ_{k+1} = Γ_k (k < K_c),   Γ_{k+1} = min(0, Γ_k + dt·g·(n_c − cos Γ_k)/V⁺_c) (k ≥ K_c)

Monitored escape clauses for the tick k → k+1 (abstract state (x, h, vx, vz, V), ref = commit state):

- **(E1) flight path:** `vz' ≥ V'·sin Γ_{k+1}`. This is `sin γ' ≥ sin Γ_{k+1}`. It is linear in the observed
  values once `sin Γ_{k+1}` is a rational table entry, so there is no trigonometry at runtime.
- **(E2) speed band:** `V⁻_c ≤ V'`, and while `Γ_{k+1} < 0` also `V' ≤ V⁺_c`.
- **(E3) climb-out:** once the schedule has reached 0 and the climb-out has been entered, V' is in the
  climb band and `vz' ≥ 6.1`.
- **Common clauses** unchanged (`hSlack`, `pSlack`, ground-speed range). Measured requirements: hSlack 0.001 m,
  sag 0.018 m.

(E1) and (E2) imply the Envelope3D-style vertical-speed floor `vz' ≥ σ_{k+1} := V⁺_c·sin Γ_{k+1}` while
`Γ < 0`. So the existing box recurrence (`escStep`, `escLoop`) and its proof carry over unchanged, with
`sched.vz` replaced by σ. The Cartesian alternative B is `σ_k = vz_ref − D_c` for k ≤ K_c, then
`+ a_c·(k−K_c)·dt`, capped at 0. B is the Envelope3D schedule with per-cell D and a. Its margins are in §5.

### 1.2 Required height and the filter check

    H(ref) = max_j  Σ_{i<j} −dt·min(σ_i, σ_{i+1})   (σ_0 = vz_ref),  plus Envelope's sag, margin, and hSlack·(ticks to σ = 0)

The runtime filter is Envelope3D's `escapeClear`, unchanged: one free tick (`freeBox`/`freeRef`), then the
worst-case box recurrence against terrain using the cell's schedule. The runtime cost is a table lookup plus at
most about 60 schedule entries per tick, which can also be precomputed per cell as a list.

### 1.3 Choosing the parameters

The parameters are fitted per cell from simulations of the Fx model under the escape law, over a sample of
commit variants (`sysid/envconf/cells.py`). Fitting is not the soundness argument; conformance (§2 to §4) is.
In the proof, each parameter is an output of a lemma: `δγ_c` from the transient lemma, `n_c` from the funnel
plus the lift lemma, `V±` from the speed lemmas. The fit only shows how much margin those lemmas may lose before
H degrades.

## 2. Theorem to formalize

Fix a cell c with commit box Q_c:

- V ∈ [V_c ± 1], γ ∈ [γ_c ± 0.025]
- α − α_trim(V, γ) ∈ [−0.03, 0.05], q ∈ [−0.1, 0.15]
- e_prev = the trim elevator, rpm/tmap settled at idle or full throttle
- history fields consistent with the last evaluation (as in `ContProbe.consistent`)
- h ≥ 100 m (no ground effect)

Let c_0 ∈ Q_c, c_{k+1} = `Escape.tick` c_k in `Fx`, and ref = the abstract state of c_0. Then for all k:

1. `Allowed P (.escape k ref) (abs c_k) _ (abs c_{k+1})` with the clauses of §1.1;
2. validity: α_k ≤ α_max = 0.28 (the CL peak of `tbl_x_5`), n_k ≤ n_max = 3.8, V_k ≥ 31 m/s,
   stall bit = 0;
3. there is k_c ≤ 320 with c_k in the climb-out set for all k ≥ k_c.

Combined with the existing `NeverHits` proof, this gives: the filter "commit when h − terrain ≤ H(ref) + one
free tick" keeps every escape clear of terrain, with the escape flown by the detailed model.

## 3. Informal proof

Notation: n := (vx·au − vz·ah)/(g·V) + cos γ, the path-normal load factor computed from the evaluated world
accelerations. a_t := (vx·ah + vz·au)/V is the along-path acceleration.

**L0 (representation and rounding).** One tick is 8 substeps. Each substep's vz and vx increments are exact
AB2 combinations of evaluated (au, ah) (pilot, item 2). Each evaluation differs from the real vector field by
at most ε_a = 0.0042 m/s² on au, and similarly on ah and qd (`proofs/Proofs/Continuous`). So every
inequality below, stated for the real field with margin m, holds for Fx if m exceeds the propagated rounding.
The tick-level effect is below 10⁻³ m/s, three orders under the margins of §4. *Cost:* already in the pilot's
style.

**L1 (kinematics, pointwise).** For one tick:

    γ_{k+1} − γ_k = Σ_substeps (1/128)·g·(n − cos γ)/V + R

with |R| ≤ C·dt²·(|au|+|ah|)²/V² from the atan2 of (vx, vz). This is the real-analysis identity of the AB2
update and atan2's Lipschitz bound. Similarly V_{k+1} − V_k = Σ (1/128)·a_t + R′.

**L2 (lift lemma, algebraic, pointwise).** On the escape region:

    n ≥ N(V, α, e, q, α̇, rpm) := [q̄S(C_Lwbh(α) + C_Lδe·δe + C_Lq·q·c̄/2V − |C_Lα̇|·|α̇|·c̄/2V) + T·sin α]/W

N is nondecreasing in α for α ≤ 0.28. This is the same style as `AuBound.lean` (piecewise-linear table, monotone
pieces).

**L3 (transient, k ≤ K_c).** The elevator moves at most 1/16 per tick, an exact property of `command`. The
commit cell bounds α_0, q_0, e_0. *Needs:* a bound on (α, q) over K_c ticks, which a crude derivative bound
cannot give: |q̇| up to about 4 rad/s² gives ±2 rad/s after 0.5 s. A short-period energy function
(L5) then gives n ≥ n_T and so γ_k ≥ γ_0 − K_c·dt·g·(1 − n_T)/V⁻. Speed:
V_k ≤ V_0 + K_c·dt·A⁺, where A⁺ is a pointwise upper bound on a_t (thrust minus drag minus g·sin γ).

**L4 (pull, k ≥ K_c, γ < 0).** Inside the funnel F of L5, α ≥ α_P(V, γ), so L2 gives n ≥ n_c. Then L1 gives
the per-tick inequality γ_{k+1} ≥ γ_k + dt·g·(n_c − cos γ_k)/V⁺_c − ε. Since the schedule map
Γ ↦ Γ + dt·g·(n_c − cos Γ)/V⁺ is increasing (dt·g/V⁺ < 1), induction gives γ_k ≥ Γ_k (comparison
lemma). (E1) follows.

**L5 (pitch-loop funnel, the open lemma).** There is a set F_c(k) ⊂ (V, γ, α, q, e, rpm, histories) with:

- (a) c_0 ∈ Q_c implies c_k ∈ F_c(k) (by induction, through a one-tick inclusion);
- (b) F_c(k) ⊂ {α ≥ α_P(V, γ)} for k ≥ K_c and γ < 0 (gives L4);
- (c) F_c ⊂ {α ≤ α_max, n ≤ n_max} (stall and load limits);
- (d) F_c ∩ {V = V⁻} ⊂ {a_t > 0} (speed floor; this is the V–attitude coupling the pilot asked for).

The natural shape is a sublevel set {W(z; V) ≤ ρ_k}. Here z = (γ, α, q, e) − z*(V, k) is the deviation
from a nominal pull, W is quadratic (or SOS), and ρ_k shrinks from the commit box to a tube. The obligation is
one-tick: c ∈ ∂F(k) implies tick(c) ∈ F(k+1), checked on cells by the interval machinery
(`Jsb/Conformance.lean`, `checkRec`). Why not something simpler: see N5 to N7. The law's rate limiter and
saturation give a sector nonlinearity that W must absorb. For the transient they are deterministic: e ramps
at exactly 1/16 per tick until it reaches the target.

**L6 (speed band).** V⁺: pointwise a_t ≤ A⁺ during the descent part, times the descent time bounded by
Γ reaching 0. V⁻: the transient loss (L3) plus (d) above. Pointwise fact used: at the frozen-(V, γ) fast
equilibrium with full power, a_t ≥ 0.94 m/s² for all V ≤ 37, γ ≤ 0.05 (N8). So the law's speed priority
returns V upward once the fast states are near their quasi-steady values.

**L7 (climb-out).** Every sampled escape converges to the single equilibrium V = 40.9, γ = 0.152, vz = 6.2. A
local quadratic Lyapunov function of the linearized one-tick map around it gives a terminal invariant set
inside the climb band. Entry follows from L4 to L6: the schedule reaches 0 within 3 s, and the funnel's tube
lands in the terminal set's basin. This piece is standard and shared with every other option.

**L8 (altitude).** AB3 altitude update and sag: h' ≥ h + dt·min(vz, vz') − hSlack, with hSlack = 0.001 m and
sag 0.018 m measured. With (E1) and (E2), vz ≥ V⁺·sin Γ while Γ < 0, and Envelope3D's box recurrence and
`NeverHits` proof apply verbatim.

## 4. Numerical evidence, lemma by lemma

Data: 2772 escapes from the commit grid V ∈ {33, 35, …, 59} × γ ∈ {−0.4, −0.35, …, 0.1} × throttle {idle,
full} × α offset {−0.03, 0, +0.05} × q {−0.1, 0, 0.15}, each 320 ticks in `Fx`. Trims are solved in `Float`;
histories are made consistent. All numbers come from `Tools/EnvConf.lean` and `sysid/envconf/*.py`.

| # | statement | status | margin / where it fails |
|---|---|---|---|
| N1 | L0 rounding | holds (pilot) | ≤ 0.0042 m/s² per evaluation; ≤ 10⁻³ m/s per tick |
| N2 | Common clauses: hSlack, sag | hold | needed 0.001 m / 0.018 m (fitted 0.017 / 0.04) |
| N3 | transient: γ_k ≥ γ_0 − δγ for k ≤ 9 | holds on trajectories with δγ = 0.052 overall | settled commits ≤ 0.001; descending cells over all variants 0.014 to 0.019. Worst: V=33, γ=+0.1, q_0 = −0.1 (pushing). Pointwise "n ≥ cos γ in the transient" is **false**: min n − cos γ = −0.54, from commits with q_0 < 0 |
| N3b | transient: elevator ramps monotonically up | **false** in 751 of 2016 descending commits | the −1.5·q term lowers the target first when q_0 > 0; the step is −1/16 at worst. So the transient cannot be argued from "e only increases" |
| N4 | pull clause (E1) with per-cell n_c | holds on all trajectories by construction | n_c in §5; schedule parameters per cell in `cells.csv` |
| N5 | L4 pointwise on the **bounding box** of pull-phase states (V_ref = 45 cells, 4000 corner/uniform points, one Fx tick) | **fails** at 3.2 % | worst −0.0022 rad/tick against 0.0106 needed. Failures sit at box corners pairing the lowest α (seen only near γ → 0) with the steepest γ (seen only at the start) |
| N6 | same on a **data-coupled** region (e and q within linear bands of (V, γ, α)) | fails at 0.1 % | worst −0.0003 rad/tick; the remaining failures are low α with steep γ again, so α must be coupled to γ |
| N7 | inductiveness of a fitted **polytope** (α floor linear in (γ, V), e/q bands, α ≤ 0.28, V band) | **not inductive** | faces left within one tick: α floor 5 %, e band 29 %, q band 14 %, V band 1 %, α max 1 %. Linear faces cannot follow the rotating short-period motion, so a quadratic W is needed (L5) |
| N7b | multi-tick interval reachability as an alternative to L5 | **infeasible** | interval width grows 3 to 4× per tick (q up to 10×); `top` within 4 ticks even for a cell of ±0.01 m/s, ±0.0005 rad |
| N8 | L6 speed floor near the quasi-steady manifold: a_t at the frozen-(V, γ) fast equilibrium, full power | holds | a_t ≥ 0.94 m/s² for V ∈ [31, 37], γ ∈ [−0.45, 0.05] |
| N8b | speed floor overall | holds on trajectories | V_min = 31.43 m/s (commit V=33, γ=+0.1, idle, α +0.05, q +0.15), during the transient |
| N9 | stall: α ≤ 0.28 | holds on trajectories, margin 0.027 | α_max = 0.253 (11 runs above 0.25, all steep, fast commits). **Not a pointwise property of the law:** the frozen-γ fast equilibrium has α* > 0.28 for V ≥ 41, γ ≤ −0.3 (full elevator). Stall is avoided only because γ rises in time, which is exactly what L5 must capture; an α limiter in the law would make it pointwise |
| N10 | load: n ≤ 3.8 | **fails** for V_ref ≥ 51 | n_max = 5.13; 324 of 2772 runs exceed 3.8. The commit region must stop at V ≤ 49, or the law needs an n-limiter |
| N11 | climb-out | holds on trajectories | at k = 320: V 40.84 to 41.04, γ 0.152 to 0.157, vz 6.18 to 6.43. The 210 runs with γ < 0 after k = 40 all commit at V ≤ 35 (low-speed sag, below) |
| N12 | low-speed sag | a property of the law | from V_ref ≤ 35 and γ_ref ≥ 0 the law first descends (attitude target sin θ_C = 0.15 + 0.02·(vx − 38) is about 0.05 at 33 m/s), losing up to 6.4 m. The path clause then needs long K_c (32 to 48) and δγ up to 0.18; n_c ≤ 1 in the flat part |

## 5. Margins

### 5.1 Reference states

The reference states are settled trims (q = 0, zero path-normal and pitch acceleration) at h = 1000 m.
"Cell worst" is the largest loss over the 18 commit variants of the cell (throttle × α offset × q). All values
are altitude losses in metres; margin and terrain clearance are excluded.

| V | γ | approx. outer | actual, idle | actual, full | actual, cell worst | H path (C), per cell | H Cartesian (B), per cell | H per-tick (A), oracle | H μ=0.25 (3D semantics) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 35 | −0.30 | 5.8 | 16.0 | 11.7 | 17.0 | 20.5 | 18.7 | 23.9 | 466.8 |
| 35 | −0.15 | 1.5 | 8.0 | 4.7 | 8.9 | 10.6 | 9.9 | 11.0 | 175.3 |
| 35 | 0 | 0 | 2.3 | 0.0 | 2.7 | 4.0 | 3.8 | 9.2 | 21.7 |
| 45 | −0.30 | 4.2 | 13.5 | 10.8 | 14.4 | 16.3 | 15.8 | 18.3 | 117.8 |
| 45 | −0.15 | 1.1 | 5.1 | 4.0 | 5.9 | 6.5 | 6.3 | 6.8 | 48.6 |
| 45 | 0 | 0 | 0.0 | 0.0 | 0.2 | 0.3 | 0.3 | 0.0 | 7.5 |
| 55 | −0.30 | 4.9 | 14.4 | 12.0 | 15.4 | 17.2 | 16.8 | 19.7 | 88.3 |
| 55 | −0.15 | 1.2 | 5.6 | 4.6 | 6.3 | 7.1 | 6.9 | 7.7 | 39.0 |
| 55 | 0 | 0 | 0.0 | 0.0 | 0.2 | 0.4 | 0.4 | 0.0 | 6.3 |

- **The V = 55 rows are outside the certifiable region as the law stands.** The load factor reaches
  3.6 to 4.3 (N10).
- **Outer bound (approximate).** Point mass, instantaneous pull to min(3.8, n at CL_max), V held at V_ref:
  V²/g·ln((n − cos γ)/(n − 1)). It ignores the short-period lag that any real elevator input incurs, so the
  true outer bound is larger. The remaining slack splits roughly into the escape law's own transient and pull
  shape (actual − outer: 6 to 11 m on the γ = −0.3 rows) and the certificate's slack (H − actual: 1 to 3.5 m).
- **Per-tick oracle (A).** Even with parameters tuned to the single state, the per-tick form is 33 to 50 %
  above actual on steep rows (and 9.2 against 2.3 at V = 35, γ = 0). It must cover the worst per-tick drop for
  every delay tick, and the weakest single-tick pull.
- **Over all cells with γ_ref ≤ −0.1:** H_C/actual has median 1.12 and max 1.24 (largest gap +4.9 m, at
  V = 33); H_B/actual has median 1.09 and max 1.15. The near-level cells (low-speed sag) have gaps up to
  +6.9 m (C) and +7.2 m (B).

### 5.2 Fitted per-cell parameters (selected)

| V_ref | γ_ref | K (C) | δγ | n_c | V⁺ | K (B) | D (m/s) | a (m/s²) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 35 | −0.30 | 8 | 0.015 | 1.53 | 39.2 | 8 | 0.71 | 4.7 |
| 35 | −0.15 | 6 | 0.017 | 1.25 | 38.0 | 6 | 0.61 | 2.3 |
| 35 | 0 | 32 | 0.038 | 1.08 | 36.4 | 32 | 1.30 | 0.72 |
| 45 | −0.30 | 10 | 0.015 | 2.64 | 47.3 | 10 | 0.87 | 15.5 |
| 45 | −0.15 | 8 | 0.015 | 2.21 | 46.4 | 8 | 0.70 | 11.6 |
| 55 | −0.30 | 8 | 0.014 | 3.04 | 56.9 | 8 | 0.95 | 19.4 |

Compare the μ=0.25 fit: delay 35 ticks, total vz drop 2.19 m/s, pull 0.187 m/s² below 42 m/s, 1.5 m/s²
from 42 m/s, 3.75 m/s² from 50 m/s. Our law's transient is 6 to 10 ticks, and its pull is already 4.7 m/s² at
(V_ref, γ_ref) = (35, −0.3).

### 5.3 Does our escape satisfy the fitted μ=0.25 envelope?

No (`sysid/envconf/mu025_conf.py`, Envelope3D semantics). Of the 2772 runs:

- 1936 break the airspeed floor `V_ref − escVDrop`, because our law bleeds speed to its 41 m/s climb speed.
- 1076 break the vertical-speed schedule. At V_ref ≥ 51 the climb band is indexed by commit speed and asks
  for 12.3 m/s, but our law settles at 6.2 m/s. At V_ref ≤ 37 the low-speed sag exceeds the 2.19 m/s drop.
- 10 break vMin = 32.

So beyond being conservative, the fitted clauses have the wrong form for this law (§6).

## 6. What the envelope design must change for conformance to be provable

1. **Commit-referenced, not per-tick (adopt Envelope3D).** The per-tick 2D reading of the fitted numbers
   compounds the delay drop to 35 × 2.19 m/s (H of 900 to 20 000 m). Even the per-tick form with oracle
   parameters is 33 to 50 % worse than the commit-referenced form on steep rows. More importantly, no per-tick
   clause holds through the transient, as the pilot's counterexample showed.
2. **Index parameters by commit cell (V_ref, γ_ref), not by bands of current airspeed with a weak base band
   at vMin.** The pull available to this law depends strongly on γ_ref, not only on speed: n_c is 3.0 at
   (55, −0.3) and 2.1 at (55, 0). Worst-case boxes that drift into the base band waste almost all the
   authority.
3. **Model the "delay" as a short transient with a total drop in flight path.** It is not a pure delay: it is
   the elevator rate limit (1/16 per tick), the short-period response, and engine spool-up, the last of which
   matters for V but hardly for γ. In path coordinates the drop is 0.014 to 0.019 rad over the descending cells
   and at most 0.052 from pushing commits (q_0 = −0.1). In Cartesian coordinates the drop D = 0.55 to 1.3 m/s
   depends on throttle and γ_ref, because it contains a_t·sin γ.
4. **The speed clause must allow bleeding to the climb speed.** Replace `V_ref − escVDrop` by a band
   [V⁻_c, V⁺_c]. Also add the upper bound V⁺: the flight-path form needs it to turn sin γ into vz.
5. **Index the climb guarantee by the climb-out state, not the commit state.** Use a terminal "climb-out"
   mode as in Envelope3D, with its own band.
6. **Load and stall limits need either a commit region bounded at V ≤ 49 m/s or a limiter in the law** (N9,
   N10). With an α/n limiter, L5(c) becomes pointwise.
7. **Low-speed commits.** Either accept long flat transients (K = 32 to 48, costing up to +7 m in H near level
   flight at V ≤ 35), or add a floor to the law's attitude target (sin θ_C ≥ 0.12). With full power the
   aircraft can then hold level at 33 m/s and gain speed, so the pull clause holds from every commit. This is
   proposed and not evaluated.

## 7. Gaps and formalization cost

**Assumed.**

- The commit box Q_c is the set of pilot states at commit, sampled here by 18 variants per cell. In the
  formal setting it must be the free-flight relation's one-tick image, which ties to `freeBox`/`freeRef`.
- tmap in the one-tick checks was set to the throttle's target value, which is slightly optimistic on thrust
  for k < 16. tmap is not logged in the trajectories.
- No disturbance, as the brief allows.
- The per-cell parameters are fitted on samples. The proof must re-derive them from L3 to L6 with their own
  slack.

**Cost estimates.**

- **Cheap to moderate, 2 to 4 weeks:** L0, L1 and L2 (single-evaluation real analysis and table monotonicity,
  in the style of `AuBound.lean`, plus interval checks of one evaluation); L8 and the comparison lemma in L4
  (rational arithmetic); and porting Envelope3D's proofs with σ := V⁺·sin Γ (sin Γ is a rational table, and
  the proof only uses σ's monotonicity).
- **Hard, the main risk, 2 to 4 months:** L5, the pitch-loop funnel.
  1. Fit W (quadratic or SOS, per cell or with V as a parameter) to the sampled one-tick map, with an SDP
     solver offline.
  2. Prove the one-tick inclusion on ∂F by interval bisection over cells in about 8 dimensions (fast states,
     V, rpm, and the history fields constrained linearly as in `EscapeRegion.cons`).

  The pilot showed one-tick interval checks are feasible on boxes about 10 % of a region with 4 to 16 leaves.
  F's boundary is a thin shell, so cell counts are the uncertain quantity. Multi-tick interval propagation is
  ruled out (N7b).
- **Climb-out terminal set L7:** standard, about 2 weeks. It is shared with other options.

**Extension to JsbExact (6-DOF, Float).**

- The path quantities generalize directly: the pull clause uses the vertical component n·cos φ.
- Envelope3D's roll-out phase (`bankCap`, `rollStep`) precedes the γ-schedule: Γ stays flat until |φ| ≤
  `bankLevel`.
- Float rounding enters only through L0's per-evaluation bounds.
- The funnel L5 gains (p, r, β, φ). Lateral recovery would need its own funnel for the roll-out, with the same
  one-tick-on-the-boundary obligation.
- The rest of the envelope argument (box recurrence, NeverHits) is already 3D.

## 8. Reproduction

All on branch `eric/ansatz-envelope`; build one target at a time.

    lake build envconf
    .lake/build/bin/envconf grid /tmp/envconf/grid.csv 320 spec.txt -0.03,0,0.05 -0.1,0,0.15   # spec: "h V gam thr" lines
    .lake/build/bin/envconf fly /tmp/envconf/ref.csv 640 <h V gam thr dal q0>...              # reference states
    .lake/build/bin/envconf reach 1000 45 -0.3 0 0.01 0.0005 0.0002 0.0005 4                  # interval widths (N7b)
    .lake/build/bin/envconf qs /tmp/envconf/qs.csv                                            # fast equilibria (N8, N9)
    cd sysid/envconf
    uv run --with pandas python forms.py /tmp/envconf/ref.csv /tmp/envconf/ref_forms.csv      # forms A/B/C per state
    uv run --with pandas python cells.py /tmp/envconf/grid.csv /tmp/envconf/cells.csv         # per-cell B/C, §5
    uv run --with pandas --with numpy python stats.py /tmp/envconf/grid.csv                   # N3, N9 to N11
    uv run --with pandas --with numpy python pullbox.py /tmp/envconf/grid.csv 45 10 /tmp/envconf/pts45.txt   # N5, N6
    uv run --with pandas --with numpy python pullinv.py fit|sample|check ...                  # N7
    uv run --with pandas python mu025_conf.py /tmp/envconf/grid.csv                           # §5.3
    uv run --with pandas --with tabulate python reftable.py                                   # §5.1
