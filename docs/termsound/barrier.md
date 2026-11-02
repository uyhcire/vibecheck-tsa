# Energy barrier: membership of the level-off loop (issue #58)

Family "energy barrier" of #58, for the level-off of the terminal escape law (`docs/escape-law-terminal.md`) at
about 1,000 m. Reproduce with `make barrier` (or `make barrier K="128 512"`); scripts in `Tools/termsound/`:
`barrier.py` (the property, `B`, `U`, `R`), `barrier_search.py` (adversarial search), `barrier_size.py` (box sizing),
`barrier_run.py` (the table).

**Status: falsified for every k tried.** The barrier direction itself holds where it was expected to: at
k = 512 frames (4 s), on θ₀, the adversarial search finds no state in the band whose `B` ends below `b` (worst +8.0 m) and no frame from `S` below
`zTop + e` = 941 m (worst +3.8 m). Everything else fails: the region `R` is not mapped into itself (C2: the upper
altitude face by about 10 m, and no lateral box size closes), the largest 4-second drop of `B` (49 m) exceeds the
band (30 m), and at k = 1, 16, 64 and 128 C1 fails too. Six variants that close one of these reopen another at a
corner of `R` (slow zooms, fast steep climbs) that explicit boxes force `R` to contain. Nothing is validated: the
interval tool (`TsInterval.frameBox`) is sound only on boxes about 1e-6 rad wide in pitch and panics (unsoundly)
on metre-scale boxes. C4 is proved by construction for every θ.

## Target

- `f` = one frame (1/128 s) of `JsbExact` (fuel frozen) under the candidate law `NEW` of `terminal.py`
  (`tsmap`, plain loop, `Cand` with `hLevel` 1000, `kHold` 0.005), holding track east (ψ = π/2) at latitude 0.
- States are `tsmap` charts `(h, y[32])` (`TsMap.lean` `chart`/`place`).
- Level trim `x*` (`Tools/termsound/barrier_trim.json`, copied from `level_cert2.py`): h* = 1000.2166 m,
  V* = 70.7807 m/s, θ* = −0.021909 rad.
- Floor `F = zTop + e = 934 + 7 = 941 m` (`e` = 7 m, the `CrashH 7` airframe margin of `termsound-proof.tex` §1).

## The property P[θ](f)

Notation: `V = |(v_al, v_rt, v_dn)|`, `v_z = −v_dn`, `γ = asin(v_z / V)`, `g = 9.80665`.

**Barriers.**

```
B(x) = h − w1·max(V*² − V², 0)/(2g) − wl·max(−v_z, 0) − wq·max(−v_z, 0)²
U(x) = h + uV·max(V² − V*², 0)/(2g) + ul·c + uq·c²,   c = max(min(v_z, v_z − V·0.005·(1000 − h)), 0)
```

`B` is altitude less two penalties: for flying slower than the level trim (kinetic-energy deficit, weight `w1`) and
for descending (a stopping-distance estimate: delay `wl` plus `v_z²/(2a)` with `wq = 1/(2a)`). `U` is the mirror
image for the top of the region: altitude plus the energy surplus and a stopping distance for climbing faster than
the level-off command. Both penalties have a fixed sign, so **`B ≤ h` and `U ≥ h` everywhere**.

**Region R** (all bounds explicit):
- `V_lo ≤ V ≤ V_hi`, `γ_lo ≤ γ ≤ γ_hi`, `U(x) ≤ u_hi`;
- `|Δα| ≤ dα`, with `Δα = θ − θ* − γ` (pitch relative to the flight path, i.e. α to first order);
- for every boxed quantity `q` (half-widths in the contract section): `|q(x) − q(x*)| ≤ w_q`. The boxed quantities are the chart
  coordinates `φ, Δψ, p, q, r, Δv⁰, a⁰, ṗ, q̇, ṙ, u̇, v̇, ẇ, rpm, MAP, ia, ib, iφ`, plus
  `β = v_rt/V − Δψ` (in place of `v_rt`), `Δa = a¹ − a⁰` (in place of `a¹`) and `Δ²v = Δv¹ − Δv⁰` (in place of
  `Δv¹`). Independent boxes on `v_rt` and on the integrator histories `a¹`, `Δv¹` have corners that no flight
  reaches (a sideslip of several degrees, or a previous-frame acceleration 24 m/s² away from the current one).

**Conditions** (k frames per step, threshold `b`, band `Δ`, slack `ε`):

| | condition |
|---|---|
| C1 | `x ∈ R`, `b ≤ B(x) ≤ b + Δ` ⟹ `B(f^k x) ≥ b` |
| C1′ | `x ∈ R`, `B(x) ≥ b` ⟹ `B(f^k x) ≥ B(x) − ε` |
| C2 | `x ∈ R`, `B(x) ≥ b` ⟹ `f^k x ∈ R` |
| C3 | `x ∈ R`, `B(x) ≥ b`, `0 < j ≤ k` ⟹ `h(f^j x) ≥ F` |
| C4 | `x ∈ R`, `B(x) ≥ b` ⟹ `h(x) ≥ F` |
| side | `ε ≤ Δ`, `b ≥ F` |

C1′ with `ε ≤ Δ` is what makes C1 enough: a state above the band cannot jump below `b` in one step. Together,
C1, C1′ and C2 make `S = R ∩ {B ≥ b}` invariant under `f^k`; C4 covers the frames `0, k, 2k, …` and C3 the frames
in between, so every frame from `S` stays at or above `F`. **C4 holds by construction** (`B ≤ h` and `b ≥ F`), on
exact reals, for every θ of this form.

## Why this form

At the level trim the speed term of the law is saturated (`gcC` = `GC_HI_T` = 0.5 at 70.8 m/s), so the commanded
flight-path gradient is the altitude hold alone, `0.005·(1000 − h)`, clamped to ±0.35. Throttle is fixed at 1.0.
Near the floor the law therefore commands a strong climb (0.30 rad at 941 m), and what threatens the floor is:

- **descending**: the aircraft keeps sinking until the pull-up arrests it. Measured on the real loop from 945 m with
  pitch at the flight path plus trim α, other states at trim (`stopping` in `barrier_run.py`): the altitude lost is
  1.2, 3.6, 6.9 and 11.4 m from 5, 10, 15 and 20 m/s of descent, which fits `τ·|v_z| + v_z²/(2a)` with
  τ = 0.14 s and a = 23 m/s² to 0.01 m. Hence the `wl·|v_z| + wq·v_z²` penalty; the defaults (0.15 s, 0.03 s²/m,
  i.e. a = 17 m/s²) are more conservative than the fit, because adversarial α and pitch rate delay the pull-up;
- **slow flight**: lift authority falls with V², and at full throttle a slow aircraft regains speed only by
  giving up the climb. The penalty `w1·(V*² − V²)/(2g)` is the kinetic-energy deficit counted as height. With
  `w1 = 1` it is total energy, which fails C1: a hard pull-up dissipates energy (induced drag at high α), so total
  energy *falls* during the recovery that saves the aircraft. `w1 < 1` credits the altitude gained.

Climbing and flying fast are never credited, which is what makes `B ≤ h` and C4 free. The upper barrier `U` is
needed only because `R` must be invariant (C2): a box `h ≤ h_hi` is left by any state climbing at its face, while a
state at low altitude climbing at the commanded rate is no threat to the top, hence the climb bonus counts only
climb in excess of the level-off command.

## Search

For each θ and condition, the worst point of `R` (or of the band) is searched on the real loop (`tsmap` `S`,
every frame), not sampled:
- 256 uniform points and 256 random vertices of the box (`u ∈ [0,1]^33` decodes to a state of `R` with `B ≥ b`;
  the last coordinate places `h` between `B = b` and `U = u_hi`, or inside the band for C1);
- differential evolution (scipy, population 264) seeded with the worst of those;
- Nelder–Mead (adaptive, bounded) from the four best points.

About 3,000–4,000 real-loop rollouts per condition. Before the search, `barrier_size.py` sizes the boxes for C2 by
a fixed point: run the C2 search, widen every box whose image exceeded 0.9 of it, repeat (5 rounds).

## Results

All numbers are **measured** (adversarial search on the real loop); none is validated or proved except C4.
Margins: C1 is `min B(f^k x) − b` over the band (≥ 0 holds); "drop" is `max B(x) − B(f^k x)` over `S`, the `ε`
C1′ needs, to compare with `Δ`; C2 is `1 − max excursion` (≥ 0 holds; for the `U` face one unit is 10 m); C3 is
`min h − F` over frames `1..k` (≥ 0 holds); C4 is `b − F`.

**θ₀** (`THETA0` in `barrier.py`): `w1 = 0.5`, `wl = 0.15 s`, `wq = 0.03 s²/m`, `b = 946 m`, `Δ = 30 m`;
`uV = 1`, `ul = 0.15 s`, `uq = 0.08 s²/m`, `u_hi = 1065 m`; `V ∈ [50, 86] m/s`, `γ ∈ [−0.4, 0.4]`, `dα = 0.12`;
boxes `FAST0` (about 1.5× the largest excursion seen after 2 s in 60 rollouts of 30 s from level-off starts).

| k | boxes | C1 | drop vs Δ | C2 (binding face) | C3 | C4 |
|---|---|---|---|---|---|---|
| 1 | base | **−0.34 m** | 0.44 vs 30 | **−120** (Δa_al) | +5.01 m | +5 m |
| 16 | base | **−8.19 m** | 8.41 vs 30 | **−6.9** (ẇ) | +4.87 m | +5 m |
| 64 | base | **−6.27 m** | 14.6 vs 30 | **−7.4** (a⁰_rt) | +4.50 m | +5 m |
| 128 | base | **−2.63 m** | 24.0 vs 30 | **−7.1** (a⁰_rt) | +4.41 m | +5 m |
| 512 | base | +8.50 m | **49.2 vs 30** | **−1.5** (a⁰_rt) | +4.26 m | +5 m |
| 1 | sized | **−4.43 m** | 4.42 vs 30 | **−1.06** (U) | +5.00 m | +5 m |
| 16 | sized | **−11.6 m** | 12.3 vs 30 | **−3.7** (U) | +4.83 m | +5 m |
| 64 | sized | **−43.5 m** | **56.6 vs 30** | **−167** (Δ²v_rt) | +2.78 m | +5 m |
| 128 | sized | **−126 m** | **111 vs 30** | **−219** (Δ²v_rt) | **−17.8 m** | +5 m |
| 512 | sized | +8.00 m | **49.3 vs 30** | **−1.01** (U, 10 m over) | +3.82 m | +5 m |

"base" rows: `barrier_run.py --base 1 16 64 128 512` (boxes as in θ₀); "sized" rows: `make barrier`, after 5 rounds of `barrier_size.py`. Sizing converges nowhere: at k ≤ 128 it diverges (the boxes grow
by 1.2–8× per round, and at k = 128 they reach 2.6 rad of heading error, which drags C1 and C3 down with them); at
k = 512 it stalls at a C2 margin of about −0.3 with the lateral boxes (`φ`, `Δψ`, `β`) still growing about 1.3× per
round. Each row is about 3,900 rollouts per condition after sizing (5 × 2,433 for the sizing itself).

Variants at k = 512 (boxes started from the sized k = 512 row, sized again), trying to close C2 and `ε ≤ Δ`:

| variant (overrides of θ₀) | C1 | drop vs Δ | C2 (face) | C3 | what broke |
|---|---|---|---|---|---|
| A: `ul 0.3, uq 0.1, Δ 55` | **−8.44 m** | 46.8 vs 55 | **−4.2** (U) | **−1.14 m** | slow state high up (h 1028, V 51) descends to 1000: `B` falls with `h` while the slow penalty stays |
| B: A + `w1 0.8` | **−22.9 m** | 47.5 vs 55 | **−2.1** (p) | +4.31 m | recovery from a 10 m/s descent climbs 13 m but bleeds 8 m/s; with `w1` near 1 the pull-up's dissipation dominates |
| C: A + `hB 1000` (B uses min(h, 1000)) | **−18.5 m** | 46.9 vs 55 | **−3.7** (U) | +4.62 m | slow steep climb above 1000 m (V 55, γ 0.38) zooms and loses speed; no altitude credit above the cap |
| D: C + `hU 1000, u_hi 1200, V_hi 95` | **−21.0 m** | 47.5 vs 55 | **−2.1** (ṙ) | +4.73 m | same zoom corner; `U` itself now holds |
| E: A + `L 50, V_lo 45` (slow penalty fades to 0 over the 50 m below 1,000 m) | **−54.5 m** | **59.8 vs 55** | **−6.5** (U) | **−0.76 m** | slow dive just under 1,000 m (V 47, 18 m/s down): the penalty switches on as it descends |
| F: E + `w1 0.8` | **−98.5 m** | **58.8 vs 55** | **−5.5** (U) | +1.46 m | same corner |

Reproduce a variant with, e.g., `cd Tools/termsound && ../../.lake/tsvenv/bin/python barrier_run.py 512 --tag=A
ul=0.3 uq=0.1 Delta=55 fast=/tmp/barrier_results_512_128.json` after `make barrier K="512 128"`.

**Reading.**
- **The barrier direction itself (C1, C3) holds at k = 512 on θ₀:** the worst state in the band ends 8.0–8.5 m
  above `b`, and no frame goes below `F` (worst 3.8 m above, from 950 m at 85 m/s descending at 9 m/s, nose 0.12 rad low). At k ≤ 128 it
  does not: within one second the pull-up has not finished, and `B` dips *during* the recovery. The worst k = 128
  case starts at 949 m at V*, descending at 7.5 m/s with the nose 0.075 rad low; one second later it is back at
  949 m and climbing at 12 m/s, but the pull-up has cost 1.6 m/s, and the slow penalty puts `B` 2.6 m under `b`.
  The aircraft never went below 946 m. At k = 1 it cannot hold with any box that allows a descent: on `B = b` the next frame needs an upward
  acceleration of `|v_z| / (wl + 2 wq |v_z|)`, and the box's `a⁰`, α and pitch-rate corners deny it.
- **C3 holds everywhere except sized k = 128** (where the boxes had diverged). The floor margin `b − F` = 5 m is
  enough: no search found a frame below 941 m from `S`.
- **What fails is the rest of `P[θ]`:**
  - **`ε ≤ Δ`:** at k = 512 the largest 4-second drop of `B` is 49 m (states high up that the law brings down
    toward 1,000 m). Widening the band to 55 m pulls slow states high up into it, and those break C1 (variant A).
  - **C2, region invariance:** two faces. The `U` face: a fast steep climb from near the floor (V 85, γ 0.37)
    zooms 10–40 m over `u_hi`; climb counted against the level-off command underestimates it, and counting all
    climb (variant D) needs `u_hi` = 1,200 m. The lateral boxes (`φ`, `Δψ`, `β`, `p`, `r`): no box size found is
    mapped into itself, even in 4 s, because pull-ups and zooms drive the lateral axis (torque and P-factor at
    full throttle and changing α).
- Every repair of one condition reopened another at a corner of `R` that the level-off never visits on its own
  (a slow steep zoom above 1,000 m; a 30 m/s climb at 85 m/s at 946 m). Explicit boxes force `R` to contain those
  corners. That is the structural obstacle for this family, the same one the k-step family hit with the fast
  states (#46 §7: the fast states leave their boxes).

## Validated bounds

**None obtained; the existing interval tooling cannot reach `R`'s scale.** `TsInterval.frameBox` (the `tsmap B`
command used by `level_cert2.py`) encloses one frame of the real map and its Jacobian over a box, with outward
rounding (libm assumed within 4 ulps). Measured on boxes around the level trim (`barrier_valid.py`):

| box (half-widths) | result |
|---|---|
| one coordinate at a time, the rest zero: `h`, `v_al`, `rpm`, `MAP`, `a⁰_dn` ±10; `v_dn` ±1; `q` ±0.1 | clean |
| `θ` alone | clean only at ±1e-6 rad (±1e-5 already panics or is infinite) |
| all of `R`'s base boxes × 1e-5 | clean, `v_dn′` ±0.0015 m/s |
| × 1e-4 … 1 | `v_dn′` infinite, `θ′` = ±π/2, 10 saturation flags "may be active" |
| slow coordinates only (`h` ±60, `v_al` ±18, `v_dn` ±1, `θ` ±0.05) | Lean panic `index out of bounds` in `Table.seg1` (the piston table), which returns a default value and continues, so the enclosure is **unsound**, not just wide |

So a cover of `R` would need sub-boxes about 1e-6 rad wide in pitch alone, and the tool needs a guard that turns
the panic into a failure before any wide enclosure can be trusted. Neither the k-frame conditions (C1–C3 involve
`f^k` with k ≥ 128) nor their one-frame ingredients are validated here. **Proved:** C4, for every θ of this form, on
exact reals (`B ≤ h` and `b ≥ F`).

## Contract for the Lean side

The sufficiency side is `docs/termsound/abstractions.tex` (#60), Family 2. The conditions here are its
**barrier with margin** `P₂′[θ′](F)` (Definition `def:near`, Theorem `thm:near`), with `z = F`, `I_θ = S` and
`θ′ = (k, B, b, R, ε, Δ)`:

| here | `abstractions.tex` | note |
|---|---|---|
| C2 | (B1a) region | |
| C1′ | (B1b) bounded drop above the band | measured on all of `S`, which implies (B1b) |
| C1 | (B1c), weakened to `B(F^k x) ≥ b` in the band | the weakening is allowed by the remark after `thm:near` |
| C3 | (B2) | measured for `1 ≤ j ≤ k`; (B2) needs `j < k` |
| C4 | (B3) | holds by construction: `B ≤ h` and `b ≥ F` (the remark `rem:b3` with `M = 0`) |
| side `ε ≤ Δ` | `Σ₂′`: `k ≥ 1`, `0 ≤ ε ≤ Δ` | |

**Instantiation for the JsbExact level-off (θ₀, k = 512), as measured.** Every definition below is in
`Tools/termsound/barrier.py`; the constants are exact decimals.
- `X`: `tsmap` charts `(h, y) ∈ ℝ × ℝ³²`; `f`: one frame of `TsMap`'s `M` command (plain loop, `P` = `NEW`,
  ψ = π/2, north = 0), i.e. `Plane.step ∘ Law.step` read through `place`/`chart`.
- `h`: the chart's `h`. `F = 941`. `k = 512`, `b = 946`, `Δ = 30`, `ε = 30` (C1′ is **measured false** at 30: the
  largest drop found is 49.2 m).
- `V* = 70.78069916555519`, `θ* = −0.021908839125330662`, `g = 9.80665`;
  `B = h − 0.5·max(V*² − V², 0)/(2g) − 0.15·max(−v_z, 0) − 0.03·max(−v_z, 0)²`.
- `R`: `50 ≤ V ≤ 86`; `|asin(v_z/V)| ≤ 0.4`; `|θ − θ* − asin(v_z/V)| ≤ 0.12`;
  `h + max(V² − V*², 0)/(2g) + 0.15·c + 0.08·c² ≤ 1065` with `c = max(min(v_z, v_z − 0.005·V·(1000 − h)), 0)`;
  and `|q − q*| ≤ w` for each row of `FAST0` (half-widths `w`) with `q*` the value at the trim of
  `barrier_trim.json` (`Q_TRIM` in `barrier.py`): φ 0.03, Δψ 0.03, β 0.01, p 0.05, q 0.2, r 0.05,
  Δv⁰ (0.04, 0.003, 0.1), Δ²v (0.003, 0.001, 0.01), a⁰ (4.5, 0.3, 12), Δa (0.3, 0.1, 1), ṗ 0.08, q̇ 1, ṙ 0.06,
  u̇ 4, v̇ 1.3, ẇ 10, rpm 70, MAP 1500, ia 0.08, ib 0.015, iφ 0.03 (axes al, rt, dn; SI units as in the chart).
- Status per condition at this θ: C1 survives search (+8.5 m), C3 survives search (+4.3 m), C4 proved,
  **C1′ with `ε ≤ Δ` falsified (49.2 m > 30 m), C2 falsified (−1.5, lateral acceleration `a⁰_rt` box).**
  So this θ is a fully specified, falsified instance: suitable as a worked instantiation of the definitions of
  `abstractions.tex` (and of a Lean statement of them), not as a membership claim.
