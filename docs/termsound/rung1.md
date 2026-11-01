# TermSound rung 1: robust end sets for a point mass

Rung 1 of Step 3 in issue #30. Two end sets are proved robustly invariant over ℝ with Mathlib, for a point mass
flying the escape law's settled climbs:

- the 30° climbing turn (helix);
- the straight climb (ray).

Each set is invariant under every per-frame disturbance within a stated budget `δ`, and it implies the numeric
bounds the geometric lemmas (`Geo`) need. Code: `proofs/Proofs/TermSound/`. Numerics and simulation:
`proofs/scripts/termsound_rung1.py`.

## The model `S` (`Model.lean`)

One frame is `h = 1/128 s`. The state is `(x, y, z, ψ, u, v_z, l)`:

- position (m), with `z` up;
- heading `ψ`, counterclockwise from east;
- horizontal speed `u`;
- climb rate `v_z`;
- `l = tan φ`, positive for a left bank.

| Part | Equation (per second) | Source of the numbers |
|---|---|---|
| Speed | `u̇ = a₀ − a_z z − k_D (u − u_r) − (g/u_r) v_z` | `u_r = 35 = V_REF`; `k_D = 0.05/s` |
| Climb | `v̇_z = k_G (v₀ + k_V (u − u_r) − v_z)` | `k_G = KG = 2.5/s`; `k_V = u_r·KV = 0.7/s`; `v₀ = u_r·GC_REF = 5.25 m/s` |
| Bank | `l̇ = (l_c − l)/τ` | `τ = 0.5 s` (roll loop `KPHI = 2.5`) |
| Heading | `ψ̇ = g l / u` | coordinated turn |
| Helix | `l_c = 4/7` (29.7°, `ESC_BANK = 0.52`) | kinematics: exact arc over the frame |
| Ray | `l_c = −KPSI · ψ`, with `KPSI = 1`; held track along `x` | kinematics: Euler |

- **The climb law** is the gate's speed-on-pitch law (`gc = GC_REF + KV (v − V_REF)`), with full throttle.
- **Excess thrust** falls linearly with altitude (density). The coefficients `a₀, a_z` are derived from the trim:

  ```
  u*(z) = u_r + E₀ − E₁ z
  v_z*(z) = v₀ + k_V (E₀ − E₁ z)
  E₁ = 7/4000
  ```

  | Kind | `E₀` | `u*(0)` | `v_z*(0)` | Ceiling |
  |---|---|---|---|---|
  | Ray | −1/2 | 34.5 m/s | 4.9 m/s | 4000 m |
  | Helix (turn drag) | −3/2 | 33.5 m/s | 4.2 m/s | 3429 m |

  These are close to the measured settled climbs: 30–41 m/s, a few m/s up.
- **Simplifications:** `V ≈ u` (`cos γ ≈ 0.99`); the `1/V` in the energy equation is linearised at `u_r`; the
  `GC_LO/GC_HI` and `±0.15` clamps are inactive inside the sets. Rung 2 should absorb these as residual.

## The sets and the theorems

`Dyn` is a quadratic sublevel set around the altitude-dependent trim, plus geometric parts that are needed only
below `ztop`. `ztop` is where `Geo` stops mattering (above the map's top plus `e`). It is assumed that
`0 ≤ z0 ≤ ztop ≤ ZT = 1200 m`.

```lean
DynH c0 z0 m0 ztop s :=                                        -- helix
  q_L(u − u*(z), v_z − v_z*(z)) ≤ 1/4 ∧ z0 ≤ z ∧ z ≤ 4100 ∧
  (z < ztop → |l − l_c| ≤ 1/200 ∧ ‖centre s − c0‖ ≤ m0 + (1/3)(z − z0))
DynR x0 z0 w0 ztop s :=                                        -- ray
  q_L(...) ≤ 1/4 ∧ z0 ≤ z ∧ z ≤ 4600 ∧
  (z < ztop → q_T(ψ, l) ≤ 1/625 ∧ x0 ≤ x ∧ |y| ≤ w0 + (1/30)(x − x0) ∧ z0 + (2/25)(x − x0) ≤ z)
```

- **The quadratic forms:**
  - `q_L = 28 e_u² − 6 e_u e_vz + e_vz²`, which gives `|e_u| ≤ 0.115 m/s` and `|e_vz| ≤ 0.61 m/s`;
  - `q_T = 5ψ² + 3.5ψl + l²`, which gives `|ψ| ≤ 0.03 rad` and `|l| ≤ 0.065`.
- **`centre s = pos s + R*(z)·i·e^{iψ}`** is the turn centre the trim radius `R*(z) = u*(z)²/(g l_c)` would give.
  These are the turn-centre coordinates. The disturbance acts on position and heading directly, so a heading
  residual `ε` moves the centre by about `R*·ε`.

| Theorem | Statement |
|---|---|
| `Quad.q_robust_step` | `c²P − AᵀPA ⪰ 0`, `q e ≤ r²`, `q w ≤ K` and `(1+t)c²r² + (1+1/t)K ≤ r²` give `q(Ae + w) ≤ r²` |
| `Long.long_step` | longitudinal sublevel set invariant; the trim moving with altitude enters as `E₁·Δz` in `w` |
| `Helix.dynH_robust` | `DynH s → Small d → DynH (stepHelix s + d)` |
| `Ray.dynR_robust` | `DynR s → Small d → DynR (stepRay s + d)` |
| `Bounds.helix_forever`, `ray_forever` | every frame of every disturbed trajectory stays in `Dyn` |
| `Bounds.helix_stays_above`, `ray_stays_above` | once at `ztop` or higher, never below it again |
| `Bounds.helix_bounds`, `helix_conf` | the annulus bounds below |
| `Bounds.ray_bounds`, `ray_conf` | the corridor bounds below |
| `Checks.*` | non-vacuity and rejections (below) |

**Audit (`Checks.lean`).** Every theorem above depends only on `[propext, Classical.choice, Quot.sound]`. There is
no `sorry`, no `native_decide` and no new axiom. Build with `lake build Proofs.TermSound.Checks`. It needs only
Mathlib, not the parent package.

**Trusted surface.** It is the definitions in `Model.lean`, `DynH`/`DynR` and `Small`. Nothing else is trusted:
`S` is a model, not a claim about `JsbExact`, and connecting the two is the next rung's residual bound.

**Non-vacuity.**

- These states are members:
  - the helix and ray trims at 300 m (`trimH_mem`, `trimR_mem`);
  - an off-trim helix state that is 0.05 m/s fast, climbing 0.2 m/s extra, 0.2° steep, with its centre 3 m off
    (`offH_mem`).
- `helix_trim_forever` and `ray_trim_forever` instantiate the forever theorems with every hypothesis discharged.
  Their disturbance is at the full budget in every component, every frame.
- These states are rejected:
  - sinking at 1 m/s;
  - a 45° bank;
  - a centre 10 m away;
  - a heading 10° off the held track;
  - being under the climb line.

## The budget `δ` (per frame) and how large it can be

| Component | `δ` per frame | Per second | Note |
|---|---|---|---|
| `u` | 5e-5 m/s | 6.4e-3 m/s² | |
| `v_z` | 1e-4 m/s | 1.3e-2 m/s² | |
| `z` | 1e-4 m | 1.3e-2 m/s | |
| `l = tan φ` | 1e-5 | 1.3e-3 /s | ≈ 0.07°/s of bank |
| `ψ` | 1e-6 rad | 1.3e-4 rad/s | moves the helix centre by `R*·δ` |
| `x`, `y` (each) | 1e-4 m | 1.3e-2 m/s | |

- **Proved headroom.** All budgets can be scaled together by 1.40 before a side condition fails. The longitudinal
  set binds. Separately, the blocks allow these scales:

  | Block | Scale |
  |---|---|
  | Longitudinal | 1.40 |
  | Helix centre drift | 1.50 |
  | Ray cone | 2.8 |
  | Ray gradient | 3.7 |
  | Bank | 7.8 |
  | Lateral | 8.1 |

- **The atmosphere is the largest consumer of the speed budget.** The trim moves by `E₁·Δz ≈ 7.7e-5 m/s` per
  frame, which is 1.5 times `δ_u`.
- **Simulation.** The script runs 4 seeds × 60 s for each kind. The starts are at 90–100% of each Lyapunov level.
  The disturbances are of two kinds:
  - uniform random;
  - adversarial: along the Lyapunov gradient, and for the helix synchronised with the heading.

  | Scale | Uniform random | Adversarial |
  |---|---|---|
  | ×1 | every state stays in | every state stays in |
  | ×3 | every state stays in | leaves (`q_L` reaches 1.4–1.5 × `r²`) |

  So the proved budget is within about 2× of the empirical adversarial limit.
- **Scaling.** The budget is about (contraction rate × set size). The longitudinal Lyapunov rate is 0.47/s, limited
  by the law's slow speed mode (0.27/s). A bigger set buys `δ` linearly but widens the helix cone in proportion.

## Bounds in the form the geometry needs

Below `ztop`:

- **Helix** (`helix_bounds`):

  ```
  | ‖p − c0‖ − R*(z) | ≤ m0 + κ (z − z0)
  κ = 1/3
  176 ≤ R*(z) ≤ 200.5
  |R − R*| ≤ 3.2 m
  v_z ≥ 2 m/s
  ```

  In the fixed-annulus form `Helix.Conf` of `Spec/EndSets.lean` (`helix_conf`):

  ```
  r = (R*(z0) + R*(ztop)) / 2
  δ_r = (R*(z0) − R*(ztop)) / 2 + m0 + κ (ztop − z0)
  ```

  `R*` falls by 0.021 m per metre climbed.
- **Ray** (`ray_bounds`):

  ```
  |lateral| ≤ w0 + along/30
  z ≥ z0 + 0.08 · along
  v_z ≥ 2.8 m/s
  |ψ| ≤ 0.03
  ```

  In the constant-width form `Ray.Conf` (`ray_conf`), `w = w0 + (ztop − z0)/(30 · 0.08)`.

Everywhere, `z ≥ z0`. From `ztop` on, `z ≥ ztop` forever, and nothing horizontal is claimed.

## Where the roadmap in #30 needs adjusting

1. **A fixed annulus or a constant-width corridor "forever" is not provable** under a persistent per-frame `δ`
   with the gate's open-loop terminal laws. Those laws are bank hold for the helix and heading hold for the ray.
   - **Why, for the helix.** An adversary can raise the turn radius while the aircraft heads one way and lower it
     while it heads the other way. The centre then ratchets by about `4·|R − R*|` per revolution, without bound.
   - **Why, for the ray.** A heading error held at `ε` drifts the aircraft sideways by `ε·s` over an along-track
     distance `s`.
   - **What is provable** is the widening form proved here, valid until `ztop`. Above `ztop` only `z ≥ ztop` is
     needed, and it is proved: the aircraft never sinks back below `ztop`.
     - Helix: `κ = 1/3` m per metre climbed.
     - Ray: 1/30 per metre along track. The gate's `ray_clear` already widens its corridor by 2%.
   - **What this means for `Conf`.** `Helix.Conf` and `Ray.Conf` on `eric/termsound-geo` should therefore be
     `(z < ztop → annulus or corridor) ∧ z ≥ z0`, with `ztop > top + e`.
   - **A fixed annulus forever** would need centre-holding feedback in the terminal law, for example
     `φ_c = φ₀ + k_r (ρ − r) + k_χ χ`.
2. **"`v_z ≥ 0`, so altitude is non-decreasing" is false near the ceiling under disturbance**, and the trim
   descends above the ceiling. What holds is:
   - `z ≥ z0` always;
   - `z` increasing while `z ≤ ZT`;
   - `z ≥ ztop` once reached.

   The proof caps altitude at `ZCAP`, which is above the ceiling, and shows that the cap is invariant.
3. **The real law's `GC_LO = 0.05` clamp binds above the altitude where `v_z*` falls below `0.05·u`** (about
   2500 m for the ray). Above that, `S` and the law differ: the law keeps commanding a climb it cannot sustain and
   bleeds speed. A forever claim against the real law needs a terminal level-off or a `v_z` floor of 0, or rung 4's
   residual will be large above that altitude.
4. **The budget `δ` is small:** about 6e-3 m/s² in speed and 1.3e-4 rad/s in heading rate. The "main risk" in #30
   (`δ_k` against the one-frame residual) is real and should be measured at rung 2 before any proofs.
5. **The disturbance has to be stated in `Dyn`'s coordinates.** For the helix, a heading residual counts about 200
   times over in the centre.
6. **The sets reached are tight:** ±0.11 m/s, ±0.6 m/s climb and ±0.2° of bank. The slow speed mode (0.27/s) means
   reaching them from a pull-up exit takes about 10 s. That fits the 16 s horizon only for escapes that are
   already near trim. A per-escape settling check belongs in the acceptance test.

## What changes at rung 2

- **Model:** smooth aero (a lift and drag polar, thrust lapse), pitch dynamics and engine lag. The state goes from
  2 to about 4 longitudinal states. `q_robust_step` generalises with the n-dimensional `PsdForm`/`StepLyap` lemmas
  on `eric/ci-proof`.
- **Reclaiming the atmosphere's share of `δ`:** centre the ellipse on `x*(z) + e_ss`. Here `e_ss = −F⁻¹ m v_z*` is
  the steady lag behind the moving trim.
- **First the measurement:** measure the one-frame residual of rung-2 `S` against rung-1 `S` on the settled
  climbs, and compare it with the table above.
