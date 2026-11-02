# TermSoundR skeleton: the named obligations

`TermSoundR cityGate (CrashH 7) GInit` is the one substantive assumption left in the headline. It says that when
the gate's end-of-escape test passes, flying on is safe forever. The skeleton (`CityGate/TermSkeleton.lean`, #56)
breaks it into named obligations. Each obligation is a `def … : Prop` hypothesis, never a `sorry`. Two
compositions are fully proved:

- `termSoundR_of (E : Ends A) (hE : E.Sound) (hT : EndTestCertified E T) (hL : TermLink T) : TermSoundR cityGate (CrashH 7) GInit`
- `cityGate_spec_safe_of_obligations` (`SpecBridgeNative.lean`): the same hypotheses, plus `TbBounded`, give
  `CitySafety.Safe cityMap specFilter`.

`termSoundR_of` uses only the standard axioms; `cityGate_spec_safe_of_obligations` adds the existing
`native_decide` ones for the 4 starts.

`proofs/Proofs/TermSound/Glue.lean` instantiates the abstraction with the rung-1 point mass (#38), which turns
`dyn_abstract_inv` into a theorem. `termSoundR_glue` is the composition with `dyn_abstract_inv` already discharged.

## The certified sets

There are three end kinds `k`, each with tube parameters `θ`. Each kind has a certified set
`C_k θ = Dyn_k θ ∧ Geo_k θ` on the gate state `x : Ctl × Plane`.

- **Kinds:** helix (`θ : Helix`), straight ray (`θ : Ray`), and street. The street tube is a ray funnel, as a
  placeholder until it has its own `Geo`.
- **`Geo_k θ`** is #37's map clearance for the 7 m cube: `GeoH H := 0 ≤ H.r + H.δ ∧ 0 ≤ H.s ∧ H.Geo cityMap 7 10` and
  `GeoR R := 0 ≤ R.g ∧ 0 ≤ R.s ∧ R.Geo cityMap 7`.
- **`Dyn_k θ x := (∃ a, π x = some a ∧ DynA θ a) ∧ Fast θ x`.** This uses an abstraction
  `Abs Θ A = ⟨π, F, Near, DynA, Fast⟩` with these parts:
  - `π : Ctl × Plane → Option A` reads the gate state, and is `none` if a number involved is not finite;
  - `F` is the escape law's step in the model;
  - `Near θ b a` says `a` is within the per-frame disturbance `δ` of `b`;
  - `DynA` is the model's invariant set;
  - `Fast` holds the boxes on attitude, rates, α and engine, which the model leaves out.

## Obligations

| Name (Lean) | Exact statement | Owner | Status |
|---|---|---|---|
| `term_sound_mem` = `EndTestCertified E T` | `∀ x, Origin cityGate GInit x → ∀ n, T (cityGate.flyN n x) = true → InTubes E (cityGate.flyN n x)` | End-test fix (`eric/helix-round`) | **Open.** It is false for today's `cityGate.term`, because the falsifier found descending circles and radius drift (#30). |
| `TermLink T` | `∀ x, cityGate.term x = true → T x = true` | Same | Holds by definition once `T` is the fixed test itself (example in `TermSkeleton.lean`). |
| `dyn_abstract_inv` = `Abs.DynAbstractInv` | `∀ θ a a', DynA θ a → Near θ (F θ a) a' → DynA θ a'` | Informal proof (#36, #46); rung 1 | **Proved for the rung-1 abstraction:** `helixAbs_inv` and `rayAbs_inv` in `Glue.lean`, from `dynH_robust`/`dynR_robust`. The informal proof's coarse set can replace `DynA` here. |
| `residual_bound` = `Abs.ResidualBound` | `∀ θ x a, Dyn θ x → π x = some a → ∃ a', π (cityGate.fly x) = some a' ∧ Near θ (F θ a) a'` | Measurement, then proof | **Open.** Rung 1's per-frame budget is about 6e-3 m/s² of airspeed, and the atmosphere alone takes 1.5 times that (#38). The residual must be measured first. |
| `fast_states_bounded` = `Abs.FastBounded` | `∀ θ x, Dyn θ x → Fast θ (cityGate.fly x)` | Measurement, then proof | **Open.** `Fast` is a parameter of the glue (`helixAbs Fast`), still to be chosen. |
| `dyn_conf` = `Abs.DynConf Conf` | `∀ θ x, Dyn θ x → ∃ c, exactPos x.2 = some c ∧ Conf θ (toPt c)` | Informal proof's set, #54's ℝ/ℚ bridge | **Open.** For rung 1, `helix_conf`/`ray_conf` (#38) and #54's `helix_box_clear`/`ray_box_clear` give the ℝ part. What remains is matching #37's `Helix.Conf`/`Ray.Conf` parameters (radius and slack) to rung 1's `Rstar`, `m0` and `kappa`. |
| `geo_clear` | `Dyn_k θ x → Geo_k θ → ¬ CrashH 7 x.2` | #37 | **Proved** from `dyn_conf`: `geo_clear_helix` and `geo_clear_ray`. |
| `Abs.dyn_inv` | `Dyn` invariant under `cityGate.fly` | Skeleton | **Proved** from `dyn_abstract_inv`, `residual_bound` and `fast_states_bounded`. |

## The rung-1 glue (`Glue.lean`)

- **`A = St`:** rung 1's `(x, y, z, ψ, u, v_z, l)` over ℝ.
- **`π = piSt`:** the position comes from `exactPos`, which is exact in ℚ. Track angle, airspeed, climb rate and
  bank come from the observation doubles through `ratOf`, then cast to ℝ: `ψ = arg(vE + i·vN)` and `l = tan φ`.
  Everything is exact; there is no Float arithmetic.
- **Helix:**
  - `F = stepHelix`;
  - `Near = Small (a − b)`;
  - `DynA H = DynH ⟨cx, cy⟩ z0 δ zTop`, plus `0 ≤ z0 ≤ zTop ≤ ZT`.
- **Ray:** the same, in the ray's own frame:
  - `toLocal` rotates by the direction's angle about the start, and `fromLocal` undoes it;
  - `F = fromLocal ∘ stepRay ∘ toLocal`;
  - `Near` is `Small` of the difference in the ray frame;
  - `DynA R = DynR 0 z0 w zTop ∘ toLocal`.
- **Street:** reuses the ray model, as a placeholder.
- **Non-vacuity:** rung 1's trims are members (`dynHA trimTube trimH`, `dynRA eastTube trimR`).

## Where things live

The skeleton is in the root package (ℚ/Float, no Mathlib) and is generic in the model state `A`. Real-valued
models live in `proofs/` (Mathlib), which imports the root package, as #54 does.

## Run-time check

`make termcheck` is a run, not a proof. From each of the 4 spec starts it flies the gate's start escape until
`cityGate.term` passes, builds a ray or helix funnel at the settled state, and tests its `Conf` and `Geo`. All 4
settle into the straight ray at frame 1536, about 1620 m up, and pass both. This is easy because the starts are
above every solid.
