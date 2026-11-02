# Escape law: terminal phase of the straight escape, and a level-off for all escapes

Status: implemented in `flight/src/envfilter.rs` (Rust `Law`, `LAW_CEGIS2`) and `CityGate/Law.lean` (Lean
`CityGate.Esc.Law`), bit-identical (`make gatefaith` checks both against the reference hashes below), and extended to
the turning escapes (see "Turning escapes" at the end). Issue #36 (step 0), proof context in
`docs/termsound-proof.tex`. The reference implementation is `Tools/termsound/TsMap.lean` (`Cand`, `elevHold`,
`controlsHold`, `stepHold`) with the values of `NEW` in `Tools/termsound/terminal.py`. Numbers below come from
`make certify` (`terminal.py`, `reftraj.py`).

## Goal

For the certificate in `docs/termsound-proof.tex` (the `Dyn` part of the ray end set), the straight escape's settled
climb has to do four things:

1. stay inside one segment of the c172p's lift (`CLwbh`) and drag (`CDwbh`) tables, from entry (about 10 m) up to the
   release altitude `zTop` = 934 m and above;
2. settle quickly, so the end test can accept it within the gate's 16 s horizon;
3. end in one level-flight equilibrium above `zTop`, instead of climbing into the `GC_LO`-clamp regime near
   2,500 m and the ceiling near 3,150 m;
4. contract in one quadratic norm across the band.

Today's law fails 1: the trim's angle of attack α crosses `CDwbh`'s breakpoint at 0.0873 rad near 375 m and
`CLwbh`'s at 0.09 near 545 m (`termsound-proof.tex`, Section 5.5). It also fails 2: the median settling time is
18.8 s, and 14 of 48 starts settle within 16 s. And it fails 3.

## Why this design

- **Fly the climb at a constant equivalent airspeed (EAS).** At fixed weight and load factor the trim's α is a
  function of dynamic pressure, so holding EAS (`v·√σ`, σ = the law's density ratio) holds α nearly constant at every
  altitude. With a reference of 35.2 m/s EAS the trim's α is 0.0777–0.0782 rad over 10–1,000 m. That is inside
  `CDwbh`'s segment [0.0698, 0.0873] with margins of 0.0079 and 0.0091, and inside `CLwbh`'s segment [0, 0.09].
  - **Cost: none.** The climb gradient rises from 0.140 to 0.144–0.147, and the climb rate from 4.6–4.9 m/s to
    5.0–5.35 m/s.
  - The true airspeed rises from 34.8 to 36.4 m/s over the band (old: 34.6 falling to 34.4).
  - The funnel slope `s = κ/γ` falls by about 8 % for the same cross-track drift κ, because the climb rate γ is
    higher.
- **Faster speed loop (KV 0.02 → 0.06).** Speed error was the slowest-settling quantity. 0.06 is the knee of the
  scan: 0.08 gained 0.25 s of median.
- **Faster α integrator (KI_A 2 → 6).** Its slow mode was the next bottleneck.
- **Wider flight-path limits (GC_LO 0.05 → 0, GC_HI 0.35 → 0.5).** Slow starts (25 m/s) were acceleration-limited
  while climbing at 0.05. Fast starts (60 m/s) were limited by how fast a 0.35 gradient bleeds speed.
- **Only past the pull-up.** All four changes apply once the escape is past its pull-up (its held track is set),
  so the pull-up, which decides the close calls in `docs/boundary-regimes/`, is unchanged.
- **Level-off at 1,000 m for all escapes.** The commanded gradient is capped by an altitude hold,
  `0.005·(1000 − h)`, so the climb levels off at 1,000 m ≈ `zTop` + 66 m. Below 972 m the cap is above every
  gradient the law commands, so nothing changes there. The handover from the climb to the level trim happens above
  `zTop`, where no clearance is needed.

Tried and rejected:
- heading gain KPSI 1.5 or 2 (oscillatory bank; median 11.8–12.5 s);
- KI_PHI 0.5 or 2 (worse);
- KG 3.5 or 4 (no change);
- roll gains KPHI 4 with KP 1.2 (no change);
- GC_LO −0.05 (median 11.3 s, and it gives up altitude while slow).

## Changes, exactly

All changes are in the elevator law (`Law.elevCegis` in Lean, `Law::elev_cegis` in Rust). The lateral law, the
throttle (1.0), the escape library and the pull-up logic are unchanged.

### New constants (both languages, `f64`/`Float`, these exact decimal literals)

| Name | Value | Meaning |
|---|---|---|
| `V_EAS_T` | `35.2` | straight escape's terminal speed reference, equivalent airspeed (m/s) |
| `KV_T` | `0.06` | its speed gain (rad of flight-path gradient per m/s) |
| `KI_A_T` | `6.0` | its α-integrator gain (1/s) |
| `GC_LO_T` | `0.0` | its lower gradient limit (rad) |
| `GC_HI_T` | `0.5` | its upper gradient limit (rad) |
| `H_LEVEL` | `1000.0` | level-off altitude (m above sea level, the observation's `h` = Lean `o[2]!`) |
| `K_HOLD` | `0.005` | level-off gain (rad per m) |

The level-off clamp uses the law's existing `GC_HI` (`0.35`, `LAW_CEGIS2.gc_hi`), not `GC_HI_T`.

### Terminal condition

`term := (esc == 0) && turning`, where `turning` is the law state's `psiRef`/`psi_ref` being non-NaN **as it is when
the elevator law is called**. In both implementations the elevator law runs at the top of `controls`, before
`controls` sets `psiRef`. So `term` becomes true on the frame after the frame that set `psiRef`.
- Lean: `l.turning` on the `l` that `controls` received, after `capture` and `streetTurn`, which are no-ops for
  escape 0.
- Rust: `self.turning()` inside `elev_cegis`.

### The elevator law (only the marked lines change)

Inputs as today: `v = max(vt, 10)`, `g = atan2(−vD, √(vN² + vE²))`, `cphi = cos φ`, `vRef = V_REF[esc]`, `h = o.h`.

```
term   := esc == 0 && turning                                   -- NEW
(kv, gcLo, gcHi, kiA) := if term then (KV_T, GC_LO_T, GC_HI_T, KI_A_T) else (KV, GC_LO, GC_HI, KI_A)   -- NEW
vs     := if term then v * sqrt(rhoOf(h) / 1.225) - V_EAS_T else v - vRef                            -- NEW
gcC    := clamp(GC_REF + kv * vs, gcLo, gcHi)                   -- was clamp(GC_REF + KV * (v - vRef), GC_LO, GC_HI)
gc     := min(gcC, clamp(K_HOLD * (H_LEVEL - h), -GC_HI, GC_HI))   -- NEW (all escapes, every frame)
nLong  := cos g + v * KG * (gc - g) / G0                        -- unchanged from here on
ncmd   := if cphi < 0.35 then NMIN else clamp(nLong / cphi, NMIN, NMAX)
rv2    := rhoOf(h) * v * v
acmd   := min(A0 + KA0 * ncmd / rv2, AMAX)
nAch   := (acmd - A0) * rv2 / KA0
qcmd   := G0 * (nAch - cos g * cphi) / v
sc     := if VS > 0 then min((VS / v) * (VS / v), 1) else 1
ea     := acmd - alpha
eRaw   := E0 + E1 * acmd + KQF * qcmd * 40 / v + sc * (KA * ea - KQ * (q - qcmd)) + ia
e      := clamp(eRaw, -1, 1)
ia     := if e == eRaw || ea * ia < 0 then clamp(ia + kiA * ea * DT_JSB, -0.4, 0.4) else ia   -- kiA was KI_A
```

Operation order and rounding:
- **`vs` when terminal:** exactly `v * sqrt(rhoOf(h) / 1.225) - V_EAS_T`. Divide, then the correctly rounded square
  root (`Float.sqrt` / `f64::sqrt`), then multiply, then subtract. `rhoOf` is the existing `rhoOf`/`rho_of`
  (`1.225 * max(1 − 2.2558e-5·h, 0.5)^4.256`), called with the same `h` as for `rv2`.
- **`vs` when not terminal:** `v - vRef`, which keeps today's `KV * (v - vRef)` bit for bit.
- **`gcC`:** `GC_REF + kv * vs`, with no fused multiply-add (neither language fuses by default).
- **`clamp`:** Lean's `clamp x lo hi` (`if x < lo then lo else if x > hi then hi else x`) and Rust's `f64::clamp`
  agree on finite inputs. The bounds here are finite constants.
- **`min`:** Lean's `fmin a b` and Rust's `a.min(b)` agree on finite inputs. Both arguments are finite.
- **The level-off term:** `K_HOLD * (H_LEVEL - h)`, subtraction first.

**Structure, where this meets the speed-first rule for the turning escapes.** Compute the escape's climb gradient
`gcC` in one place (a function of escape, phase, `v`, `h`), then apply the common level-off cap
`gc = min(gcC, clamp(K_HOLD·(H_LEVEL − h), −GC_HI, GC_HI))` once, for every escape. The speed-first rule changes
`gcC` for escapes 1–4. This spec changes `gcC` only for escape 0 when terminal, and adds the cap for all.

The street escape (escape 5) is untouched here. Its axis-following phase should take the same terminal parameters
when per-street tubes (#36 step 8) are built.

## What it achieves (`terminal.py`)

**Trims of the new climb, 10–1,000 m:**

| h (m) | V (m/s) | climb (m/s) | gradient | α (rad) |
|---|---|---|---|---|
| 10 | 34.76 | 5.00 | 0.1439 | 0.0779 |
| 500 | 35.62 | 5.19 | 0.1457 | 0.0779 |
| 1000 | 36.44 | 5.35 | 0.1468 | 0.0777 |

- **Table segments:**
  - α stays in one segment of `CLwbh` (index 2) and `CDwbh` (index 10) over the whole band.
  - The propeller tables and the Mach corrections stay in one segment each.
  - The engine's mixture-efficiency table crosses one breakpoint (fuel/air ratio 0.08845, near 830 m). Fuel/air ratio
    depends only on ambient pressure, so this kink sits at a fixed altitude and not in the error state.
- **No saturation at any trim.**

**Contraction:**
- The per-frame spectral radius is 0.99833–0.99837 (slowest mode 0.209–0.215 /s, up from 0.137–0.175). The
  one-second factor is 0.807–0.811 across the band, and it changes smoothly.
- **One norm for the whole band:** with `Q_N` from the one-second Lyapunov equation at 450 m (μ = 0.85, fast
  coordinates weighted 1e-4), the largest `‖A±(h)^128‖_{Q_N}` over 10–1,000 m and both sides of the |β| kink is
  **0.902**. The old law needed two norms and still reached 1.26.
- **Level-off trim:** 1,000.20 m, 70.78 m/s, full throttle, α = −0.0219.
  - α is inside `CLwbh` segment 1 and `CDwbh` segment 4; the margin to `CDwbh`'s −0.0175 breakpoint is 0.0044.
  - Tip Mach is 0.888, inside the Mach tables' upper segment.
  - The per-frame spectral radius is 0.99931 and the one-second factor 0.915.

**Settling into the box around the law's own climb** (±0.5 m/s speed, ±0.5 m/s climb, ±0.02 rad bank and heading,
integrators ±0.02), from 48 representative starts at 150 m:

| | median | p90 | max | within 16 s |
|---|---|---|---|---|
| gate law | 18.8 s | 26.5 s | 27.6 s | 14 / 48 |
| new terminal phase | **10.0 s** | **13.9 s** | **15.7 s** | **48 / 48** |

The 48 starts are 25, 35, 45 and 60 m/s, flight path −0.35, −0.15, 0 and 0.2 rad, and bank 0, 0.6 and 1.1 rad.
By start speed (median, max): 25 m/s 13.3 s, 15.7 s; 35 m/s 8.7 s, 9.6 s; 45 m/s 8.4 s, 8.9 s; 60 m/s 13.0 s,
13.9 s.

**The 6–8 s median target is not met.** Starts near the climb speed settle in 8–9 s. Slow and fast starts are
limited by physics, not by gains:
- From 25 m/s the aircraft must gain about 10 m/s at full throttle; level acceleration is about 1 m/s².
- From 60 m/s it must lose 25 m/s, and a 0.5 rad climb bleeds about 4.7 m/s².

Lowering `GC_LO_T` below 0 (a descent while slow) would buy a little and costs altitude. It is not proposed.

## Reference trajectories

Starts are `CityGate.startPlane x y z v gam psi phi n thr` in Lean, the same `State` as `JsbPlant::new` in Rust:
(X, Y, Z, V, GAM, PSI, PHI, N, THR). Each frame is `Law.step` (escape 0, from `Law.new 0`) then `Plane.step`.
Every 256th frame lists elevator, aileron, rudder and throttle as passed to the plant (JSBSim signs), then the map
position x, y, z (`Plane.pos`), all as 16-hex-digit IEEE bit patterns. `HASH` is FNV-1a 64 (offset
`cbf29ce484222325`, prime `100000001b3`) over the little-endian bytes of those seven values for **every** frame, in
order.
- The "gate law" blocks are today's law: an implementation must reproduce them before the change.
- The "new law" blocks are this spec.
- Start A exercises the terminal phase.
- Start B (950 m) exercises the level-off.

Regenerate with `make certify` (`Tools/termsound/reftraj.py`, `tsmap` command `V`). The heading of starts A and B
is exactly π/2 (`np.pi / 2`); the headers below print it rounded to 6 decimals, which does not reproduce the hashes.

```
## start A, gate law, 2048 frames: startPlane(0.0, 0.0, 150.0, 30.0, -0.1, 1.570796, 0.4, 1.0, 1.0)
256 bfb68f98a3c319b1 3fd41ed1c2e8d412 bfc1672063f8c7dd 3ff0000000000000 c007a643c690b934 404e6d0539a34887 4062e257a36d8c16
512 bfb04d261cabc40a 3f844ab3cd6844a0 bfa3bfbb47a46c02 3ff0000000000000 c022504a2f98e6a0 405eb9e28a6c39b1 40636fabf8df793e
768 bfaa1b0af5437db0 3fba1cdee04841d4 bf9a6d553414d7e6 3ff0000000000000 c02a65b293c263d1 4067575b6dcbbe96 406428a84acea57b
1024 bfa7044c64f72bf8 3fc42028672f0916 bfa4979976fd4b96 3ff0000000000000 c032004f1c66cd67 406f78c8aedeaeaf 4065038e51a04a24
1280 bfa4d8f34a12c9de 3fbfc040c577c157 bfa4d9a84a2cd957 3ff0000000000000 c038153e1b062a15 4073d9ca4dd73fd0 4065f68e5cad7526
1536 bfa36ec596f9c2bd 3fbad4221612f2b0 bfa23020eb3b196b 3ff0000000000000 c03e5941caf63f73 40780126ebb8ca89 4066faba727258e2
1792 bfa2947385623178 3fbc94e8dea08211 bfa16966aa3548e7 3ff0000000000000 c04244fe2e9602c3 407c2fdd4446bc0b 40680aff22df8fc5
2048 bfa19f5f8bd5e1c0 3fbd6cd2d763ee62 bfa1d55122368922 3ff0000000000000 c045723072f437b8 408031cac2b62800 4069241062e31b09
HASH 3e8e6a72f80e9f1b
## start B, gate law, 5120 frames: startPlane(0.0, 0.0, 950.0, 40.0, 0.1, 1.570796, 0.0, 1.0, 1.0)
256 3f8a48efc4d1c360 3fbdc20a47184edb bf906628f2526d78 3ff0000000000000 bfe5558e9823d786 40531fb3f821a4d7 408e2d170d3b0419
512 3f32509f14582fe0 3fbe0968b28b25fc bfa0ecaa2c65b914 3ff0000000000000 c002f587a67c34cd 4062cc7182175ab7 408ea6890ac70d50
768 bf863fc7b71f2378 3fb9293cf05242ae bf9f9a0dc1a0fe7e 3ff0000000000000 c010d0e20f49ea22 406bdcd2a3ad26b7 408f149ba4569fbf
1024 bf93f428124972ca 3fbaac22ff534775 bf9f920da032417f 3ff0000000000000 c016e51048ad2e60 4072658f944b604c 408f7a17891506a8
1280 bf9af40498c8aef1 3fbc93651fc1ebc5 bfa0beff9177d756 3ff0000000000000 c01c72f53c7c6e7b 4076cf646d290b1c 408fd8faf4c39639
1536 bfa0380cad81be1a 3fbd0e8e3f504e41 bfa161580101c09b 3ff0000000000000 c020f8215a94b876 407b2ee534e09a0b 40901968960187e3
1792 bfa1f56bfecb0f94 3fbd3fb34c543e3e bfa1b013ae4572fe 3ff0000000000000 c023a449b194b134 407f866f69d21559 4090446805e884d0
2048 bfa2e09fe02d3a5d 3fbda0409b875d95 bfa1ea583ef6c541 3ff0000000000000 c02636bf4a39c577 4081ebef61e2f31b 40906e0a04fe80ec
2304 bfa38f68ea3a7ab9 3fbdf89f1d1a1179 bfa22523725f9552 3ff0000000000000 c028b7a601dd879d 40841263482cfdf8 409096b53746a68e
2560 bfa4149a9029517a 3fbe2bf1d5dcd042 bfa251202c23b2ca 3ff0000000000000 c02b2d23b7eaf55c 4086372655646a45 4090beaece3bd5a9
2816 bfa47c298dc27374 3fbe51f20ede5e00 bfa26ebec442c1c6 3ff0000000000000 c02d98a2b6d28139 40885aa3428b0305 4090e626d6764106
3072 bfa4ce3ea9313703 3fbe75553bf32add bfa28661d5c891f3 3ff0000000000000 c02ffbb3fbfe25f3 408a7d27a710e6fb 40910d3f0d2d6396
3328 bfa510c731bdb8de 3fbe92b9ebfad4a2 bfa29a037aa746fc 3ff0000000000000 c0312c42f4e8acef 408c9eec1687905e 4091340f5c944993
3584 bfa54802102b7baf 3fbea9eeae59e055 bfa2a9b745561b9c 3ff0000000000000 c0325858873b3e2d 408ec01a2cf11bdc 40915aa8ea3f8cf4
3840 bfa576f1e9411f3e 3fbebd933517064b bfa2b671a6ff1889 3ff0000000000000 c033829b63a7cff3 409070685b429e17 40918118218068a7
4096 bfa59fc139a2ce8a 3fbecef7c824d3f7 bfa2c1448d593381 3ff0000000000000 c034ab73055964ee 4091809347cf217e 4091a76611968ded
4352 bfa5c406ccd8f2c4 3fbede5e4db61215 bfa2cab42a39beee 3ff0000000000000 c035d33608e1b98e 409290965eb52c67 4091cd996086d85f
4608 bfa5e4ed867fb39c 3fbeec2b560f34ec bfa2d308dab2b073 3ff0000000000000 c036fa24c3e2f03a 4093a077fc0c547a 4091f3b6f6ac86f7
4864 bfa60350fa4d5a86 3fbef8d9fdb29415 bfa2da8b06c7b592 3ff0000000000000 c038206dfdf407a5 4094b03ce3e68cc6 409219c277e1743a
5120 bfa61fd3b72a91d2 3fbf04b71810b101 bfa2e1758333253b 3ff0000000000000 c03946358a0b0413 4095bfe8aa1debc2 40923fbe99c6f15c
HASH 2e6522149455aa02
## start A, new law, 2048 frames: startPlane(0.0, 0.0, 150.0, 30.0, -0.1, 1.570796, 0.4, 1.0, 1.0)
256 bfbbdd4111069ca6 3fd2cd5cac8a084a bfbcf9c43b78b4c1 3ff0000000000000 c00791fc2705bded 404e72ae349a64a9 4062da3d2b42a57b
512 bfbcc304b7e9c428 3f9728b5de861860 bfa6f6429bf5e49e 3ff0000000000000 c022319733375574 405f492bb3adfe7d 4062d93ba8344e3c
768 bfa7624ab9ea63df 3fb7707b4c67b27d bf9d485d65886f88 3ff0000000000000 c02acaf11290c8d8 40682306f5bb200a 40635a1227d092a3
1024 bf9ef1f0918ccf7c 3fc0de8044d599ba bfa321befeae3d9e 3ff0000000000000 c032609bb4c6c2b4 40706473c4ef1da2 40644c6ba1c82d77
1280 bf96242bdb5be9af 3fbc743019c6b448 bfa2562879a8783d 3ff0000000000000 c03877ccde6c75ff 4074bd40a1171dfc 40656dbd6e1894b0
1536 bf927267202cbd74 3fb9a708cbc521a6 bfa0b4f00fcb3d0d 3ff0000000000000 c03edce3a457e317 4079188ff738deb9 4066a309db88b22d
1792 bf913c1cff197e76 3fba7358fc4420c0 bfa028e564036cd9 3ff0000000000000 c042a8caf7b03350 407d752375825239 4067e0276a329ba6
2048 bf90ade56cc5cfa1 3fbaf5df49acfca4 bfa04cb6c018a7c2 3ff0000000000000 c045f5be35c2bf05 4080e92c95dfe837 40692073aa1bf838
HASH 2947c707944678e9
## start B, new law, 5120 frames: startPlane(0.0, 0.0, 950.0, 40.0, 0.1, 1.570796, 0.0, 1.0, 1.0)
256 3fa7eb911bc522b4 3fbb0389a576f3a0 bf834e5315ba9986 3ff0000000000000 bfe4726c168c15e5 40532e443c7f1d04 408e288ec383a88d
512 3fa5646097395a6a 3fbb5fb069667a02 bf9adb05edf1361e 3ff0000000000000 c0017c839953987f 406317d7c0bd9184 408e8568001eda1d
768 3fa72132a29a5c23 3fb5676675e166ed bf986e136db98490 3ff0000000000000 c00f743584f2349d 406cd269f7934ebe 408ec4f7d3854155
1024 3fae81ef946d5c21 3fb39749a0b02cdc bf9629b02010a52a 3ff0000000000000 c015cc91c0545f48 407378ae51ff3a7a 408ef00ad80e74bd
1280 3fb47d8862945e92 3fb2382f34986a5e bf94eae8b3100267 3ff0000000000000 c01b493e643a516f 4078ca39898b4929 408f0cc712f2096c
1536 3fba7f61a30af7d4 3fb05e727fa6dedd bf93211c3254c245 3ff0000000000000 c0204c5c8a7d822b 407e6952aa47b7ef 408f1f85824eee98
1792 3fc0472bc17404ac 3fad44a6586cfcf0 bf90fd807b501b7f 3ff0000000000000 c022edbc8c6c65e1 40822df25527e381 408f2b6c724f3838
2048 3fc326358f3d597b 3faa7add70b74188 bf8dbc93c59bd869 3ff0000000000000 c02591d87f1c408e 408550f05dd11159 408f32c80a6de787
2304 3fc5bf23e42a8547 3fa83d4316ee6de0 bf89d862a6f31420 3ff0000000000000 c02843ff8a069ce4 40889be63166dd88 408f373ab6a87aad
2560 3fc811ea3247d040 3fa6667474156141 bf86548a9e1d6dab 3ff0000000000000 c02b0d573fe3950c 408c0c3beb1fb053 408f39ec9be63732
2816 3fca1b38f78c07a0 3fa4e974b2e7a92d bf833aa07a8bc556 3ff0000000000000 c02df27ccb90ab8c 408f9e9697890c5d 408f3b9bb90bab1d
3072 3fcbddf55bf2d4d7 3fa3b5f0999967c4 bf8088cc635558c0 3ff0000000000000 c0307a7076825a5a 4091a7a588cf3173 408f3cc1f0febf98
3328 3fcd5aae56aad42e 3fa2be3042cd7387 bf7c8444d2bc5301 3ff0000000000000 c0320a13b35c994d 40938d6177515f64 408f3d9ac6e69d64
3584 3fce9c21a9ec74dd 3fa1f3b65ea7e918 bf78b55fc616b24a 3ff0000000000000 c033a77afe392210 40957edd65270a5d 408f3e435ef2b9c1
3840 3fcfac20c26c19a1 3fa14c93c56738ab bf7587c1e92c82e1 3ff0000000000000 c0355196d9de79a7 40977aa2aaa88b05 408f3ecb96ae2d43
4096 3fd04b43d6c9ee59 3fa0c13e19b4f6ab bf72cbb33621c599 3ff0000000000000 c03707136faed693 40997f5a304cfd09 408f3f3f01f31375
4352 3fd0acc80df4b61e 3fa04fefe76051dc bf707f5ad254b5f9 3ff0000000000000 c038c66968da002b 409b8bbc0fb14d70 408f3fa155bfc986
4608 3fd0fe2bb0533c0e 3f9fe68dfdcae072 bf6d29b57e99464a 3ff0000000000000 c03a8e3edc617a0f 409d9ea955995b31 408f3ff3a24f0069
4864 3fd142467ee6f499 3f9f4d739040d95e bf69f97d97e5653c 3ff0000000000000 c03c5d6479b600b8 409fb72b751fe5aa 408f40389329a320
5120 3fd17bd2c07506ea 3f9ecddbf31a8f7b bf67450e75f9ff16 3ff0000000000000 c03e32c4e524b2a5 40a0ea3659bbaa55 408f40730f39e704
HASH dd0d6deef038f51a
```

## For the proof

With these changes `docs/termsound-proof.tex` needs:
- one α regime from 10 m to the level-off;
- one norm for the climb band (0.902 per second, linear part);
- one level trim above `zTop` (0.915 per second).

What remains is a covering bound on the nonlinear remainder, the switching at the |β| kink inside each second, the
heading disturbance, and the climb-to-level handover above `zTop`. That re-certification starts once this lands in
both laws.

## Turning escapes

The terminal phase applies to every escape once its pull-up ends, with an EAS reference per kind of ending: 35.2 m/s
straight, 37.8 m/s in the 30° turns, 40.3 m/s in the 40° turns and in the street escape (on its street too, so its
roll-in needs no acceleration). The turn values are 35.2/√cos φ, so the turns trim at the straight climb's α (about
0.08). `make helixlab ARGS=trim` (Rust):

- **The gate law's turns lock into a post-stall branch.** The α integral saturates at −0.4 while the pitch-rate
  feedforward keeps commanding the load factor the capped α would give unstalled, so the aircraft holds α ≈ 0.25–0.28
  at 32–33 m/s and sinks 0.1–1.7 m/s indefinitely (#30's root cause A; the crash hunts saw 33–37 m/s).
- **The terminal law has no such branch.** From every post-stall state found (5 from 400 perturbed starts, at
  300 m), it settles at 39.0 m/s (30°) or 41.3 m/s (40°), α 0.080, climbing 5.0–5.2 m/s. From 72 level starts per turn
  (24–55 m/s, γ −0.3 to 0.35, bank −0.9 to 1.1) it settles at 38.7–39.1 m/s (30°) and 41.0–41.5 m/s (40°) at 200 m,
  α 0.079–0.081, climbing 4.8–5.2 m/s.
- **The full-throttle power curve climbs at every speed from 30 m/s up** at 30° and 40° bank (stiff speed hold,
  no α cap), from 1.1–2.6 m/s at 30 m/s to 6.4–6.9 m/s at 50 m/s: the descent is the law's, not the aircraft's.

The helix end test's airspeed floor (37.5 m/s at 30°, 39.5 m/s at 40°) sits above the post-stall band and below the
terminal trims (true airspeed rises above the EAS reference with altitude). The turns settle 0.5–1.0 m/s above the
true airspeed of their EAS reference, so the end test's annulus spans the radii from the current airspeed to that
speed −1 to +2 m/s instead of waiting for the airspeed to settle.

## Speed-scheduled heading hold (adopted)

Status: implemented in both gates, bit-identical (`make gatefaith` checks the reference hashes below); measured first in the harness (`Tools/termsound/TsMap.lean`, `Cand.kpsiV`).

**Why.** The straight escape holds its track with a bank target `phiT = clamp(KPSI · wrap(psiRef − track), ±0.15)`, `KPSI = 1`. For a bank φ the turn rate is `g·tan φ / V`, so the heading mode's rate is about `g·KPSI / V`:
- 0.28 /s at the climb speed of 35 m/s;
- only 0.14 /s at the level-off speed of 70.8 m/s.

That slow lateral mode is what made both certificate families of #58 need very thin roll, heading and cross-track boxes (`lateral.py`, `docs/termsound-proof.tex` §9).

**Change.** In `controls`, the straight escape's bank target once turning (`dir == 0`) becomes:

```
ks   := max(1, v / V_KPSI)                          -- NEW, V_KPSI = 35.2 (m/s, the law's v = max(vt, 10))
phiT := clamp(KPSI * ks * wrap(psiRef - track), -0.15, 0.15)   -- was clamp(KPSI * wrap(psiRef - track), ...)
```

- **Lean:** `let ks := fmax 1.0 (v / V_KPSI)`, then `clamp (KPSI * ks * wrap (l.psiRef - track)) (-0.15) 0.15`. The product is `(KPSI * ks) * wrap(...)`.
- **Rust:** `let ks = (v / V_KPSI).max(1.0);` then `(p.kpsi * ks * wrap(self.psi_ref - track)).clamp(-0.15, 0.15)`.
- **Where it applies:** at or below 35.2 m/s true airspeed nothing changes. It stiffens the hold in proportion to speed above that, which keeps the heading mode's rate at about `g·KPSI/35.2 ≈ 0.28 /s` at any speed.

**Measured effect** at the level trim (`lateral.py`; 1,000.22 m, 70.78 m/s, flying east):

| | slowest lateral mode | settling after a 3° bank + 3° heading + 1 m/s sideslip upset | cross-track displacement |
|---|---|---|---|
| gate (`KPSI = 1`) | 0.134 /s | 15.6 s | 7.7 m |
| proposed (`KPSI·max(1, V/35.2)`) | 0.235 /s | 5.3 s | 3.9 m |

Settling is to within 0.2° in bank and heading and 0.1 m/s in sideslip. Stiffer roll gains (`KPHI = 4`, `KP = 1.2`) or a faster roll integrator (`KI_PHI = 2`) do not settle the upset sooner: 4.6–7.8 s with peak bank up to 3.2°.

**Effect on the certificate** (`membership_lat.py`; `docs/termsound-proof.tex` §9). The schedule doubles the lateral room of the surviving k-step set: about ±4.8° roll and heading and ±2 m/s cross-track speed, against ±2.4° and ±1 m/s under the gate's law.

**Effect on the climb.** None measured. Settling from the 48 representative starts is unchanged (`lateral_climb.py`): median 10.0 s, p90 13.9 s.

**Reference trajectories** (`reftraj_lat.py`; same format and hash as above, every 512 frames):

```
## start B, proposed law, 5120 frames: startPlane(0.0, 0.0, 950.0, 40.0, 0.1, 1.570796, 0.0, 1.0, 1.0)
512 3fa565aa03fa4703 3fbb7125f80201ea bf9b16855775bb3c 3ff0000000000000 c001746f909a7fa2 406317d7923d1dd6 408e856801960f91
1024 3fae80e0d186a1f0 3fb382c6a58cdcb3 bf960fa751ec0a07 3ff0000000000000 c0157652b9287c44 407378ae0b6d4bb1 408ef00ac7eb3262
1536 3fba7ecebec978d8 3fb06077b6a17903 bf93160c5bd60abb 3ff0000000000000 c01fdf240ede0c83 407e694d6fd8ba2e 408f1f8547043262
2048 3fc325f61f73e9b4 3faa7d64204117f8 bf8da3fb2fe9750e 3ff0000000000000 c0251b4637e40efa 408550ea5397e8fc 408f32c7e3557dda
2560 3fc811c13f467891 3fa66eca2766fc1f bf864d21c755e7f6 3ff0000000000000 c02a9b50fdb4df13 408c0c31bece7a64 408f39ec82dd2f9e
3072 3fcbdde24357a781 3fa3babdbc046984 bf808afb4845e690 3ff0000000000000 c0304ea2dc9f1b42 4091a79e7e7c10ed 408f3cc1e5b934f1
3584 3fce9c1a4bfb087c 3fa1f5c478bc6875 bf78c198442e336a 3ff0000000000000 c0338b9be4ec9855 40957ed4b50b6508 408f3e435b32e910
4096 3fd04b42a850ba6b 3fa0c13545595ee0 bf72d82d2cf6dde6 3ff0000000000000 c036f8522c319579 40997f503f3da713 408f3f3f014fdb09
4608 3fd0fe2b2c5a8c17 3f9fe56395c8f686 bf6d3e137a3fcb78 3ff0000000000000 c03a877d6675b47e 409d9e9e8ac42f0a 408f3ff3a2547cee
5120 3fd17bd270e808e3 3f9ecc3a3fe440ef bf675454cc69d9ed 3ff0000000000000 c03e2ed7f40db1b6 40a0ea30b54cf0a7 408f40730f4c7ec6
HASH 7e1fb4f97ce2425f
## start C, proposed law, 6400 frames: startPlane(0.0, 0.0, 950.0, 40.0, 0.1, 1.570796, 0.3, 1.0, 1.0)
512 3fa438933b82439a 3fa54a3ce54dfe24 bf9ac0aa0bfe89b4 3ff0000000000000 c02193b762c4c6f6 4063005f45540841 408e84fd30e8dad5
1024 3fad1714de836d27 3fb7a1af541d3de2 bf96163c733a116f 3ff0000000000000 c031958939d94d48 40735d35e3b86d8e 408eef7eedcec6f7
1536 3fb9eab365914042 3fb08b2224c36b82 bf933af9b88b248a 3ff0000000000000 c03d6f592aa13491 407e39c7be196eca 408f1f28b52260df
2048 3fc2ea8fe0ed6107 3fab01cae98e80ef bf8dcc8ef016b4aa 3ff0000000000000 c04595731f2f9711 40852e9f1bf418ba 408f3297d9663766
2560 3fc7e51d6a7dab30 3fa6ac0fec15a633 bf86821c653d8a9f 3ff0000000000000 c04d51a5ee69d3f8 408bdfb3cf84abd5 408f39d427558588
3072 3fcbbd24fc0a107a 3fa3daf385cf9aa0 bf80b6a92022c571 3ff0000000000000 c052e3edf9e01940 40918c9d5a26da6b 408f3cb1d43a02aa
3584 3fce84d973981869 3fa2085ffba3d228 bf7902916c85875d 3ff0000000000000 c0576714cceb2022 40955f6e0919d9df 408f3e373ce23d3d
4096 3fd042d358c3c966 3fa0ccb5b759aac8 bf7308bfe0dc09f8 3ff0000000000000 c05c208c8e9e67cd 40995bd2839de9e0 408f3f3562241774
4608 3fd0f840aa77d1b9 3f9ff3e212b06afc bf6d8375fdbe3de7 3ff0000000000000 c06080dce441d3af 409d7750420e394f 408f3fec488fe5e4
5120 3fd1779b02bdd790 3f9ed5e32dd0a0ed bf678672144686d4 3ff0000000000000 c062ffaef6c34890 40a0d4bc803d3710 408f406d4eb8a7a1
5632 3fd1d052d6e848d0 3f9e14238df04009 bf634a880a75f25d 3ff0000000000000 c065889641700158 40a2f5f56ddc8f1b 408f40c9548fbeac
6144 3fd20dbe629f1eef 3f9d9055ff0ccfe6 bf605bc0523f6495 3ff0000000000000 c068188d5e889346 40a51cf16fbf3950 408f41095c43ae2f
HASH cb2aae7e29b013a5
```
