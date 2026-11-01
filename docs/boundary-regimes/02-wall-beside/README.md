# Regime 2: wall beside

**What it is.** A tall face runs alongside the aircraft, which is drifting toward it at a shallow angle. The way out is to turn away before the drift closes the gap, and the wing on the wall side is what touches first. What decides it: the distance to the face, the heading angle into it, and the bank (which tilts the near wingtip toward or away from the glass). Every failing escape hits the face beside it (`wall-side`); close to the face the 40° turns and the street escape also run into their load-factor cap.

## Location

The west face of the park-side tower: box `x ∈ [−218.1, −186.2]`, `y ∈ [255.8, 334.5]`, 87 m tall, with 129 m and 157 m setback tiers behind it. The park is open to the west. Start abreast of the face's south end, `y = 265`, 50 m above the ground, heading north and 10° into the face (both slices), 45 m/s, wings level.

| Slice | Fixed | Varied |
|---|---|---|
| `02a-wall-beside-park` | heading 10° into the face | distance from the aircraft's centre to the face, 0 to 80 m |
| `02b-wall-beside-angle` | 25 m from the face | heading angle into the face, 0 to 45° |

## Slices

![distance](02a-wall-beside-park.svg)

![angle](02b-wall-beside-angle.svg)

| Slice | Proven safe | Best found, 4 m | Best found, 0 m | Proven unsafe | Filter conservatism | Cost of the 4 m margin | Outer-bound slack |
|---|---|---|---|---|---|---|---|
| distance (m) | 16.0 | 13.5 | 9.5 | 0.5 | 2.5 | 4.0 | 9.0 |
| angle at 25 m (°) | 17.7 | 24.2 | 28.1 | none to 45° | 6.5° | 3.9° | ≥ 17° |

**Binding causes along the slices.** On the distance slice, the left 40° turn (away from the face) is the escape that verifies closest, from 16 m; the left 30° turn and the street escape join at 22 m and 20 m. The right 30° turn (toward the face) hits it out to 46 m, the right 40° turn hits it or the tower beyond at every distance on the slice, and the straight escape hits it out to 26 m; beyond that the straight escape's terminal ray is blocked by the towers north of the park. On the angle slice the same left 40° turn verifies up to 17.7° and everything hits the face beside it beyond that; at 45° the right 40° turn's hit becomes a hit ahead.

**Where the conservatism is.** On the distance slice the filter is 2.5 m from the best found with its own margin: the search's program rolls into a 56° to 61° bank at 3.3 to 3.5 g for about 0.9 s before a 33° to 45° climbing turn, where the library's steepest turn is 40°. On the angle slice the same lever is worth 6.5°. The margin costs 4 m (or 4°). The outer bound proves almost nothing here: a point mass may put its whole 3.8 g sideways at once, which stops a 10° drift at 45 m/s (7.8 m/s toward the face) within a metre, so it only proves unsafety when the aircraft is already against the face (0.5 m) and never on the angle slice.

<!-- DEMOS -->

<!-- WILD -->

## State of progress

- **Exact:** escapes flown on the bit-exact JSBSim port, with the wing as a capsule along the drawn wing line, banked with the aircraft (`World::airframe_clearance`).
- **Numerical:** clearance at 1/16 s samples; terminal sets on the settled rollout.
- **Formally proved:** nothing for this regime (the formal work in `Envelope/` is longitudinal and terrain-only).
- **Main lever:** the margin (4 m) and a steeper, harder roll-away escape (a 60° bank for the first second; 2.5 m, 6.5°). The outer bound would need lift to support the aircraft's weight in a level turn to say anything useful.
