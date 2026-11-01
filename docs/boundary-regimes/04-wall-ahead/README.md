# Regime 4: wall or tower ahead

**What it is.** A tower face is dead ahead, too tall to simply climb over in time. The way out is to turn away (or pull up and over, if the roof is low enough), and what decides it is the distance to the face, the closing angle and the speed (which sets the turn radius). At 45 m/s the c172 can pull only about 2.8 g before its α limit, so a turn needs about 80 m of radius plus the roll-in.

## Location

The park-side tower again (box `x ∈ [−218.1, −186.2]`, `y ∈ [255.8, 334.5]`, 87 m tall, setback tiers of 129 m and 157 m behind it), approached head-on across the open park: start on `y = 295`, 40 m from the face's north end and 39 m from its south end, 50 m above the ground, heading east, 45 m/s, level, wings level. Varied: distance from the aircraft's centre to the face, 5 to 250 m.

## Slice

![wall ahead](04-wall-ahead.svg)

| Proven safe | Best found, 4 m | Best found, 0 m | Proven unsafe | Filter conservatism | Cost of the 4 m margin | Outer-bound slack |
|---|---|---|---|---|---|---|
| 188.0 m | 117.5 m | 109.5 m | 28.0 m | 70.4 m | 8.0 m | 81.5 m |

**Binding causes along the slice.** Inside 188 m every escape hits the face ahead (`wall-ahead`), with the load-factor cap binding closer than about 120 m. Between 152 m and 188 m a few escapes clip the face beside them instead (`wall-side`) as they turn away, and around 176 m the climbing escapes hit the 87 m roof (`roof`): that is where a pull-up over the roof stops being an option. Only the left 40° turn verifies, from 188 m.

**Where the conservatism is.** The biggest gap of the wall regimes: 70.4 m between what the filter certifies and what the search finds with the same 4 m margin. The library's turns roll in only once the climb is established (the 40° turns as soon as the flight path is 1.7° up, the 30° turns after at least 1.5 s), at the shared roll gains, and hold 30° or 40°; the search's program at the 4 m marker rolls straight into a 53° and then 70° bank (1.3 g, then 2.8 g) for 1.8 s, rolls level for a 2.9 g pull for a second, then flies a 45° climbing turn. So the lever is the escape library: a hard level break-turn at 60° or more before the climb. The outer bound proves unsafety only within 28 m, 4× closer than the best found: it lets the point mass turn at `(3.8 g + g) / V` in any direction at once, nearly twice the 2.8 g level turn rate the c172 actually has at 45 m/s, with no roll-in.

<!-- DEMOS -->

<!-- WILD -->

## State of progress

- **Exact:** escapes flown on the bit-exact JSBSim port.
- **Numerical:** clearance at 1/16 s samples; terminal sets on the settled rollout.
- **Formally proved:** nothing for this regime.
- **Main lever:** the escape library (a hard break-turn escape: up to 70 m here). The outer bound would tighten by using the c172's stall limit per unit dynamic pressure instead of 3.8 g at this speed and by charging the turn for supporting the aircraft's weight.
