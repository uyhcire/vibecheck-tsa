# Appendix: envelope regimes (not safety boundaries under the current objective)

These two folders are from the first pass of this study, before the safety objective (`docs/safety-objective.md`)
fixed what counts as a crash: actual contact with terrain or a building, with no clearance margin, and with
flight-envelope limits (angle of attack, load factor, minimum airspeed, stall) explicitly not part of safety.

- [05-low-speed](05-low-speed/README.md): slow flight, where the escape law's α cap binds.
- [06-high-speed](06-high-speed/README.md): a fast dive, where the load-factor cap binds (the richer search was held to
  4.0 g, the outer bound to 3.8 g).

Under the objective neither is a separate piece of the safety boundary. Their slices end in contact with the ground
or a tower, so they are re-run with contact markers in the main study instead: the slow valley and the fast dive as
slices `01c` and `01d` of [regime 1](../01-terrain-roof-below/README.md), the slow wallow as slice `04b` of
[regime 4](../04-wall-ahead/README.md), all with no load-factor ceiling on the search or the bound.

Everything below this page is kept as produced: markers at the gate's 4 m margin (proven safe = the gate accepts;
best found at 4 m and at 0 m), the binding causes at that margin, and demo outcomes measured then. The slice keys
`05a`, `05b`, `06` no longer exist in `regimes`; the numbers here are not regenerated.
