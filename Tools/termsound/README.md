# Tools/termsound

Numerical tooling for the informal TermSound proof (`docs/termsound-proof.tex`): `tsmap` (`TsMap.lean`, driven from
Python through `tsmap.py`) runs the real escape closed loop frame by frame, and its `B` command evaluates one frame
over a box of states with interval arithmetic (`TsInterval.lean`).

## Interval enclosures (`TsInterval.frameBox`, `tsmap B`)

`frameBox` evaluates one frame (`frameG`: `placeG`, the terminal law `lawG`, `JsbExact.step` with fuel frozen, then
`chartG`) over a box `c ± b` of the 33 inputs (altitude, then the 32 chart coordinates). It uses the interval-dual
instance of `JsbExact`'s `Scalar` class, so it runs the same code as the point frame.

**What a valid enclosure guarantees.** For every point `x` of the box, the `Float` frame `frameG` at `x` has its
altitude `h'`, its 32 chart coordinates, and the plant's β and α inside the returned value intervals. This rests on:

- outward rounding, and round-to-nearest being monotone;
- `sin`, `cos`, `atan`, `asin`, `exp` and `log` being within 4 ulps (`LIBM_ULPS`), and `pow` being enclosed as
  `exp (y · log x)`;
- every undecided branch being evaluated both ways and joined (table lookups too: the hull over every segment the
  key interval reaches, clamped as the point code clamps);
- the checks behind the validity flag below.

The derivative intervals are a Jacobian enclosure only where the map is smooth across the joined branches (no law
saturation possible, as the scripts require); the validity flag is about the values.

**The validity flag.** `frameBox` returns a `BoxResult` with `valid` and `reasons`. It is valid only if all of the
following hold:

1. The input is well-formed: 33 finite centres, 33 finite non-negative half-widths, and no more base gears than the
   gear table has.
2. No point of the box touches the ground: `0.999 · hsl > 1.01 · gearReach + 3.3 ft`. `JsbExact` decides ground
   contact with `mode`, which has no join, so the instance reads an undecided contact as none. The check makes that
   correct for every point. A gear point lies within `gearReach` of the CG, and geodetic height is at least
   `0.999 ×` the radial height `hsl`.
3. β lies strictly inside ±0.349. The β tables' rule (`linRule`) uses the fact that `CYb`, `Clb` and `Cnb` are one
   line across β = 0, and that fact holds only between their outer keys.
4. Every value interval is finite. An infinite interval is sound, but it carries no information.

An invalid result's numbers must not be used. `tsmap B` prints `VALID` or `INVALID <reasons>` as its last line, and
`tsmap.py`'s `box()` raises `InvalidEnclosure` on an invalid one. `tsmap.py` also starts `tsmap` with
`LEAN_ABORT_ON_PANIC=1`. Without it, a Lean panic (such as an out-of-range `arr[i]!`) prints a message, returns a
default value and carries on. With it, the process stops and the script's read fails.

Lookups on the interval path never return a default value:

- Table reads (`JsbExact.Table.at'`) are checked: an index past the end gives NaN, which the instance reads as
  unbounded. At `Float`, `TableStop.lean` proves the checked read and the stopped walk equal the old ones on in-range
  reads (`at'_eq_old`, `seg1_eq_old`, and `get1_eq_old` for every key).
- The one-column table walk (`Table.seg1`) stops at the last segment. Without the stop, an undecided comparison
  walks past the end of the table (the piston's `mixEff` panic).
- Chart, observation and input indexing (`ix`) and derivative indexing (`ID.dget`) are checked.
- Interval endpoints are never NaN (`Iv.mk'`).
- `JsbExact.step`'s fixed-position reads of its configuration arrays are checked at build time (`#guard`s at the end
  of `TsInterval.lean`).

The only joined arrays are the friction multipliers. Both of their sides have the same length, and the friction
solver is not reached on a valid box.

**Known width blow-up.** The enclosure is sound but becomes uselessly wide (so `INVALID`, unbounded) beyond small
boxes:

- *Attitude.* At the level trim with the track held east, two of `FGMatrix33::GetQuaternion`'s four candidates
  (`LinAlg.toQuat`) are nearly equal. On a box wider than about 1e-5 rad in pitch, or about 100 m in altitude, the
  choice is undecided. The candidates give `q` and `−q`, so their join contains 0. The step's `normalize` then
  divides by an interval containing 0, and the body-axis velocities, α, β and the accelerations become unbounded.
  Measured with `make tsinterval-check`: pitch ±1e-6 rad is valid and ±1e-5 is not; altitude ±60 m is valid and
  ±150 m is not; all coordinates at 1e-5 of `trim.py`'s scales are valid, and at 1e-4 they are not.
- *Both arms on the whole box.* An undecided branch's arms are each evaluated on the whole box, not on the part
  where they apply. For example, the propeller's P-factor divides by the transverse inflow `tv` inside `tv > 1e-4`.
  So once α can reach about 0 (`v_dn` ±2 m/s), the propeller moment is unbounded.
- *Heading across north.* `chartG` does not wrap the heading difference, so on a box whose heading straddles north
  the `dpsi'` enclosure covers both sides of the wrap, about 2π wide.
- *Geodetic altitude.* Fukushima's formula encloses about 30 times wider than the altitude box, so the ground check
  uses `hsl` instead.

**Test: `make tsinterval-check`** (`TsIntervalCheck.lean`, `N` points per box, default 200). The run has two parts:

- *Frame boxes.* About 30 boxes around the level trim (`barrier_trim.json`), from a point box through 1e-9 of the
  scales to metre scale, including the two boxes that used to panic and boxes that span table breakpoints: propeller
  J and tip Mach, the piston's `mixEff`, ground-effect h/b, β across 0, and α across a `CDwbh` key. Half of the
  sampled points are uniform in the box and half are vertices. Each point is stepped with the `Float` `frameG`, and
  all 35 outputs are checked against the box's enclosure.
- *Table lookups.* Random key intervals (around a key, across several keys, and past the ends) for every table the
  frame reads, checked against `Float` lookups at points in each interval.

A point outside a valid enclosure fails the run (exit 1). Invalid boxes are reported with their reasons.
