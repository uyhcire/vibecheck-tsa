import JsbExact.Scalar

/-! `FGTable` lookups.  `data` is JSBSim's `Data` vector: element (r, c) is `data[r*(cols+1)+c]`, row 0 holds
the column keys, column 0 the row keys. -/

namespace JsbExact
open S

structure Table where
  rows : Nat
  cols : Nat
  data : Array Float

variable {α : Type} [Scalar α]

namespace Table
/-- `data[i]`, checked: an index past the end gives NaN, never a panic's default value. No lookup below reads past
the end (each walk stops at the last row or column), so the `Float` instance never takes that branch; for a
set-valued instance NaN is the explicit failure (an interval instance reads it as unbounded). -/
@[inline] def at' (t : Table) (i : Nat) : α := lit (if h : i < t.data.size then t.data[i] else 0.0 / 0.0)

/-- Interpolation on segment `r` (between key rows `r - 1` and `r`) of a one-column table. -/
@[inline] def interp1 (t : Table) (key : α) (r : Nat) : α :=
  let x0 : α := t.at' (2 * r - 2)
  let span := t.at' (2 * r) - x0
  let factor := (key - x0) / span
  let y0 : α := t.at' (2 * r - 1)
  mac factor (t.at' (2 * r + 1) - y0) y0

/-- `interp1` on the first segment from `r` whose upper key is not below `key`, stopping at the last segment (`r =
rows`). `get1` calls it only for `key` below the last key, so on a point the walk never reaches the stop and the stop
changes nothing; a set-valued instance that cannot decide a comparison explores both sides, and without the stop it
walked past the end of `data`. -/
def seg1 (t : Table) (key : α) (r : Nat) : (fuel : Nat) → α
  | 0 => t.interp1 key r
  | fuel + 1 =>
    if r < t.rows then
      sif lt (t.at' (2 * r)) key then t.seg1 key (r + 1) fuel else t.interp1 key r
    else t.interp1 key r

def get1 (t : Table) (key : α) : α :=
  let n := t.rows
  sif le key (t.at' 2) then t.at' 3
  else sif ge key (t.at' (2 * n)) then t.at' (2 * n + 1)
  else t.seg1 key 2 n

/-- Bilinear cell (row segment `r`, column segment `c`) with column fraction `cf`. -/
@[inline] def cell2 (t : Table) (rowKey cf : α) (c r : Nat) : α :=
  let w := t.cols + 1
  let x0 : α := t.at' ((r - 1) * w)
  let span := t.at' (r * w) - x0
  let rf := constrain zero ((rowKey - x0) / span) one
  let c1 := mac rf (t.at' (r * w + c - 1)) ((one - rf) * t.at' ((r - 1) * w + c - 1))
  let c2 := mac rf (t.at' (r * w + c)) ((one - rf) * t.at' ((r - 1) * w + c))
  mac cf (c2 - c1) c1

def rowSeg (t : Table) (rowKey cf : α) (c r : Nat) : (fuel : Nat) → α
  | 0 => t.cell2 rowKey cf c r
  | fuel + 1 =>
    if r < t.rows then
      sif lt (t.at' (r * (t.cols + 1))) rowKey then t.rowSeg rowKey cf c (r + 1) fuel else t.cell2 rowKey cf c r
    else t.cell2 rowKey cf c r

/-- `get2` once the column segment `c` is known. -/
def get2At (t : Table) (rowKey colKey : α) (c : Nat) : α :=
  let w := t.cols + 1
  let x0 : α := t.at' (c - 1)
  let span := t.at' c - x0
  let cf := constrain zero ((colKey - x0) / span) one
  if t.rows == 1 then
    let y0 : α := t.at' (w + c - 1)
    mac cf (t.at' (w + c) - y0) y0
  else t.rowSeg rowKey cf c 2 t.rows

def colSeg (t : Table) (rowKey colKey : α) (c : Nat) : (fuel : Nat) → α
  | 0 => t.get2At rowKey colKey c
  | fuel + 1 =>
    if c < t.cols then
      sif lt (t.at' c) colKey then t.colSeg rowKey colKey (c + 1) fuel else t.get2At rowKey colKey c
    else t.get2At rowKey colKey c

def get2 (t : Table) (rowKey colKey : α) : α :=
  if t.cols == 1 then t.get1 rowKey else t.colSeg rowKey colKey 2 t.cols
end Table

end JsbExact
