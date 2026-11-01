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
@[inline] def at' (t : Table) (i : Nat) : α := lit t.data[i]!

def scan1 (t : Table) (key : α) (r : Nat) : (fuel : Nat) → Nat
  | 0 => r
  | fuel + 1 => if lt (t.at' (2 * r)) key then t.scan1 key (r + 1) fuel else r

def get1 (t : Table) (key : α) : α :=
  let n := t.rows
  if le key (t.at' 2) then t.at' 3
  else if ge key (t.at' (2 * n)) then t.at' (2 * n + 1)
  else
    let r := t.scan1 key 2 n
    let x0 : α := t.at' (2 * r - 2)
    let span := t.at' (2 * r) - x0
    let factor := (key - x0) / span
    let y0 : α := t.at' (2 * r - 1)
    mac factor (t.at' (2 * r + 1) - y0) y0

def scanC (t : Table) (key : α) (c : Nat) : (fuel : Nat) → Nat
  | 0 => c
  | fuel + 1 => if lt (t.at' c) key && c < t.cols then t.scanC key (c + 1) fuel else c

def scanR (t : Table) (key : α) (r : Nat) : (fuel : Nat) → Nat
  | 0 => r
  | fuel + 1 => if lt (t.at' (r * (t.cols + 1))) key && r < t.rows then t.scanR key (r + 1) fuel else r

def get2 (t : Table) (rowKey colKey : α) : α :=
  if t.cols == 1 then t.get1 rowKey else
  let w := t.cols + 1
  let c := t.scanC colKey 2 t.cols
  let x0 : α := t.at' (c - 1)
  let span := t.at' c - x0
  let cf := constrain zero ((colKey - x0) / span) one
  if t.rows == 1 then
    let y0 : α := t.at' (w + c - 1)
    mac cf (t.at' (w + c) - y0) y0
  else
    let r := t.scanR rowKey 2 t.rows
    let x0 : α := t.at' ((r - 1) * w)
    let span := t.at' (r * w) - x0
    let rf := constrain zero ((rowKey - x0) / span) one
    let c1 := mac rf (t.at' (r * w + c - 1)) ((one - rf) * t.at' ((r - 1) * w + c - 1))
    let c2 := mac rf (t.at' (r * w + c)) ((one - rf) * t.at' ((r - 1) * w + c))
    mac cf (c2 - c1) c1
end Table

end JsbExact
