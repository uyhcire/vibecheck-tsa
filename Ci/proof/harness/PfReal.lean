import Ci.proof.T
open Vibecheck Jsb

/-! Float stand-in for the real-number model (exact arithmetic, continuous tables), in raw units (value · 2^16), to
measure the per-tick gap between the Fx tick and the real tick from the same state and input. -/

namespace PfReal

structure R where v : Float deriving Inhabited

def segF (xs : Array Int) (x : Float) : Nat := Id.run do
  let mut i := 0
  for k in [0:xs.size] do
    if k + 2 < xs.size ∧ Float.ofInt xs[k + 1]! ≤ x then i := k + 1
  return i
def lerpF (x0 x1 y0 y1 x : Float) : Float := if x1 > x0 then y0 + (y1 - y0) * (x - x0) / (x1 - x0) else y0
def tbl1F (t : Tbl1) (x : Float) : Float :=
  let n := t.xs.size
  if x ≤ Float.ofInt t.xs[0]! then Float.ofInt t.ys[0]! else if Float.ofInt t.xs[n - 1]! ≤ x then Float.ofInt t.ys[n - 1]! else
  let i := segF t.xs x
  lerpF (Float.ofInt t.xs[i]!) (Float.ofInt t.xs[i + 1]!) (Float.ofInt t.ys[i]!) (Float.ofInt t.ys[i + 1]!) x
def tbl2F (t : Tbl2) (r c : Float) : Float :=
  let nc := t.cols.size
  let rc := max (Float.ofInt t.rows[0]!) (min (Float.ofInt t.rows[t.rows.size - 1]!) r)
  let cc := max (Float.ofInt t.cols[0]!) (min (Float.ofInt t.cols[nc - 1]!) c)
  let i := segF t.rows rc
  let j := segF t.cols cc
  let cell (a b : Nat) : Float := Float.ofInt t.data[a * nc + b]!
  let row (a : Nat) : Float := lerpF (Float.ofInt t.cols[j]!) (Float.ofInt t.cols[j + 1]!) (cell a j) (cell a (j + 1)) cc
  lerpF (Float.ofInt t.rows[i]!) (Float.ofInt t.rows[i + 1]!) (row i) (row (i + 1)) rc
def atmF (tab : Array Int) (h : Float) : Float :=
  let span := 50 * 65536.0
  let hc := max 0 (min (span * 159) h)
  let i := (hc / span).floor.toUInt64.toNat
  let f := hc - i.toFloat * span
  Float.ofInt tab[i]! + (Float.ofInt tab[i + 1]! - Float.ofInt tab[i]!) * f / span

instance : Scalar R where
  add a b := ⟨a.v + b.v⟩
  sub a b := ⟨a.v - b.v⟩
  neg a := ⟨-a.v⟩
  mul a b := ⟨a.v * b.v / 65536⟩
  div a b := ⟨a.v * 65536 / b.v⟩
  max a b := if a.v ≤ b.v then b else a
  min a b := if a.v ≤ b.v then a else b
  lit r := ⟨Float.ofInt r⟩
  mulR a b := ⟨a.v * b.v / 65536⟩
  shr a k := ⟨a.v / (2 ^ k.toFloat)⟩
  ab3 a b c := ⟨(23 * a.v - 16 * b.v + 5 * c.v) / 12⟩
  abs a := ⟨a.v.abs⟩
  sqrt a := ⟨Float.sqrt (max 0 a.v * 65536)⟩
  atan2 y x := ⟨Float.atan2 y.v x.v * 65536⟩
  tbl1 t x := ⟨tbl1F t x.v⟩
  tbl2 t r c := ⟨tbl2F t r.v c.v⟩
  atm t h := ⟨atmF t h.v⟩
  selLt a b t e := if a.v < b.v then t else e
  selLe a b t e := if a.v ≤ b.v then t else e
  rnC c s := ⟨c.v * (98304 - (c.v * c.v / 65536 + s.v * s.v / 65536) / 2) / 65536⟩
  rnS c s := ⟨s.v * (98304 - (c.v * c.v / 65536 + s.v * s.v / 65536) / 2) / 65536⟩

def ofFx (s : State) : StateOf R := s.map fun x => ⟨Float.ofInt x.raw⟩

/-- For each input state (21 ints), the real tick's end state minus the Fx tick's (19 floats, raw units). -/
def run : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    let a := ((l.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
    if a.size < 21 then break
    let f := fun (i : Nat) => (⟨a[i]!⟩ : Fx)
    let s : State := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩
    let m : Ci.Lawfirst.Mem := ⟨a[19]!, a[20]!⟩
    let u := Ci.clampInput (Ci.Proof.step m s).1
    let sF := tickAB u s
    let uR : InputOf R := u.map fun x => ⟨Float.ofInt x.raw⟩
    let sR := tickAB uR (ofFx s)
    let d := [sR.h.v - Float.ofInt sF.h.raw, sR.vx.v - Float.ofInt sF.vx.raw, sR.vz.v - Float.ofInt sF.vz.raw,
      sR.dx.v - Float.ofInt sF.dx.raw, sR.dz.v - Float.ofInt sF.dz.raw, sR.q.v - Float.ofInt sF.q.raw,
      sR.rpm.v - Float.ofInt sF.rpm.raw, sR.tmap.v - Float.ofInt sF.tmap.raw, sR.au.v - Float.ofInt sF.au.raw,
      sR.ah.v - Float.ofInt sF.ah.raw, sR.wdot.v - Float.ofInt sF.wdot.raw, sR.qd.v - Float.ofInt sF.qd.raw]
    IO.println (" ".intercalate (d.map toString))

end PfReal
