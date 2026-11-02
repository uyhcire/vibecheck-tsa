import JsbExact.Table

/-! # `at'`, `seg1` and `get1` at `Float` equal their unchecked, unstopped versions (`…Old`) on in-range reads. -/

namespace JsbExact.Table
open S

def at'Old (t : Table) (i : Nat) : Float := lit t.data[i]!

def interp1Old (t : Table) (key : Float) (r : Nat) : Float :=
  let x0 : Float := t.at'Old (2 * r - 2)
  let span := t.at'Old (2 * r) - x0
  let factor := (key - x0) / span
  let y0 : Float := t.at'Old (2 * r - 1)
  mac factor (t.at'Old (2 * r + 1) - y0) y0

def seg1Old (t : Table) (key : Float) (r : Nat) : (fuel : Nat) → Float
  | 0 => t.interp1Old key r
  | fuel + 1 => sif lt (t.at'Old (2 * r)) key then t.seg1Old key (r + 1) fuel else t.interp1Old key r

def get1Old (t : Table) (key : Float) : Float :=
  let n := t.rows
  sif le key (t.at'Old 2) then t.at'Old 3
  else sif ge key (t.at'Old (2 * n)) then t.at'Old (2 * n + 1)
  else t.seg1Old key 2 n

theorem at'_eq_old (t : Table) (i : Nat) (h : i < t.data.size) : (t.at' i : Float) = t.at'Old i := by
  simp [at', at'Old, h, lit, Scalar.ofFloat, getElem!_pos]

/-- IEEE `<` implies `≤` (both come from the same comparison in Lean's `Float` model). -/
theorem float_le_of_lt {a b : Float} (h : a < b) : a ≤ b := by
  change a.le b = true
  change a.lt b = true at h
  simp only [Float.lt, Float.le, decide_eq_true_eq] at *
  change a.toModel.unpack.le b.toModel.unpack = true
  change a.toModel.unpack.lt b.toModel.unpack = true at h
  simp only [Float.Model.UnpackedFloat.lt, Float.Model.UnpackedFloat.le] at *
  cases hc : a.toModel.unpack.compare b.toModel.unpack with
  | none => simp [hc] at h
  | some o => cases o <;> simp_all

theorem interp1_eq_old (t : Table) (key : Float) (r : Nat) (hr : 2 * r + 1 < t.data.size) :
    (t.interp1 key r : Float) = t.interp1Old key r := by
  simp only [interp1, interp1Old]
  rw [at'_eq_old t (2 * r - 2) (by omega), at'_eq_old t (2 * r) (by omega), at'_eq_old t (2 * r - 1) (by omega),
    at'_eq_old t (2 * r + 1) (by omega)]

/-- With `key` not above the last key, the new walk (stopping at the last segment) equals the old one from any
segment `r ≤ rows`. -/
theorem seg1_eq_old (t : Table) (key : Float) (hs : 2 * t.rows + 2 ≤ t.data.size)
    (hk : ¬ (t.at' (2 * t.rows) : Float) < key) :
    ∀ (fuel r : Nat), r ≤ t.rows → (t.seg1 key r fuel : Float) = t.seg1Old key r fuel := by
  intro fuel
  induction fuel with
  | zero => intro r hr; simp only [seg1, seg1Old, interp1_eq_old t key r (by omega)]
  | succ fuel ih =>
    intro r hr
    simp only [seg1, seg1Old]
    by_cases hlt : r < t.rows
    · simp only [hlt, ite_true, S.br, Scalar.branch, S.lt, Scalar.lt, at'_eq_old t (2 * r) (by omega),
        interp1_eq_old t key r (by omega), ih (r + 1) (by omega)]
      rfl
    · have hre : r = t.rows := by omega
      subst hre
      have hk' : ¬ (t.at'Old (2 * t.rows) : Float) < key := by rwa [← at'_eq_old t _ (by omega)]
      simp only [hlt, ite_false, S.br, Scalar.branch, S.lt, Scalar.lt, hk', decide_false,
        interp1_eq_old t key t.rows (by omega)]
      rfl

theorem get1_eq_old (t : Table) (key : Float) (h2 : 2 ≤ t.rows) (hs : 2 * t.rows + 2 ≤ t.data.size) :
    (t.get1 key : Float) = t.get1Old key := by
  have e (i : Nat) (h : i < t.data.size) := at'_eq_old t i h
  simp only [get1, get1Old, S.br, Scalar.branch, S.le, S.ge, Scalar.le, e 2 (by omega), e 3 (by omega),
    e (2 * t.rows) (by omega), e (2 * t.rows + 1) (by omega)]
  by_cases h1 : key ≤ t.at'Old 2
  · simp [h1]
  · by_cases h3 : t.at'Old (2 * t.rows) ≤ key
    · simp [h1, h3]
    · have hk : ¬ (t.at' (2 * t.rows) : Float) < key := by
        rw [e _ (by omega)]; exact fun h => h3 (float_le_of_lt h)
      simp only [h1, h3, decide_false]
      exact seg1_eq_old t key hs hk t.rows 2 h2

end JsbExact.Table

#print axioms JsbExact.Table.at'_eq_old
#print axioms JsbExact.Table.seg1_eq_old
#print axioms JsbExact.Table.get1_eq_old
