/-! Fixed-point numbers on the grid `2^-16`; only `*` and `/` round (toward −∞). -/

namespace Vibecheck

structure Fx where
  raw : Int
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Fx

/-- `a * b / 2^16`, computed in `Int64` when both fit in 32 bits (see `fastMul_eq`). -/
def fastMul (a b : Int) : Int :=
  if -2147483648 ≤ a ∧ a < 2147483648 ∧ -2147483648 ≤ b ∧ b < 2147483648 then
    ((Int64.ofInt a * Int64.ofInt b) >>> (16 : Int64)).toInt
  else a * b / 65536

theorem shr16 (x : Int64) : (x >>> (16 : Int64)).toInt = x.toInt >>> 16 := by
  rw [← Int64.toInt_toBitVec]; simp [Int64.toBitVec_shiftRight]

theorem mul_bound (a b : Int) (ha : -2147483648 ≤ a ∧ a < 2147483648)
    (hb : -2147483648 ≤ b ∧ b < 2147483648) : -2^62 ≤ a * b ∧ a * b ≤ 2^62 := by
  have h1 : a.natAbs ≤ 2147483648 := by omega
  have h2 : b.natAbs ≤ 2147483648 := by omega
  have h3 : (a * b).natAbs ≤ 2147483648 * 2147483648 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul h1 h2
  omega

theorem fastMul_eq (a b : Int) : fastMul a b = a * b / 65536 := by
  unfold fastMul
  split
  · rename_i h
    have ha : (Int64.ofInt a).toInt = a := Int64.toInt_ofInt_of_le (by omega) (by omega)
    have hb : (Int64.ofInt b).toInt = b := Int64.toInt_ofInt_of_le (by omega) (by omega)
    have hm := mul_bound a b ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩
    rw [shr16, Int64.toInt_mul, ha, hb, Int.bmod_eq_of_le (by omega) (by omega),
      Int.shiftRight_eq_div_pow]
    rfl
  · rfl


@[reducible] def unit : Int := 65536

instance : OfNat Fx n := ⟨⟨(n : Int) * 65536⟩⟩
instance : Add Fx := ⟨fun a b => ⟨a.raw + b.raw⟩⟩
instance : Sub Fx := ⟨fun a b => ⟨a.raw - b.raw⟩⟩
instance : Neg Fx := ⟨fun a => ⟨-a.raw⟩⟩
/-- Fixed-point product, rounded toward −∞. -/
instance : Mul Fx := ⟨fun a b => ⟨fastMul a.raw b.raw⟩⟩
/-- Fixed-point quotient, rounded toward −∞ for positive divisors; `a / 0 = 0`. -/
instance : Div Fx := ⟨fun a b => ⟨a.raw * 65536 / b.raw⟩⟩
instance : LE Fx := ⟨fun a b => a.raw ≤ b.raw⟩
instance : LT Fx := ⟨fun a b => a.raw < b.raw⟩
instance (a b : Fx) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.raw ≤ b.raw))
instance (a b : Fx) : Decidable (a < b) := inferInstanceAs (Decidable (a.raw < b.raw))
instance : Max Fx := ⟨fun a b => if a ≤ b then b else a⟩
instance : Min Fx := ⟨fun a b => if a ≤ b then a else b⟩

/-- Decimal literals such as `0.056`, rounded toward −∞ to the grid. -/
instance : OfScientific Fx where
  ofScientific m s e :=
    if s then ⟨(m : Int) * 65536 / ((10 ^ e : Nat) : Int)⟩
    else ⟨((m * 10 ^ e : Nat) : Int) * 65536⟩

def toRat (a : Fx) : Rat := (a.raw : Rat) / 65536

/-- Conversion for drawing only (never used by the dynamics). -/
def toFloat (a : Fx) : Float := Float.ofInt a.raw / 65536.0

def clamp (lo hi a : Fx) : Fx := max lo (min hi a)

def abs (a : Fx) : Fx := if a.raw < 0 then ⟨-a.raw⟩ else a

/-- Exact division by 16 (one simulation step is `1/16` s), rounded toward −∞. -/
def div16 (a : Fx) : Fx := ⟨a.raw / 16⟩

@[simp] theorem le_def (a b : Fx) : (a ≤ b) = (a.raw ≤ b.raw) := rfl
@[simp] theorem lt_def (a b : Fx) : (a < b) = (a.raw < b.raw) := rfl
@[simp] theorem add_raw (a b : Fx) : (a + b).raw = a.raw + b.raw := rfl
@[simp] theorem sub_raw (a b : Fx) : (a - b).raw = a.raw - b.raw := rfl
@[simp] theorem neg_raw (a : Fx) : (-a).raw = -a.raw := rfl
@[simp] theorem mul_raw (a b : Fx) : (a * b).raw = a.raw * b.raw / 65536 := fastMul_eq _ _
@[simp] theorem div16_raw (a : Fx) : (div16 a).raw = a.raw / 16 := rfl
@[simp] theorem ofNat_raw (n : Nat) : (OfNat.ofNat n : Fx).raw = (n : Int) * 65536 := rfl
theorem ext_raw {a b : Fx} (h : a.raw = b.raw) : a = b := by cases a; cases b; simp_all

theorem max_def' (a b : Fx) : max a b = (if a ≤ b then b else a) := rfl
theorem min_def' (a b : Fx) : min a b = (if a ≤ b then a else b) := rfl

theorem max_raw (a b : Fx) : (max a b).raw = max a.raw b.raw := by
  rw [max_def']; by_cases h : a.raw ≤ b.raw
  · simp only [le_def, h, ite_true]; omega
  · simp only [le_def, h, ite_false]; omega

theorem min_raw (a b : Fx) : (min a b).raw = min a.raw b.raw := by
  rw [min_def']; by_cases h : a.raw ≤ b.raw
  · simp only [le_def, h, ite_true]; omega
  · simp only [le_def, h, ite_false]; omega

theorem clamp_raw (lo hi a : Fx) :
    (clamp lo hi a).raw = max lo.raw (min hi.raw a.raw) := by
  simp only [clamp, max_raw, min_raw]

theorem clamp_ge (lo hi a : Fx) : lo ≤ clamp lo hi a := by
  simp only [le_def, clamp_raw]; omega

theorem clamp_le (lo hi a : Fx) (h : lo ≤ hi) : clamp lo hi a ≤ hi := by
  simp only [le_def, clamp_raw] at *; omega

theorem clamp_of_mem (lo hi a : Fx) (h1 : lo ≤ a) (h2 : a ≤ hi) : clamp lo hi a = a := by
  simp only [le_def] at *; apply ext_raw; simp only [clamp_raw]; omega

end Fx
end Vibecheck
