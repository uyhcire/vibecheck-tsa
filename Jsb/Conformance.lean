import Jsb.Escape
import Jsb.Enc

/-! One-tick properties of the closed loop (model + escape autopilot), proved by interval bisection checked
in the kernel. -/

namespace Jsb
open Vibecheck

variable {α : Type} [Scalar α]

/-- One substep that also accumulates the vz and vx increments it applies (`integrate`'s AB2 updates). -/
def incStep (u : InputOf α) (p : α × α × StateOf α) : α × α × StateOf α :=
  (p.1 + Scalar.shr (3 * p.2.2.au - p.2.2.au1) 8, p.2.1 + Scalar.shr (3 * p.2.2.ah - p.2.2.ah1) 8,
   step 7 true u p.2.2)

/-- vz and vx increments over one closed-loop escape tick. -/
def tickIncr (c : CLOf α) : α × α :=
  let r := iter 8 (incStep (Escape.input c)) (0, 0, c.s)
  (r.1, r.2.1)

def CLOf.map {β γ : Type} (f : β → γ) (c : CLOf β) : CLOf γ := ⟨c.s.map f, f c.elev⟩
def CLOf.Mem (B : CLOf Iv) (c : CLOf Fx) : Prop := B.s.Mem c.s ∧ B.elev.Mem c.elev

/-- Raw coordinate `i` (state fields in declaration order, then the elevator). -/
def CLOf.get (c : CLOf β) (i : Nat) : β :=
  match i with
  | 0 => c.s.x | 1 => c.s.h | 2 => c.s.vx | 3 => c.s.vz | 4 => c.s.dx | 5 => c.s.dz | 6 => c.s.q
  | 7 => c.s.rpm | 8 => c.s.tmap | 9 => c.s.udot | 10 => c.s.wdot | 11 => c.s.stall | 12 => c.s.ah
  | 13 => c.s.au | 14 => c.s.qd | 15 => c.s.ah1 | 16 => c.s.au1 | 17 => c.s.pvz | 18 => c.s.pvz2
  | _ => c.elev

/-- Replace coordinate `i`. -/
def CLOf.set (c : CLOf β) (i : Nat) (v : β) : CLOf β :=
  let s := c.s
  match i with
  | 0 => ⟨{ s with x := v }, c.elev⟩ | 1 => ⟨{ s with h := v }, c.elev⟩ | 2 => ⟨{ s with vx := v }, c.elev⟩
  | 3 => ⟨{ s with vz := v }, c.elev⟩ | 4 => ⟨{ s with dx := v }, c.elev⟩ | 5 => ⟨{ s with dz := v }, c.elev⟩
  | 6 => ⟨{ s with q := v }, c.elev⟩ | 7 => ⟨{ s with rpm := v }, c.elev⟩ | 8 => ⟨{ s with tmap := v }, c.elev⟩
  | 9 => ⟨{ s with udot := v }, c.elev⟩ | 10 => ⟨{ s with wdot := v }, c.elev⟩
  | 11 => ⟨{ s with stall := v }, c.elev⟩ | 12 => ⟨{ s with ah := v }, c.elev⟩ | 13 => ⟨{ s with au := v }, c.elev⟩
  | 14 => ⟨{ s with qd := v }, c.elev⟩ | 15 => ⟨{ s with ah1 := v }, c.elev⟩ | 16 => ⟨{ s with au1 := v }, c.elev⟩
  | 17 => ⟨{ s with pvz := v }, c.elev⟩ | 18 => ⟨{ s with pvz2 := v }, c.elev⟩ | _ => ⟨s, v⟩

end Jsb

namespace Jsb
open Vibecheck

def P3map {β γ : Type} (f : β → γ) (p : β × β × StateOf β) : γ × γ × StateOf γ := (f p.1, f p.2.1, p.2.2.map f)

theorem incStep_v (u : InputOf Enc) (p : Enc × Enc × StateOf Enc) :
    P3map Enc.v (incStep u p) = incStep (u.map Enc.v) (P3map Enc.v p) := by kernel_rfl
theorem incStep_i (u : InputOf Enc) (p : Enc × Enc × StateOf Enc) :
    P3map Enc.i (incStep u p) = incStep (u.map Enc.i) (P3map Enc.i p) := by kernel_rfl
theorem input_v (c : CLOf Enc) : (Escape.input c).map Enc.v = Escape.input (c.map Enc.v) := by kernel_rfl
theorem input_i (c : CLOf Enc) : (Escape.input c).map Enc.i = Escape.input (c.map Enc.i) := by kernel_rfl
theorem command_v (c : CLOf Enc) : (Escape.command c).v = Escape.command (c.map Enc.v) := by kernel_rfl
theorem command_i (c : CLOf Enc) : (Escape.command c).i = Escape.command (c.map Enc.i) := by kernel_rfl

theorem tickIncr_comm [Scalar β] (p : Enc → β) (hp : ∀ (u : InputOf Enc) (q : Enc × Enc × StateOf Enc),
      P3map p (incStep u q) = incStep (u.map p) (P3map p q)) (hin : ∀ c : CLOf Enc, (Escape.input c).map p = Escape.input (c.map p))
    (h0 : p 0 = 0) (c : CLOf Enc) : (p (tickIncr c).1, p (tickIncr c).2) = tickIncr (c.map p) := by
  unfold tickIncr
  have := iter_comm 8 (incStep (Escape.input c)) (incStep (Escape.input (c.map p))) (P3map p)
    (fun q => by rw [hp, hin]) (0, 0, c.s)
  simp only [P3map] at this
  rw [h0] at this
  exact congrArg (fun q => (q.1, q.2.1)) this

def CLOf.zip (c : CLOf Fx) (B : CLOf Iv) (h : B.Mem c) : CLOf Enc := ⟨c.s.zip B.s h.1, ⟨c.elev, B.elev, h.2⟩⟩

theorem tickIncr_sound {c : CLOf Fx} {B : CLOf Iv} (h : B.Mem c) :
    (tickIncr B).1.Mem (tickIncr c).1 ∧ (tickIncr B).2.Mem (tickIncr c).2 := by
  have hv := tickIncr_comm Enc.v incStep_v input_v rfl (c.zip B h)
  have hi := tickIncr_comm Enc.i incStep_i input_i rfl (c.zip B h)
  have e1 : (c.zip B h).map Enc.v = c := rfl
  have e2 : (c.zip B h).map Enc.i = B := rfl
  rw [e1] at hv; rw [e2] at hi
  rw [← hv, ← hi]
  exact ⟨(tickIncr (c.zip B h)).1.h, (tickIncr (c.zip B h)).2.h⟩

theorem step_vz (u : InputOf Fx) (s : StateOf Fx) :
    (step 7 true u s).vz = s.vz + Scalar.shr (3 * s.au - s.au1) 8 := by kernel_rfl
theorem step_vx (u : InputOf Fx) (s : StateOf Fx) :
    (step 7 true u s).vx = s.vx + Scalar.shr (3 * s.ah - s.ah1) 8 := by kernel_rfl

theorem iter_incStep (u : InputOf Fx) : ∀ (n : Nat) (a b : Fx) (s : StateOf Fx),
    (iter n (incStep u) (a, b, s)).2.2 = iter n (step 7 true u) s ∧
    (iter n (incStep u) (a, b, s)).1.raw = a.raw + (iter n (step 7 true u) s).vz.raw - s.vz.raw ∧
    (iter n (incStep u) (a, b, s)).2.1.raw = b.raw + (iter n (step 7 true u) s).vx.raw - s.vx.raw := by
  intro n
  induction n with
  | zero => intro a b s; simp [iter]
  | succ n ih =>
    intro a b s
    simp only [iter]
    have := ih (a + Scalar.shr (3 * s.au - s.au1) 8) (b + Scalar.shr (3 * s.ah - s.ah1) 8) (step 7 true u s)
    simp only [incStep]
    refine ⟨this.1, ?_, ?_⟩
    · rw [this.2.1]; rw [step_vz]; show _ + _ + _ - (s.vz.raw + _) = _; omega
    · rw [this.2.2]; rw [step_vx]; show _ + _ + _ - (s.vx.raw + _) = _; omega

/-- vz and vx increments of the escape tick, as computed by `tickIncr` on `Fx`. -/
theorem tickIncr_fx (c : CLOf Fx) :
    (tickIncr c).1.raw = (Escape.tick c).s.vz.raw - c.s.vz.raw ∧
    (tickIncr c).2.raw = (Escape.tick c).s.vx.raw - c.s.vx.raw := by
  have h := iter_incStep (Escape.input c) 8 0 0 c.s
  have z0 : (0 : Fx).raw = 0 := rfl
  unfold tickIncr Escape.tick tickAB
  refine ⟨?_, ?_⟩
  · rw [h.2.1]; show (0 : Fx).raw + _ - _ = (iter 8 (step 7 true (Escape.input c)) c.s).vz.raw - _
    rw [z0, Int.zero_add]
  · rw [h.2.2]; show (0 : Fx).raw + _ - _ = (iter 8 (step 7 true (Escape.input c)) c.s).vx.raw - _
    rw [z0, Int.zero_add]

end Jsb

namespace Jsb
open Vibecheck

theorem CLOf.mem_get {B : CLOf Iv} {c : CLOf Fx} (h : B.Mem c) (i : Nat) : (B.get i).Mem (c.get i) := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩, h19⟩ := h
  unfold CLOf.get
  split <;> assumption

theorem CLOf.mem_set {B : CLOf Iv} {c : CLOf Fx} (h : B.Mem c) (i : Nat) {v : Iv} (hv : v.Mem (c.get i)) :
    (B.set i v).Mem c := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩, h19⟩ := h
  unfold CLOf.set
  unfold CLOf.get at hv
  split <;> simp_all [CLOf.Mem, StateOf.Mem]

/-- Linear constraint `lo ≤ Σ k * raw(coordinate i) ≤ hi`. -/
structure LinCon where
  terms : List (Int × Nat)
  lo : Int
  hi : Int

def LinCon.val (l : LinCon) (c : CLOf Fx) : Int := l.terms.foldl (fun a t => a + t.1 * (c.get t.2).raw) 0
def LinCon.Holds (l : LinCon) (c : CLOf Fx) : Prop := l.lo ≤ l.val c ∧ l.val c ≤ l.hi

def termI (k : Int) : Iv → Option (Int × Int)
  | .box a b => some (Min.min (k * a) (k * b), Max.max (k * a) (k * b))
  | .top => none

def LinCon.range (l : LinCon) (B : CLOf Iv) : Option (Int × Int) :=
  l.terms.foldl (fun o t => match o, termI t.1 (B.get t.2) with
    | some (a, b), some (p, q) => some (a + p, b + q)
    | _, _ => none) (some (0, 0))

def LinCon.feasible (l : LinCon) (B : CLOf Iv) : Bool :=
  match l.range B with
  | some (a, b) => decide (a ≤ l.hi) && decide (l.lo ≤ b)
  | none => true

theorem termI_sound {k : Int} {I : Iv} {x : Fx} (h : I.Mem x) {p q : Int} (ht : termI k I = some (p, q)) :
    p ≤ k * x.raw ∧ k * x.raw ≤ q := by
  cases I with
  | top => simp [termI] at ht
  | box a b =>
    simp only [termI, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact Iv.mulRange (x := k) a b h

theorem foldl_none {γ : Type} (f : Option (Int × Int) → γ → Option (Int × Int)) (hf : ∀ t, f none t = none) :
    ∀ ts : List γ, ts.foldl f none = none := by
  intro ts; induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.foldl, hf, ih]

theorem LinCon.range_sound (B : CLOf Iv) (c : CLOf Fx) (h : B.Mem c) :
    ∀ (ts : List (Int × Nat)) (a b acc : Int), a ≤ acc → acc ≤ b → ∀ p q,
      ts.foldl (fun o t => match o, termI t.1 (B.get t.2) with
        | some (a, b), some (p, q) => some (a + p, b + q)
        | _, _ => none) (some (a, b)) = some (p, q) →
      p ≤ ts.foldl (fun a t => a + t.1 * (c.get t.2).raw) acc ∧ ts.foldl (fun a t => a + t.1 * (c.get t.2).raw) acc ≤ q := by
  intro ts
  induction ts with
  | nil => intro a b acc h1 h2 p q hf; simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hf ⊢; omega
  | cons t ts ih =>
    intro a b acc h1 h2 p q hf
    simp only [List.foldl] at hf ⊢
    cases ht : termI t.1 (B.get t.2) with
    | none =>
      rw [ht] at hf
      simp only at hf
      rw [foldl_none _ (fun _ => rfl)] at hf
      simp at hf
    | some pq =>
      obtain ⟨p', q'⟩ := pq
      rw [ht] at hf
      have hb := termI_sound (CLOf.mem_get h t.2) ht
      exact ih _ _ _ (by omega) (by omega) p q hf

theorem LinCon.feasible_of (l : LinCon) {B : CLOf Iv} {c : CLOf Fx} (h : B.Mem c) (hl : l.Holds c) :
    l.feasible B = true := by
  unfold LinCon.feasible
  cases hr : l.range B with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have := LinCon.range_sound B c h l.terms 0 0 0 (by omega) (by omega) a b hr
    unfold LinCon.Holds LinCon.val at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

def allFeasible (ls : List LinCon) (B : CLOf Iv) : Bool := ls.all (·.feasible B)

theorem allFeasible_of {ls : List LinCon} {B : CLOf Iv} {c : CLOf Fx} (h : B.Mem c) (hl : ∀ l ∈ ls, l.Holds c) :
    allFeasible ls B = true := by
  unfold allFeasible; rw [List.all_eq_true]; exact fun l hm => LinCon.feasible_of l h (hl l hm)

def halve (B : CLOf Iv) (i : Nat) : CLOf Iv × CLOf Iv :=
  match B.get i with
  | .box a b => (B.set i (.box a ((a + b) / 2)), B.set i (.box ((a + b) / 2) b))
  | .top => (B, B)

theorem halve_cover {B : CLOf Iv} {c : CLOf Fx} (h : B.Mem c) (i : Nat) :
    (halve B i).1.Mem c ∨ (halve B i).2.Mem c := by
  have hg := CLOf.mem_get h i
  unfold halve
  split
  · rename_i a b he
    rw [he] at hg
    simp only [Iv.mem_box] at hg
    by_cases hm : (c.get i).raw ≤ (a + b) / 2
    · exact Or.inl (CLOf.mem_set h i ⟨hg.1, hm⟩)
    · exact Or.inr (CLOf.mem_set h i ⟨by omega, hg.2⟩)
  · exact Or.inl h

def width : Iv → Int
  | .box a b => b - a
  | .top => 0

/-- Coordinate to split: largest `weight * width` among `dims`. -/
def pick (dims : List (Nat × Int)) (B : CLOf Iv) : Nat :=
  (dims.foldl (fun (best : Nat × Int) d =>
    let sc := d.2 * width (B.get d.1)
    if best.2 < sc then (d.1, sc) else best) (19, -1)).1

/-- Bisection checker: every sub-box is infeasible, satisfies `ok`, or is split (depth ≤ `n`). -/
def checkRec (ok : CLOf Iv → Bool) (cons : List LinCon) (dims : List (Nat × Int)) : Nat → CLOf Iv → Bool
  | 0, B => !allFeasible cons B || ok B
  | n + 1, B => !allFeasible cons B || ok B ||
      (checkRec ok cons dims n (halve B (pick dims B)).1 && checkRec ok cons dims n (halve B (pick dims B)).2)

theorem checkRec_sound (ok : CLOf Iv → Bool) (P : CLOf Fx → Prop) (cons : List LinCon) (dims : List (Nat × Int))
    (hok : ∀ B c, B.Mem c → ok B = true → P c) :
    ∀ n B, checkRec ok cons dims n B = true → ∀ c, B.Mem c → (∀ l ∈ cons, l.Holds c) → P c := by
  intro n
  induction n with
  | zero =>
    intro B hc c hm hl
    simp only [checkRec, Bool.or_eq_true, Bool.not_eq_true'] at hc
    rcases hc with hf | ho
    · rw [allFeasible_of hm hl] at hf; simp at hf
    · exact hok B c hm ho
  | succ n ih =>
    intro B hc c hm hl
    simp only [checkRec, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hc
    rcases hc with (hf | ho) | ⟨h1, h2⟩
    · rw [allFeasible_of hm hl] at hf; simp at hf
    · exact hok B c hm ho
    · rcases halve_cover hm (pick dims B) with hL | hR
      · exact ih _ h1 c hL hl
      · exact ih _ h2 c hR hl

/-- Interval check of the two increment bounds on one box. -/
def incrOK (dvzMin dvxMin : Int) (B : CLOf Iv) : Bool :=
  match tickIncr B with
  | (.box a _, .box b _) => decide (dvzMin ≤ a) && decide (dvxMin ≤ b)
  | _ => false

/-- The one-tick property: vz rises by at least `dvzMin` and vx drops by at most `-dvxMin` (raw units). -/
def IncrProp (dvzMin dvxMin : Int) (c : CLOf Fx) : Prop :=
  dvzMin ≤ (Escape.tick c).s.vz.raw - c.s.vz.raw ∧ dvxMin ≤ (Escape.tick c).s.vx.raw - c.s.vx.raw

theorem incrOK_sound (dvzMin dvxMin : Int) (B : CLOf Iv) (c : CLOf Fx) (h : B.Mem c)
    (hok : incrOK dvzMin dvxMin B = true) : IncrProp dvzMin dvxMin c := by
  have hs := tickIncr_sound h
  have hf := tickIncr_fx c
  unfold incrOK at hok
  unfold IncrProp
  split at hok
  · rename_i a a' b b' he
    rw [he] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Iv.mem_box] at hs
    omega
  · simp at hok

theorem region_sound (dvzMin dvxMin : Int) (cons : List LinCon) (dims : List (Nat × Int)) (n : Nat) (B : CLOf Iv)
    (h : checkRec (incrOK dvzMin dvxMin) cons dims n B = true) :
    ∀ c, B.Mem c → (∀ l ∈ cons, l.Holds c) → IncrProp dvzMin dvxMin c :=
  checkRec_sound _ _ cons dims (incrOK_sound dvzMin dvxMin) n B h

end Jsb
