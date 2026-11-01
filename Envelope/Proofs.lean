import Envelope.Filter
import Envelope.Spec

/-! Proofs: comparison lemma, escape-check soundness, `never_hit`, passthrough and hand-back, substeps. -/

namespace Envelope
variable {ι : Type}

/-! ### Performance table -/

theorem addBand_ge (V : Rat) (p : Perf) (b : Band) :
    p.pull ≤ (Params.addBand V p b).pull ∧ p.climb ≤ (Params.addBand V p b).climb := by
  unfold Params.addBand; split <;> grind

theorem addBand_mono {V V' : Rat} {p p' : Perf} (b : Band) (hV : V ≤ V') (hp : p.pull ≤ p'.pull)
    (hc : p.climb ≤ p'.climb) :
    (Params.addBand V p b).pull ≤ (Params.addBand V' p' b).pull ∧
      (Params.addBand V p b).climb ≤ (Params.addBand V' p' b).climb := by
  unfold Params.addBand
  by_cases h1 : b.vLo ≤ V
  · have h2 : b.vLo ≤ V' := Rat.le_trans h1 hV
    simp only [h1, h2, ite_true]; constructor <;> grind
  · simp only [h1, ite_false]; split <;> grind

theorem foldl_ge (V : Rat) : ∀ (l : List Band) (p : Perf),
    p.pull ≤ (l.foldl (Params.addBand V) p).pull ∧ p.climb ≤ (l.foldl (Params.addBand V) p).climb
  | [], p => ⟨Rat.le_refl, Rat.le_refl⟩
  | b :: l, p => by
    have h1 := addBand_ge V p b
    have h2 := foldl_ge V l (Params.addBand V p b)
    simp only [List.foldl_cons]; constructor <;> grind

theorem foldl_mono {V V' : Rat} (hV : V ≤ V') : ∀ (l : List Band) (p p' : Perf),
    p.pull ≤ p'.pull → p.climb ≤ p'.climb →
    (l.foldl (Params.addBand V) p).pull ≤ (l.foldl (Params.addBand V') p').pull ∧
      (l.foldl (Params.addBand V) p).climb ≤ (l.foldl (Params.addBand V') p').climb
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | b :: l, p, p', h1, h2 => by
    have := addBand_mono b hV h1 h2
    exact foldl_mono hV l _ _ this.1 this.2

theorem perf_base (P : Params ι) (V : Rat) :
    P.base.pull ≤ (P.perf V).pull ∧ P.base.climb ≤ (P.perf V).climb := foldl_ge V _ _

theorem perf_mono (P : Params ι) {V V' : Rat} (h : V ≤ V') :
    (P.perf V).pull ≤ (P.perf V').pull ∧ (P.perf V).climb ≤ (P.perf V').climb :=
  foldl_mono h _ _ _ Rat.le_refl Rat.le_refl

/-! ### Monotonicity of the one-tick floors -/

theorem vzEsc_mono (P : Params ι) (hdt : 0 ≤ P.dt) (k : Nat) {vz vz' V V' : Rat} (h1 : vz ≤ vz')
    (h2 : V ≤ V') : vzEsc P k vz V ≤ vzEsc P k vz' V' := by
  unfold vzEsc
  split
  · grind
  · have hp := perf_mono P h2
    have := Rat.mul_le_mul_of_nonneg_right hp.1 hdt
    grind

theorem vzFloor_mono (P : Params ι) (hdt : 0 ≤ P.dt) (m : Mode) (u : ι) {vz vz' V V' : Rat}
    (h1 : vz ≤ vz') (h2 : V ≤ V') : vzFloor P m u vz V ≤ vzFloor P m u vz' V' := by
  cases m with
  | free => simp only [vzFloor]; grind
  | escape k => exact vzEsc_mono P hdt k h1 h2

theorem VFloor_mono (P : Params ι) (m : Mode) (u : ι) {V V' : Rat} (h : V ≤ V') :
    VFloor P m u V ≤ VFloor P m u V' := by
  cases m <;> simp only [VFloor, VEsc] <;> grind

/-! ### Boxes -/

theorem Box.sub_refl (b : Box) : b.Sub b :=
  ⟨Rat.le_refl, Rat.le_refl, Rat.le_refl, Rat.le_refl, Rat.le_refl⟩

theorem contains_iff_sub (b : Box) (s : State) : b.Contains s ↔ (Box.point s).Sub b := Iff.rfl

theorem Box.point_contains (s : State) : (Box.point s).Contains s := Box.sub_refl _

theorem esc_eq_next (P : Params ι) (k : Nat) (u : ι) (b : Box) :
    b.esc P k = b.next P (.escape k) u := rfl

/-- One tick of the envelope stays in the worst-case box. -/
theorem next_contains (P : Params ι) (hdt : 0 ≤ P.dt) {m : Mode} {s s' : State} {u : ι} {b : Box}
    (hb : b.Contains s) (hA : Allowed P m s u s') : (b.next P m u).Contains s' := by
  obtain ⟨hx1, hx2, hh, hvz, hV⟩ := hb
  obtain ⟨_, _, ax1, ax2, ah, avz, aV⟩ := hA
  have f1 := vzFloor_mono P hdt m u hvz hV
  have f2 := VFloor_mono P m u hV
  have hmin : min b.vzLo (vzFloor P m u b.vzLo b.VLo) ≤ min s.vz s'.vz := by grind
  have := Rat.mul_le_mul_of_nonneg_left hmin hdt
  simp only [Box.Contains, Box.next, Box.adv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem adv_sub (P : Params ι) (hdt : 0 ≤ P.dt) {b c : Box} {vb vc Vb Vc : Rat} (h : b.Sub c)
    (hv : vc ≤ vb) (hV : Vc ≤ Vb) : (b.adv P vb Vb).Sub (c.adv P vc Vc) := by
  obtain ⟨hx1, hx2, hh, hvz, _⟩ := h
  have hmin : min c.vzLo vc ≤ min b.vzLo vb := by grind
  have := Rat.mul_le_mul_of_nonneg_left hmin hdt
  simp only [Box.Sub, Box.adv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The worst-case escape step is monotone in the box. -/
theorem esc_sub (P : Params ι) (hdt : 0 ≤ P.dt) (k : Nat) {b c : Box} (h : b.Sub c) :
    (b.esc P k).Sub (c.esc P k) :=
  adv_sub P hdt h (vzEsc_mono P hdt k h.2.2.2.1 h.2.2.2.2) (by simp only [VEsc]; have := h.2.2.2.2; grind)

theorem escIter_sub (P : Params ι) (hdt : 0 ≤ P.dt) :
    ∀ (j k : Nat) (b c : Box), b.Sub c → (escIter P k b j).Sub (escIter P k c j)
  | 0, _, _, _, h => h
  | j + 1, k, b, c, h => by
    simp only [escIter]
    exact escIter_sub P hdt j (k + 1) _ _ (esc_sub P hdt k h)

/-! ### Comparison lemma -/

/-- Comparison lemma: an escape obeying the envelope stays in the worst-case boxes. -/
theorem comparison (P : Params ι) (hdt : 0 ≤ P.dt) :
    ∀ (j k : Nat) (b : Box) (s : Nat → State) (u : Nat → ι), b.Contains (s 0) →
      (∀ i, Allowed P (.escape (k + i)) (s i) (u i) (s (i + 1))) →
      (escIter P k b j).Contains (s j)
  | 0, _, _, _, _, h0, _ => h0
  | j + 1, k, b, s, u, h0, hA => by
    simp only [escIter]
    have h1 : (b.esc P k).Contains (s 1) := by
      rw [esc_eq_next P k (u 0)]; exact next_contains P hdt h0 (by simpa using hA 0)
    exact comparison P hdt j (k + 1) _ (fun i => s (i + 1)) (fun i => u (i + 1)) h1
      (fun i => by have := hA (i + 1); rwa [show k + (i + 1) = k + 1 + i by omega] at this)

theorem comparison_altitude (P : Params ι) (hdt : 0 ≤ P.dt) (k : Nat) (s : Nat → State)
    (u : Nat → ι) (hA : ∀ i, Allowed P (.escape (k + i)) (s i) (u i) (s (i + 1))) (j : Nat) :
    (escIter P k (Box.point (s 0)) j).hLo ≤ (s j).h :=
  (comparison P hdt j k _ s u (Box.point_contains _) hA).2.2.1

/-! ### Tick clearance and the escape check -/

theorem boxTickClear_anti (P : Params ι) {b c b' c' : Box} (h : BoxTickClear P b c)
    (hb : b'.Sub b) (hc : c'.Sub c) : BoxTickClear P b' c' := by
  obtain ⟨b1, b2, b3, _, _⟩ := hb
  obtain ⟨c1, c2, c3, _, _⟩ := hc
  intro x h1 h2
  have := h x (by grind) (by grind)
  grind

theorem safeFrom_anti (P : Params ι) (hdt : 0 ≤ P.dt) {k : Nat} {b c : Box}
    (h : SafeFrom P k c) (hb : b.Sub c) : SafeFrom P k b := fun j =>
  boxTickClear_anti P (h j) (escIter_sub P hdt j k _ _ hb) (escIter_sub P hdt (j + 1) k _ _ hb)

theorem safeFrom_tail (P : Params ι) {k : Nat} {b : Box} (h : SafeFrom P k b) :
    SafeFrom P (k + 1) (b.esc P k) := fun j => h (j + 1)

theorem tickOK_sound (P : Params ι) (hw : 0 < P.terrain.w) {b c : Box} (h : tickOK P b c = true) :
    BoxTickClear P b c := by
  intro x h1 h2
  have := P.terrain.heightAt_le_maxOver hw h1 h2
  simp only [tickOK, decide_eq_true_eq] at h
  grind

/-- Semantic form of `escDone`: past the delay, climbing, and above all terrain from `b.xlo` on. -/
def DoneInv (P : Params ι) (k : Nat) (b : Box) : Prop :=
  P.delayTicks ≤ k ∧ P.base.climb ≤ b.vzLo ∧
    ∀ x, b.xlo ≤ x → P.terrain.heightAt x + P.margin < b.hLo - P.sag

theorem escDone_inv (P : Params ι) (hw : 0 < P.terrain.w) {k : Nat} {b : Box}
    (h : escDone P k b = true) : DoneInv P k b := by
  simp only [escDone, decide_eq_true_eq] at h
  obtain ⟨hk, hvz, hh⟩ := h
  refine ⟨hk, hvz, fun x hx => ?_⟩
  have := P.terrain.heightAt_le_maxAhead hw hx
  grind

/-- Once done, the escape stays done (it climbs and only moves forward) and its next tick is clear. -/
theorem doneInv_step (P : Params ι) (hP : P.WellFormed) {k : Nat} {b : Box} (h : DoneInv P k b) :
    DoneInv P (k + 1) (b.esc P k) ∧ BoxTickClear P b (b.esc P k) := by
  obtain ⟨hdt, _, _, hpull, hslack, hvx⟩ := hP
  obtain ⟨hk, hvz, hh⟩ := h
  have hp := perf_base P b.VLo
  have hv' : P.base.climb ≤ vzEsc P k b.vzLo b.VLo := by
    unfold vzEsc
    simp only [show ¬ k < P.delayTicks by omega, ↓reduceIte]
    have : 0 ≤ (P.perf b.VLo).pull * P.dt := Rat.mul_nonneg (by grind) hdt
    grind
  have hmin : P.base.climb ≤ min b.vzLo (vzEsc P k b.vzLo b.VLo) := by grind
  have := Rat.mul_le_mul_of_nonneg_left hmin hdt
  have hrise : b.hLo ≤ (b.esc P k).hLo := by simp only [Box.esc, Box.adv]; grind
  have hfwd : b.xlo ≤ (b.esc P k).xlo := by
    have : 0 ≤ P.dt * P.vxMin := Rat.mul_nonneg hdt hvx
    simp only [Box.esc, Box.adv]; grind
  refine ⟨⟨by omega, hv', fun x hx => ?_⟩, fun x hx _ => ?_⟩
  · have := hh x (Rat.le_trans hfwd hx)
    grind
  · have := hh x (by grind)
    grind

theorem doneInv_safe (P : Params ι) (hP : P.WellFormed) :
    ∀ (j k : Nat) (b : Box), DoneInv P k b →
      BoxTickClear P (escIter P k b j) (escIter P k b (j + 1))
  | 0, _, _, h => (doneInv_step P hP h).2
  | j + 1, k, _, h => doneInv_safe P hP j (k + 1) _ (doneInv_step P hP h).1

theorem escLoop_sound (P : Params ι) (hP : P.WellFormed) :
    ∀ (n k : Nat) (b : Box), escLoop P n k b = true → SafeFrom P k b := by
  intro n
  induction n with
  | zero =>
    intro k b h
    unfold escLoop at h
    simp only [Bool.or_false] at h
    exact fun j => doneInv_safe P hP j k b (escDone_inv P hP.2.1 h)
  | succ n ih =>
    intro k b h
    unfold escLoop at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact fun j => doneInv_safe P hP j k b (escDone_inv P hP.2.1 h)
    · have hs := ih (k + 1) _ h2
      intro j
      cases j with
      | zero => exact tickOK_sound P hP.2.1 h1
      | succ j => exact hs j

theorem escapeOK_sound (P : Params ι) (hP : P.WellFormed) {b : Box} (h : escapeOK P b = true) :
    SafeFrom P 0 b := by
  simp only [escapeOK, Bool.and_eq_true] at h
  exact escLoop_sound P hP _ _ _ h.2

/-! ### The closed loop -/

theorem tickClear_of_box (P : Params ι) {s s' : State} {c : Box}
    (h : BoxTickClear P (Box.point s) c) (hc : c.Contains s') : TickClear P s s' := by
  have h' : BoxTickClear P (Box.point s) (Box.point s') := boxTickClear_anti P h (Box.sub_refl _) hc
  exact h'

/-- Loop invariant: the escape that the current mode would fly from here is clear. -/
def LoopInv (P : Params ι) (m : Mode) (s : State) : Prop := SafeFrom P m.phase (Box.point s)

/-- An escape tick preserves the invariant and clears terrain. -/
theorem escape_tick (P : Params ι) (hP : P.WellFormed) {k : Nat} {s s' : State} {u : ι}
    (hI : SafeFrom P k (Box.point s)) (hA : Allowed P (.escape k) s u s') :
    TickClear P s s' ∧ SafeFrom P (k + 1) (Box.point s') := by
  have hc : ((Box.point s).esc P k).Contains s' := by
    rw [esc_eq_next P k u]; exact next_contains P hP.1 (Box.point_contains _) hA
  exact ⟨tickClear_of_box P (hI 0) hc, safeFrom_anti P hP.1 (safeFrom_tail P hI) hc⟩

/-- A free tick certified by `escapeClear` is clear and leaves an escape from phase 0 clear. -/
theorem free_tick (P : Params ι) (hP : P.WellFormed) {s s' : State} {u : ι}
    (hclear : escapeClear P s u = true) (hA : Allowed P .free s u s') :
    TickClear P s s' ∧ SafeFrom P 0 (Box.point s') := by
  simp only [escapeClear, Bool.and_eq_true] at hclear
  have hc := next_contains P hP.1 (Box.point_contains _) hA
  exact ⟨tickClear_of_box P (tickOK_sound P hP.2.1 hclear.1) hc,
    safeFrom_anti P hP.1 (escapeOK_sound P hP hclear.2) hc⟩

/-- One closed-loop tick preserves the invariant and clears terrain. -/
theorem filter_tick (P : Params ι) (hP : P.WellFormed) {m : Mode} {s s' : State} {u : ι}
    (hI : LoopInv P m s) (hA : Allowed P (filter P m s u) s u s') :
    TickClear P s s' ∧ LoopInv P (filter P m s u).advance s' := by
  unfold filter at hA ⊢
  by_cases hclear : escapeClear P s u = true
  · simp only [hclear, ite_true] at hA ⊢
    exact free_tick P hP hclear hA
  · simp only [hclear] at hA ⊢
    cases m with
    | escape k => exact escape_tick P hP hI hA
    | free => exact escape_tick P hP hI hA

/-- Main theorem: with the filter in the loop, envelope-obeying trajectories clear terrain on every tick. -/
theorem never_hit (P : Params ι) (hP : P.WellFormed) : NeverHits P (filter P) := by
  intro pilot s h0 hA
  have inv : ∀ n, LoopInv P (modeAt (filter P) s pilot n) (s n) := by
    intro n
    induction n with
    | zero => exact escapeOK_sound P hP h0
    | succ n ih => exact (filter_tick P hP ih (hA n)).2
  exact fun n => (filter_tick P hP (inv n) (hA n)).1

/-- At every tick the aircraft is above terrain + margin. -/
theorem never_hit_tick (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι) (s : Nat → State)
    (h0 : Init P (s 0))
    (hA : ∀ n, Allowed P (appliedAt (filter P) s pilot n) (s n) (pilot n) (s (n + 1))) (n : Nat) :
    P.terrain.heightAt (s n).x + P.margin < (s n).h := by
  have := never_hit P hP pilot s h0 hA n (s n).x (by grind) (by grind)
  have := hP.2.2.1
  grind

/-! ### Passthrough and hand-back -/

/-- The pilot's input is applied whenever its worst case keeps the escape clear, in either mode
(from an escape, this hands control back). -/
theorem passthrough (P : Params ι) (m : Mode) (s : State) (u : ι) (h : escapeClear P s u = true) :
    filter P m s u = .free := by
  simp [filter, h]

/-- In free flight the filter overrides exactly when the pilot's worst case loses the escape. -/
theorem filter_free (P : Params ι) (s : State) (u : ι) :
    filter P .free s u = (if escapeClear P s u then .free else .escape 0) := rfl

/-- A committed escape is kept until the pilot's input is certified again. -/
theorem filter_escape (P : Params ι) (k : Nat) (s : State) (u : ι) :
    filter P (.escape k) s u = (if escapeClear P s u then .free else .escape k) := rfl

/-! ### Substeps -/

/-- For a plant that moves in substeps: if the tick is clear and every substep passes `substepOK`,
every substep is above terrain + margin. -/
theorem substep_clear (P : Params ι) {s s' : State} {subs : List State} (hT : TickClear P s s')
    (hS : substepOK P s s' subs = true) :
    ∀ p ∈ subs, P.terrain.heightAt p.x + P.margin < p.h := by
  intro p hp
  simp only [substepOK, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨h1, h2, h3⟩ := hS p hp
  have := hT p.x h1 h2
  grind

/-- With the filter in the loop, every substep that passes `substepOK` is above terrain + margin. -/
theorem never_hit_substeps (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι) (s : Nat → State)
    (h0 : Init P (s 0))
    (hA : ∀ n, Allowed P (appliedAt (filter P) s pilot n) (s n) (pilot n) (s (n + 1)))
    (subs : Nat → List State) (hS : ∀ n, substepOK P (s n) (s (n + 1)) (subs n) = true) (n : Nat) :
    ∀ p ∈ subs n, P.terrain.heightAt p.x + P.margin < p.h :=
  substep_clear P (never_hit P hP pilot s h0 hA n) (hS n)
