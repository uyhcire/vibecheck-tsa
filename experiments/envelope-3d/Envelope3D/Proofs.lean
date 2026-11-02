import Envelope3D.Filter
import Envelope3D.Spec

/-! Proofs: one-tick containment, comparison lemma, monotonicity of the escape check, `never_hit3d`,
passthrough and hand-back, substeps. -/

namespace Envelope3D
variable {ι : Type}

theorem dmul {d a b : Rat} (hd : 0 ≤ d) (h : a ≤ b) : d * a ≤ d * b :=
  Rat.mul_le_mul_of_nonneg_left h hd

/-! ### Tables -/

theorem perf_base (P : Params ι) (V : Rat) :
    P.base.pull ≤ (P.perf V).pull ∧ P.base.climb ≤ (P.perf V).climb := ExpEnvelope.foldl_ge V _ _

theorem perf_mono (P : Params ι) {V V' : Rat} (h : V ≤ V') :
    (P.perf V).pull ≤ (P.perf V').pull ∧ (P.perf V).climb ≤ (P.perf V').climb :=
  ExpEnvelope.foldl_mono h _ _ _ Rat.le_refl Rat.le_refl

theorem latAcc_foldl_mono {φ φ' : Rat} (h : φ ≤ φ') : ∀ (l : List (Rat × Rat)) (a a' : Rat), a ≤ a' →
    l.foldl (fun a r => if φ ≤ r.1 then min a r.2 else a) a ≤
      l.foldl (fun a r => if φ' ≤ r.1 then min a r.2 else a) a'
  | [], _, _, ha => ha
  | r :: l, a, a', ha => by
    simp only [List.foldl_cons]
    apply latAcc_foldl_mono h l
    by_cases h1 : φ' ≤ r.1
    · have h2 : φ ≤ r.1 := Rat.le_trans h h1
      simp only [h1, h2, ite_true]; grind
    · simp only [h1, ite_false]; split <;> grind

theorem latAcc_mono (P : Params ι) {φ φ' : Rat} (h : φ ≤ φ') : P.latAcc φ ≤ P.latAcc φ' :=
  latAcc_foldl_mono h _ _ _ Rat.le_refl

theorem latAcc_foldl_nonneg (φ : Rat) : ∀ (l : List (Rat × Rat)) (a : Rat), (∀ r ∈ l, 0 ≤ r.2) → 0 ≤ a →
    0 ≤ l.foldl (fun a r => if φ ≤ r.1 then min a r.2 else a) a
  | [], _, _, ha => ha
  | r :: l, a, hl, ha => by
    simp only [List.foldl_cons]
    apply latAcc_foldl_nonneg φ l _ (fun r' hr => hl r' (List.mem_cons_of_mem _ hr))
    have := hl r (List.mem_cons_self ..)
    split <;> grind

theorem latAcc_nonneg (P : Params ι) (hP : P.WellFormed) (φ : Rat) : 0 ≤ P.latAcc φ :=
  latAcc_foldl_nonneg φ _ _ hP.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.1

/-! ### Monotonicity of the escape schedule in the commit-state bounds -/

theorem Ref.within_refl (R : Ref) : R.Within R := by
  simp only [Ref.Within]; grind

theorem VFloor_mono (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (h : R'.Within R) :
    VFloor P R ≤ VFloor P R' := by
  obtain ⟨_, h2, h3, _⟩ := h
  have : max 0 R'.vzHi ≤ max 0 R.vzHi := by grind
  have := dmul hP.2.2.2.2.1 this
  simp only [VFloor]; grind

theorem bankCap_mono (P : Params ι) {R R' : Ref} (h : R'.Within R) (j : Nat) :
    bankCap P R' j ≤ bankCap P R j := by
  have := h.2.2.2.1
  simp only [bankCap]; grind

theorem climbOf_mono (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (h : R'.Within R) :
    climbOf P R ≤ climbOf P R' := (perf_mono P (VFloor_mono P hP h)).2

theorem pullAt_mono (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (h : R'.Within R) (k : Nat) :
    pullAt P R k ≤ pullAt P R' k := by
  have hc := bankCap_mono P h k
  have hp := perf_mono P (VFloor_mono P hP h)
  have hb := perf_base P (VFloor P R')
  have hr := hP.2.2.2.2.2.1
  unfold pullAt
  by_cases h1 : bankCap P R k ≤ P.bankLevel
  · have h2 : bankCap P R' k ≤ P.bankLevel := Rat.le_trans hc h1
    simp only [h1, h2, ite_true]; exact hp.1
  · simp only [h1, ite_false]; split <;> grind

theorem schedNext_mono (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (h : R'.Within R) (k : Nat)
    {σ σ' : Sched} (hv : σ.vz ≤ σ'.vz) (hs : σ'.sp ≤ σ.sp) :
    (schedNext P R k σ).vz ≤ (schedNext P R' k σ').vz ∧ (schedNext P R' k σ').sp ≤ (schedNext P R k σ).sp := by
  have hdt := hP.1
  have a := dmul hdt (pullAt_mono P hP h k)
  have b := dmul hdt (latAcc_mono P (bankCap_mono P h k))
  have c := climbOf_mono P hP h
  simp only [schedNext]
  constructor
  · split <;> grind
  · grind

theorem sched_mono (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (h : R'.Within R) :
    ∀ j, (sched P R j).vz ≤ (sched P R' j).vz ∧ (sched P R' j).sp ≤ (sched P R j).sp
  | 0 => by have := h.1; simp only [sched]; grind
  | j + 1 => by
    have ih := sched_mono P hP h j
    exact schedNext_mono P hP h j ih.1 ih.2

theorem schedNext_sp_nonneg (P : Params ι) (hP : P.WellFormed) (R : Ref) (k : Nat) {σ : Sched}
    (h : 0 ≤ σ.sp) : 0 ≤ (schedNext P R k σ).sp := by
  have := Rat.mul_nonneg hP.1 (latAcc_nonneg P hP (bankCap P R k))
  simp only [schedNext]; grind

theorem sched_sp_nonneg (P : Params ι) (hP : P.WellFormed) (R : Ref) :
    ∀ j, 0 ≤ (sched P R j).sp
  | 0 => hP.2.2.2.2.2.2.2.2.1
  | j + 1 => schedNext_sp_nonneg P hP R j (sched_sp_nonneg P hP R j)

theorem scaleLo_mono (P : Params ι) (hP : P.WellFormed) {v v' : Rat} (h : v ≤ v') :
    scaleLo P v ≤ scaleLo P v' := by
  have a := dmul hP.2.2.2.2.2.2.1 h
  have b := dmul (Rat.le_trans hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1) h
  simp only [scaleLo]; grind

theorem scaleHi_mono (P : Params ι) (hP : P.WellFormed) {v v' : Rat} (h : v ≤ v') :
    scaleHi P v ≤ scaleHi P v' := by
  have a := dmul hP.2.2.2.2.2.2.1 h
  have b := dmul (Rat.le_trans hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1) h
  simp only [scaleHi]; grind

theorem scaleLo_le_scaleHi (P : Params ι) (v : Rat) : scaleLo P v ≤ scaleHi P v := by
  simp only [scaleLo, scaleHi]; grind

/-! ### Boxes -/

theorem Box.sub_refl (b : Box) : b.Sub b := by
  simp only [Box.Sub]; grind

theorem contains_iff_sub (b : Box) (s : State) : b.Contains s ↔ (Box.point s).Sub b := Iff.rfl

theorem Box.point_contains (s : State) : (Box.point s).Contains s := Box.sub_refl _

theorem Box.point_nonInv (s : State) : (Box.point s).NonInv := by
  simp only [Box.NonInv, Box.point]; grind

/-- One escape tick of the envelope stays in the worst-case box. -/
theorem escStep_contains (P : Params ι) (hdt : 0 ≤ P.dt) {k : Nat} {ref s s' : State} {u : ι} {b : Box}
    (hb : b.Contains s) (hA : Allowed P (.escape k ref) s u s') :
    (escStep P (Ref.ofState ref) k (sched P (Ref.ofState ref) (k + 1)) b).Contains s' := by
  obtain ⟨⟨_, _, x1, x2, y1, y2, hh⟩, vz, vV, vb, vx1, vx2, vy1, vy2⟩ := hA
  obtain ⟨bx1, bx2, by1, by2, bh, bvx1, bvx2, bvy1, bvy2, bvz, _, _⟩ := hb
  have m1 := dmul hdt (show min b.vxlo (scaleLo P ref.vx - (sched P (Ref.ofState ref) (k + 1)).sp) ≤
    min s.vx s'.vx by grind)
  have m2 := dmul hdt (show max s.vx s'.vx ≤
    max b.vxhi (scaleHi P ref.vx + (sched P (Ref.ofState ref) (k + 1)).sp) by grind)
  have m3 := dmul hdt (show min b.vylo (scaleLo P ref.vy - (sched P (Ref.ofState ref) (k + 1)).sp) ≤
    min s.vy s'.vy by grind)
  have m4 := dmul hdt (show max s.vy s'.vy ≤
    max b.vyhi (scaleHi P ref.vy + (sched P (Ref.ofState ref) (k + 1)).sp) by grind)
  have m5 := dmul hdt (show min b.vzLo (sched P (Ref.ofState ref) (k + 1)).vz ≤ min s.vz s'.vz by grind)
  have e1 : (Ref.ofState ref).vxlo = ref.vx := rfl
  have e2 : (Ref.ofState ref).vxhi = ref.vx := rfl
  have e3 : (Ref.ofState ref).vylo = ref.vy := rfl
  have e4 : (Ref.ofState ref).vyhi = ref.vy := rfl
  simp only [Box.Contains, escStep, e1, e2, e3, e4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- One free tick of the envelope stays in the free box, and its end state is within the commit bounds. -/
theorem free_contains (P : Params ι) (hdt : 0 ≤ P.dt) {s s' : State} {u : ι}
    (hA : Allowed P .free s u s') :
    (freeBox P u s).Contains s' ∧ (Ref.ofState s').Within (freeRef P u s) := by
  obtain ⟨⟨_, _, x1, x2, y1, y2, hh⟩, ax, ay, vz1, vz2, vV, vb⟩ := hA
  simp only [absR] at ax ay vb
  have m1 := dmul hdt (show min s.vx (s.vx - P.dt * (P.free u).hAcc) ≤ min s.vx s'.vx by grind)
  have m2 := dmul hdt (show max s.vx s'.vx ≤ max s.vx (s.vx + P.dt * (P.free u).hAcc) by grind)
  have m3 := dmul hdt (show min s.vy (s.vy - P.dt * (P.free u).hAcc) ≤ min s.vy s'.vy by grind)
  have m4 := dmul hdt (show max s.vy s'.vy ≤ max s.vy (s.vy + P.dt * (P.free u).hAcc) by grind)
  have m5 := dmul hdt (show min s.vz (s.vz - (P.free u).vzDrop) ≤ min s.vz s'.vz by grind)
  simp only [Box.Contains, freeBox, Ref.Within, freeRef, Ref.ofState, absR]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The worst-case escape step is monotone in the box, the commit bounds and the schedule. -/
theorem escStep_sub (P : Params ι) (hP : P.WellFormed) {R R' : Ref} (hR : R'.Within R) (k : Nat)
    {σ σ' : Sched} (hv : σ.vz ≤ σ'.vz) (hs : σ'.sp ≤ σ.sp) {b b' : Box} (hb : b'.Sub b) :
    (escStep P R' k σ' b').Sub (escStep P R k σ b) := by
  have hdt := hP.1
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hR
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, _, _⟩ := hb
  have l1 := scaleLo_mono P hP r5
  have l2 := scaleHi_mono P hP r6
  have l3 := scaleLo_mono P hP r7
  have l4 := scaleHi_mono P hP r8
  have m1 := dmul hdt (show min b.vxlo (scaleLo P R.vxlo - σ.sp) ≤ min b'.vxlo (scaleLo P R'.vxlo - σ'.sp)
    by grind)
  have m2 := dmul hdt (show max b'.vxhi (scaleHi P R'.vxhi + σ'.sp) ≤ max b.vxhi (scaleHi P R.vxhi + σ.sp)
    by grind)
  have m3 := dmul hdt (show min b.vylo (scaleLo P R.vylo - σ.sp) ≤ min b'.vylo (scaleLo P R'.vylo - σ'.sp)
    by grind)
  have m4 := dmul hdt (show max b'.vyhi (scaleHi P R'.vyhi + σ'.sp) ≤ max b.vyhi (scaleHi P R.vyhi + σ.sp)
    by grind)
  have m5 := dmul hdt (show min b.vzLo σ.vz ≤ min b'.vzLo σ'.vz by grind)
  have v := VFloor_mono P hP ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩
  have c := bankCap_mono P ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ (k + 1)
  simp only [Box.Sub, escStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem escStep_nonInv (P : Params ι) (hP : P.WellFormed) {R : Ref} (h1 : R.vxlo ≤ R.vxhi)
    (h2 : R.vylo ≤ R.vyhi) (k : Nat) {σ : Sched} (hs : 0 ≤ σ.sp) {b : Box} (hb : b.NonInv) :
    (escStep P R k σ b).NonInv := by
  have hdt := hP.1
  have hp := hP.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have a1 := scaleLo_le_scaleHi P R.vxlo
  have a2 := scaleHi_mono P hP h1
  have a3 := scaleLo_le_scaleHi P R.vylo
  have a4 := scaleHi_mono P hP h2
  have m1 := dmul hdt (show min b.vxlo (scaleLo P R.vxlo - σ.sp) ≤ max b.vxhi (scaleHi P R.vxhi + σ.sp)
    by grind)
  have m2 := dmul hdt (show min b.vylo (scaleLo P R.vylo - σ.sp) ≤ max b.vyhi (scaleHi P R.vyhi + σ.sp)
    by grind)
  simp only [Box.NonInv, escStep]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ### The computable checks are monotone and sound -/

theorem tickOK_mono (P : Params ι) (hP : P.WellFormed) {b c b' c' : Box} (hb : b'.Sub b) (hc : c'.Sub c)
    (hn : b'.NonInv) (h : tickOK P b c = true) : tickOK P b' c' = true := by
  obtain ⟨b1, b2, b3, b4, b5, _⟩ := hb
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := hc
  obtain ⟨n1, n2, _, _⟩ := hn
  have := P.grid.maxOver_mono hP.2.1 hP.2.2.1
    (xlo := min b.xlo c.xlo) (xhi := max b.xhi c.xhi) (ylo := min b.ylo c.ylo) (yhi := max b.yhi c.yhi)
    (xlo' := min b'.xlo c'.xlo) (xhi' := max b'.xhi c'.xhi) (ylo' := min b'.ylo c'.ylo)
    (yhi' := max b'.yhi c'.yhi) (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
  simp only [tickOK, decide_eq_true_eq] at h ⊢
  grind

theorem climbOutClear_mono (P : Params ι) (hP : P.WellFormed) {b b' : Box} (hb : b'.Sub b)
    (hn : b'.NonInv) (h : climbOutClear P b = true) : climbOutClear P b' = true := by
  obtain ⟨b1, b2, b3, b4, b5, _⟩ := hb
  obtain ⟨n1, n2, _, _⟩ := hn
  have hr := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := P.grid.maxOver_mono hP.2.1 hP.2.2.1
    (xlo := b.xlo - P.climbR) (xhi := b.xhi + P.climbR) (ylo := b.ylo - P.climbR) (yhi := b.yhi + P.climbR)
    (xlo' := b'.xlo - P.climbR) (xhi' := b'.xhi + P.climbR) (ylo' := b'.ylo - P.climbR)
    (yhi' := b'.yhi + P.climbR) (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
  simp only [climbOutClear, decide_eq_true_eq] at h ⊢
  grind

theorem escDone_mono (P : Params ι) (hP : P.WellFormed) {k : Nat} {b b' : Box} (hb : b'.Sub b)
    (hn : b'.NonInv) (h : escDone P k b = true) : escDone P k b' = true := by
  have hc := climbOutClear_mono P hP hb hn
  have := hb.2.2.2.2.2.2.2.2.2.1
  have := hb.2.2.2.2.2.2.2.2.2.2.2
  simp only [escDone, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨h.1.1.1, by grind⟩, by grind⟩, hc h.2⟩

/-- The escape check is monotone: a tighter box, tighter commit bounds and a better schedule pass
whenever the looser ones do. -/
theorem escLoop_mono (P : Params ι) (hP : P.WellFormed) :
    ∀ (n k : Nat) (R R' : Ref) (b b' : Box) (σ σ' : Sched), R'.Within R → R'.vxlo ≤ R'.vxhi →
      R'.vylo ≤ R'.vyhi → b'.Sub b → b'.NonInv → σ.vz ≤ σ'.vz → σ'.sp ≤ σ.sp → 0 ≤ σ'.sp →
      escLoop P R n k b σ = true → escLoop P R' n k b' σ' = true := by
  intro n
  induction n with
  | zero =>
    intro k R R' b b' σ σ' _ _ _ hb hn _ _ _ h
    unfold escLoop at h ⊢
    simp only [Bool.or_false] at h ⊢
    exact escDone_mono P hP hb hn h
  | succ n ih =>
    intro k R R' b b' σ σ' hR hx hy hb hn hv hs hs0 h
    unfold escLoop at h ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (escDone_mono P hP hb hn h)
    · right
      have hσ := schedNext_mono P hP hR k hv hs
      have hsub := escStep_sub P hP hR k hσ.1 hσ.2 hb
      exact ⟨tickOK_mono P hP hb hsub hn h1,
        ih (k + 1) R R' _ _ _ _ hR hx hy hsub
          (escStep_nonInv P hP hx hy k (schedNext_sp_nonneg P hP R' k hs0) hn) hσ.1 hσ.2
          (schedNext_sp_nonneg P hP R' k hs0) h2⟩

/-! ### Comparison lemma -/

/-- Comparison lemma: an escape obeying the envelope stays in the worst-case boxes. -/
theorem comparison (P : Params ι) (hdt : 0 ≤ P.dt) (ref : State) :
    ∀ (j k : Nat) (b : Box) (s : Nat → State) (u : Nat → ι), b.Contains (s 0) →
      (∀ i, Allowed P (.escape (k + i) ref) (s i) (u i) (s (i + 1))) →
      (escIter P (Ref.ofState ref) k b (sched P (Ref.ofState ref) k) j).Contains (s j)
  | 0, _, _, _, _, h0, _ => h0
  | j + 1, k, b, s, u, h0, hA => by
    simp only [escIter]
    have h1 := escStep_contains P hdt h0 (by simpa using hA 0)
    exact comparison P hdt ref j (k + 1) _ (fun i => s (i + 1)) (fun i => u (i + 1)) h1
      (fun i => by have := hA (i + 1); rwa [show k + (i + 1) = k + 1 + i by omega] at this)

/-! ### Tick clearance -/

theorem tickClear_of_box (P : Params ι) (hP : P.WellFormed) {s s' : State} {c : Box}
    (h : tickOK P (Box.point s) c = true) (hc : c.Contains s') : TickClear P s s' := by
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := hc
  simp only [tickOK, Box.point] at h
  replace h := of_decide_eq_true h
  intro x y h1 h2 h3 h4
  have := P.grid.heightAt_le_maxOver hP.2.1 hP.2.2.1
    (xlo := min s.x c.xlo) (xhi := max s.x c.xhi) (ylo := min s.y c.ylo) (yhi := max s.y c.yhi) (x := x) (y := y)
    (by grind) (by grind) (by grind) (by grind)
  grind

/-- The climb-out terminal: everything the climbing turn can reach is clear. -/
def ClimbInv (P : Params ι) (c s : State) : Prop :=
  climbOutClear P (Box.point c) = true ∧ absR (s.x - c.x) ≤ P.climbR ∧ absR (s.y - c.y) ≤ P.climbR ∧
    c.h - P.climbDrop ≤ s.h

theorem climb_tick (P : Params ι) (hP : P.WellFormed) {c s s' : State} {u : ι} (hI : ClimbInv P c s)
    (hA : Allowed P (.climbOut c) s u s') : TickClear P s s' ∧ ClimbInv P c s' := by
  obtain ⟨hc, sx, sy, sh⟩ := hI
  obtain ⟨_, ax, ay, ah, _⟩ := hA
  refine ⟨?_, hc, ax, ay, ah⟩
  simp only [climbOutClear, Box.point] at hc
  replace hc := of_decide_eq_true hc
  simp only [absR] at sx sy ax ay
  intro x y h1 h2 h3 h4
  have := P.grid.heightAt_le_maxOver hP.2.1 hP.2.2.1
    (xlo := c.x - P.climbR) (xhi := c.x + P.climbR) (ylo := c.y - P.climbR) (yhi := c.y + P.climbR) (x := x) (y := y)
    (by grind) (by grind) (by grind) (by grind)
  grind

/-! ### The closed loop -/

def EscInv (P : Params ι) (k : Nat) (ref s : State) : Prop :=
  ∃ n, escLoop P (Ref.ofState ref) n k (Box.point s) (sched P (Ref.ofState ref) k) = true

/-- Loop invariant: the escape the current mode would fly from here is certified, or the climb-out
is clear. -/
def LoopInv (P : Params ι) : Mode → State → Prop
  | .free, s => EscInv P 0 s s
  | .escape k ref, s => EscInv P k ref s
  | .climbOut c, s => ClimbInv P c s

theorem esc_tick (P : Params ι) (hP : P.WellFormed) {k : Nat} {ref s s' : State} {u : ι}
    (hI : EscInv P k ref s) (hA : Allowed P (escMode P k ref s) s u s') :
    TickClear P s s' ∧ LoopInv P (escMode P k ref s).advance s' := by
  unfold escMode at hA ⊢
  by_cases hd : escDone P k (Box.point s) = true
  · simp only [hd, ite_true, Mode.advance] at hA ⊢
    have hc : climbOutClear P (Box.point s) = true := by
      simp only [escDone, Bool.and_eq_true] at hd; exact hd.2
    have hr := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hd' := hP.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h0 : ClimbInv P s s := ⟨hc, by simp only [absR]; grind, by simp only [absR]; grind, by grind⟩
    exact climb_tick P hP h0 hA
  · simp only [hd, Mode.advance] at hA ⊢
    obtain ⟨n, hn⟩ := hI
    cases n with
    | zero => unfold escLoop at hn; simp [hd] at hn
    | succ n =>
      unfold escLoop at hn
      simp only [hd, Bool.false_or, Bool.and_eq_true] at hn
      have hc := escStep_contains P hP.1 (Box.point_contains s) hA
      refine ⟨tickClear_of_box P hP hn.1 hc, n, ?_⟩
      exact escLoop_mono P hP n (k + 1) _ _ _ _ _ _ (Ref.within_refl _) Rat.le_refl Rat.le_refl
        ((contains_iff_sub _ _).1 hc) (Box.point_nonInv _) Rat.le_refl Rat.le_refl
        (sched_sp_nonneg P hP _ (k + 1)) hn.2

theorem free_tick (P : Params ι) (hP : P.WellFormed) {s s' : State} {u : ι}
    (hclear : escapeClear P s u = true) (hA : Allowed P .free s u s') :
    TickClear P s s' ∧ EscInv P 0 s' s' := by
  simp only [escapeClear, escapeOK, Bool.and_eq_true] at hclear
  obtain ⟨hc, hR⟩ := free_contains P hP.1 hA
  have hσ := sched_mono P hP hR 0
  refine ⟨tickClear_of_box P hP hclear.1 hc, P.horizon, ?_⟩
  exact escLoop_mono P hP _ 0 _ _ _ _ _ _ hR Rat.le_refl Rat.le_refl ((contains_iff_sub _ _).1 hc)
    (Box.point_nonInv _) hσ.1 hσ.2 (sched_sp_nonneg P hP _ 0) hclear.2.2

/-- One closed-loop tick preserves the invariant and clears the obstacles. -/
theorem filter_tick (P : Params ι) (hP : P.WellFormed) {m : Mode} {s s' : State} {u : ι}
    (hI : LoopInv P m s) (hA : Allowed P (filter P m s u) s u s') :
    TickClear P s s' ∧ LoopInv P (filter P m s u).advance s' := by
  unfold filter at hA ⊢
  by_cases hclear : escapeClear P s u = true
  · simp only [hclear, ite_true] at hA ⊢
    exact free_tick P hP hclear hA
  · simp only [hclear] at hA ⊢
    cases m with
    | free => exact esc_tick P hP hI hA
    | escape k ref => exact esc_tick P hP hI hA
    | climbOut c => exact climb_tick P hP hI hA

/-- Main theorem: with the filter in the loop, every tick of every envelope-obeying trajectory clears
the obstacles. -/
theorem never_hit3d (P : Params ι) (hP : P.WellFormed) : NeverHits P (filter P) := by
  intro pilot s h0 hA
  have inv : ∀ n, LoopInv P (modeAt (filter P) s pilot n) (s n) := by
    intro n
    induction n with
    | zero => exact ⟨P.horizon, by simp only [Init, escapeOK, Bool.and_eq_true] at h0; exact h0.2⟩
    | succ n ih => exact (filter_tick P hP ih (hA n)).2
  exact fun n => (filter_tick P hP (inv n) (hA n)).1

theorem never_hit3d_tick (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι) (s : Nat → State)
    (h0 : Init P (s 0))
    (hA : ∀ n, Allowed P (appliedAt (filter P) s pilot n) (s n) (pilot n) (s (n + 1))) (n : Nat) :
    P.grid.heightAt (s n).x (s n).y + P.margin < (s n).h := by
  have := never_hit3d P hP pilot s h0 hA n (s n).x (s n).y (by grind) (by grind) (by grind) (by grind)
  have := hP.2.2.2.1
  grind

/-! ### Passthrough and hand-back -/

theorem passthrough (P : Params ι) (m : Mode) (s : State) (u : ι) (h : escapeClear P s u = true) :
    filter P m s u = .free := by
  simp [filter, h]

theorem filter_free (P : Params ι) (s : State) (u : ι) :
    filter P .free s u = (if escapeClear P s u then .free else escMode P 0 s s) := rfl

theorem filter_escape (P : Params ι) (k : Nat) (ref s : State) (u : ι) :
    filter P (.escape k ref) s u = (if escapeClear P s u then .free else escMode P k ref s) := rfl

theorem filter_climbOut (P : Params ι) (c s : State) (u : ι) :
    filter P (.climbOut c) s u = (if escapeClear P s u then .free else .climbOut c) := rfl

/-! ### Substeps -/

theorem substep_clear (P : Params ι) {s s' : State} {subs : List State} (hT : TickClear P s s')
    (hS : substepOK P s s' subs = true) :
    ∀ p ∈ subs, P.grid.heightAt p.x p.y + P.margin < p.h := by
  intro p hp
  simp only [substepOK, List.all_eq_true, decide_eq_true_eq] at hS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
  have := hT p.x p.y h1 h2 h3 h4
  grind

theorem never_hit3d_substeps (P : Params ι) (hP : P.WellFormed) (pilot : Nat → ι) (s : Nat → State)
    (h0 : Init P (s 0))
    (hA : ∀ n, Allowed P (appliedAt (filter P) s pilot n) (s n) (pilot n) (s (n + 1)))
    (subs : Nat → List State) (hS : ∀ n, substepOK P (s n) (s (n + 1)) (subs n) = true) (n : Nat) :
    ∀ p ∈ subs n, P.grid.heightAt p.x p.y + P.margin < p.h :=
  substep_clear P (never_hit3d P hP pilot s h0 hA n) (hS n)

end Envelope3D
