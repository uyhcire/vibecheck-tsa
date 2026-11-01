import Ci.proof.SafeIv
import Ci.proof.LawIvSound
import Jsb.KernelRfl

/-! Soundness of `Ci.Proof.SafeIv.plantOK`: if the interval check passes, every substep of the tick is safe and
climbs. -/

namespace Ci.Proof.SafeIv
open Vibecheck Jsb Ci.Lawfirst
open Ci.Proof.LawIv (In I)

theorem mem_lohi {v : Iv} {x : Fx} (hb : isBox v = true) (hm : v.Mem x) : lo v ≤ x.raw ∧ x.raw ≤ hi v := by
  cases v with
  | top => simp [isBox] at hb
  | box a b => simpa [lo, hi] using hm

theorem in_pr {v : Iv} {x : Fx} (hb : isBox v = true) (hm : v.Mem x) : In x.raw (pr v) := mem_lohi hb hm

/-- The substep's vz update. -/
theorem step_vz (u : InputOf Fx) (s : State) :
    (Jsb.step 7 true u s).vz =
      instScalarFx.add s.vz (instScalarFx.shr (instScalarFx.sub (instScalarFx.mul ⟨196608⟩ s.au) s.au1) 8) := by
  kernel_rfl
theorem step_pvz (u : InputOf Fx) (s : State) : (Jsb.step 7 true u s).pvz = s.vz := by kernel_rfl
theorem step_pvz2 (u : InputOf Fx) (s : State) : (Jsb.step 7 true u s).pvz2 = s.pvz := by kernel_rfl
theorem step_h (u : InputOf Fx) (s : State) :
    (Jsb.step 7 true u s).h = instScalarFx.add s.h (instScalarFx.shr (instScalarFx.ab3 s.vz s.pvz s.pvz2) 7) := by
  kernel_rfl

theorem alphaI_sound {S : StateOf Iv} {s : State} (h : S.Mem s) (bx : isBox S.vx = true) (bz : isBox S.vz = true)
    (bdx : isBox S.dx = true) (bdz : isBox S.dz = true) (ha : alphaI S = true) : Ci.alphaOk s = true := by
  have hu := LawIv.add_in (LawIv.mul_in (in_pr bx h.2.2.1) (in_pr bdx h.2.2.2.2.1))
    (LawIv.mul_in (in_pr bz h.2.2.2.1) (in_pr bdz h.2.2.2.2.2.1))
  have hw := LawIv.sub_in (LawIv.mul_in (in_pr bx h.2.2.1) (in_pr bdz h.2.2.2.2.2.1))
    (LawIv.mul_in (in_pr bz h.2.2.2.1) (in_pr bdx h.2.2.2.2.1))
  unfold alphaI at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  unfold Ci.alphaOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold In at hu hw
  have e : Ci.alphaTanMax = 18845 := rfl
  rw [e] at ha ⊢
  constructor <;> omega

theorem loadI_sound {S : StateOf Iv} {s : State} (h : S.Mem s) (bau : isBox S.au = true) (bah : isBox S.ah = true)
    (bdx : isBox S.dx = true) (bdz : isBox S.dz = true) (hl : loadI S = true) : Ci.loadOk s = true := by
  have hn := LawIv.sub_in (LawIv.mul_in (LawIv.add_in (in_pr bau h.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (LawIv.const_in Ci.gRaw))
      (in_pr bdx h.2.2.2.2.1)) (LawIv.mul_in (in_pr bah h.2.2.2.2.2.2.2.2.2.2.2.2.1) (in_pr bdz h.2.2.2.2.2.1))
  unfold loadI at hl
  simp only [decide_eq_true_eq] at hl
  unfold Ci.loadOk Ci.loadNum
  simp only [decide_eq_true_eq]
  unfold In at hn
  unfold LawIv.const at hn
  omega

theorem speedI_sound {S : StateOf Iv} {s : State} (h : S.Mem s) (bx : isBox S.vx = true) (bz : isBox S.vz = true)
    (hs : speedI S = true) : Ci.speedOk s = true := by
  have h1 := LawIv.sq_in (in_pr bx h.2.2.1)
  have h2 := LawIv.sq_in (in_pr bz h.2.2.2.1)
  unfold speedI at hs
  simp only [decide_eq_true_eq] at hs
  unfold Ci.speedOk
  simp only [decide_eq_true_eq]
  unfold In at h1 h2
  omega

theorem safeI_sound {S : StateOf Iv} {s : State} (h : S.Mem s) (hs : safeI S = true) : Ci.safeOk s = true := by
  unfold safeI at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨bx, bz⟩, bdx⟩, bdz⟩, bau⟩, bah⟩, bst⟩, bh⟩, ha⟩, hl⟩, hsp⟩, st0⟩, st1⟩, hc⟩, hm⟩ := hs
  have hst := mem_lohi bst h.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := mem_lohi bh h.2.1
  unfold Ci.safeOk Ci.envOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨alphaI_sound h bx bz bdx bdz ha, loadI_sound h bau bah bdx bdz hl⟩, speedI_sound h bx bz hsp⟩, ?_⟩, ?_⟩, ?_⟩
  · omega
  · omega
  · omega

theorem ab3_raw (a b c : Fx) : (instScalarFx.ab3 a b c).raw = (23 * a.raw - 16 * b.raw + 5 * c.raw) / 12 := rfl
theorem shr_raw (a : Fx) (k : Nat) : (instScalarFx.shr a k).raw = Jsb.Iv.shrZ a.raw k := rfl

/-- The tracked altitude increment bounds the substep's actual one from below. -/
theorem dh_le {S : StateOf Iv} {s : State} {d1 d2 : I} (h : S.Mem s) (bz : isBox S.vz = true)
    (h1 : In (s.vz.raw - s.pvz.raw) d1) (h2 : In (s.pvz.raw - s.pvz2.raw) d2) (u : InputOf Fx) :
    (dhI S.vz d1 d2).1 ≤ (Jsb.step 7 true u s).h.raw - s.h.raw := by
  have hz := mem_lohi bz h.2.2.2.1
  rw [step_h]
  show _ ≤ (s.h.raw + (instScalarFx.shr (instScalarFx.ab3 s.vz s.pvz s.pvz2) 7).raw) - s.h.raw
  rw [shr_raw, ab3_raw]
  unfold dhI
  unfold In at h1 h2
  have : (12 * lo S.vz + 11 * d1.1 - 5 * d2.2) / 12 ≤ (23 * s.vz.raw - 16 * s.pvz.raw + 5 * s.pvz2.raw) / 12 :=
    Int.ediv_le_ediv (by decide) (by omega)
  have := Jsb.Iv.shrZ_mono 7 this
  omega

theorem dh_ge {S : StateOf Iv} {s : State} {d1 d2 : I} (h : S.Mem s) (bz : isBox S.vz = true)
    (h1 : In (s.vz.raw - s.pvz.raw) d1) (h2 : In (s.pvz.raw - s.pvz2.raw) d2) (u : InputOf Fx) :
    (Jsb.step 7 true u s).h.raw - s.h.raw ≤ (dhI S.vz d1 d2).2 := by
  have hz := mem_lohi bz h.2.2.2.1
  rw [step_h]
  show (s.h.raw + (instScalarFx.shr (instScalarFx.ab3 s.vz s.pvz s.pvz2) 7).raw) - s.h.raw ≤ _
  rw [shr_raw, ab3_raw]
  unfold dhI
  unfold In at h1 h2
  have : (23 * s.vz.raw - 16 * s.pvz.raw + 5 * s.pvz2.raw) / 12 ≤ (12 * hi S.vz + 11 * d1.2 - 5 * d2.1) / 12 :=
    Int.ediv_le_ediv (by decide) (by omega)
  have := Jsb.Iv.shrZ_mono 7 this
  omega

theorem plantOK_sound {U : InputOf Iv} {u : InputOf Fx} (hu : U.Mem u) :
    ∀ (n : Nat) (S : StateOf Iv) (s : State) (d1 d2 hb : I) (ok cl : Bool), S.Mem s →
      In (s.vz.raw - s.pvz.raw) d1 → In (s.pvz.raw - s.pvz2.raw) d2 → In s.h.raw hb →
      plantOK U n S d1 d2 hb = true →
      (Ci.subT u n s ok cl).2 = (ok, cl) ∧ hLoT ≤ (Ci.subT u n s ok cl).1.h.raw ∧
        (Ci.subT u n s ok cl).1.h.raw < hHiT := by
  intro n
  induction n with
  | zero =>
    intro S s d1 d2 hb ok cl _ _ _ hh hp
    simp only [plantOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    unfold In at hh
    exact ⟨rfl, by show hLoT ≤ s.h.raw; omega, by show s.h.raw < hHiT; omega⟩
  | succ n ih =>
    intro S s d1 d2 hb ok cl hS h1 h2 hh hp
    simp only [plantOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨bz, bnd⟩, bnz⟩, bnh⟩, hsafe⟩, hclimb⟩, hrest⟩ := hp
    have hnx : (Jsb.step 7 true U S).Mem (Jsb.step 7 true u s) := Jsb.step_sound 7 true hu hS
    have hsafe' := safeI_sound hnx hsafe
    have hnd1 : (Jsb.Iv.shr (Jsb.Iv.sub (Jsb.Iv.mul (.box 196608 196608) S.au) S.au1) 8).Mem
        (instScalarFx.shr (instScalarFx.sub (instScalarFx.mul ⟨196608⟩ s.au) s.au1) 8) :=
      Jsb.Iv.shr_sound (Jsb.Iv.sub_sound (Jsb.Iv.mul_sound (by simp) hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) 8
    have hd := dh_le hS bz h1 h2 u
    have hd' := dh_ge hS bz h1 h2 u
    have hclimb' : (Ci.climbVz ≤ (Jsb.step 7 true u s).vz.raw && s.h.raw < (Jsb.step 7 true u s).h.raw ||
        Ci.climbTop ≤ (Jsb.step 7 true u s).h.raw) = true := by
      have hvz := mem_lohi bnz hnx.2.2.2.1
      have hh2 := mem_lohi bnh hnx.2.1
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rcases hclimb with ⟨c1, c2⟩ | c3
      · left; constructor <;> omega
      · right; omega
    show (Ci.subT u n (Jsb.step 7 true u s) (ok && Ci.safeOk (Jsb.step 7 true u s))
      (cl && (Ci.climbVz ≤ (Jsb.step 7 true u s).vz.raw && s.h.raw < (Jsb.step 7 true u s).h.raw ||
        Ci.climbTop ≤ (Jsb.step 7 true u s).h.raw))).2 = (ok, cl) ∧
      hLoT ≤ (Ci.subT u n (Jsb.step 7 true u s) (ok && Ci.safeOk (Jsb.step 7 true u s))
      (cl && (Ci.climbVz ≤ (Jsb.step 7 true u s).vz.raw && s.h.raw < (Jsb.step 7 true u s).h.raw ||
        Ci.climbTop ≤ (Jsb.step 7 true u s).h.raw))).1.h.raw ∧
      (Ci.subT u n (Jsb.step 7 true u s) (ok && Ci.safeOk (Jsb.step 7 true u s))
      (cl && (Ci.climbVz ≤ (Jsb.step 7 true u s).vz.raw && s.h.raw < (Jsb.step 7 true u s).h.raw ||
        Ci.climbTop ≤ (Jsb.step 7 true u s).h.raw))).1.h.raw < hHiT
    rw [hsafe', hclimb', Bool.and_true, Bool.and_true]
    apply ih _ _ _ _ _ ok cl hnx _ _ _ hrest
    · have := mem_lohi bnd hnd1
      rw [step_vz, step_pvz]
      show In ((s.vz.raw + _) - s.vz.raw) _
      unfold In; simp only [shr_raw] at this ⊢; constructor <;> omega
    · rw [step_pvz, step_pvz2]; exact h1
    · unfold In at hh ⊢; constructor <;> omega

end Ci.Proof.SafeIv
