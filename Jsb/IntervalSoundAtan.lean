import Jsb.IntervalSoundBase

/-! Soundness of the interval `atan2`. -/

namespace Jsb
open Vibecheck

namespace Iv
variable {x y : Fx} {I J : Iv}

theorem atanStep_none (L H : Int) (cs : List Int) : cs.foldl (atanStep L H) none = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.foldl, atanStep, ih]

theorem mulShr30_sound {a b c d u v x y : Int} (h : mulShr30 a b c d = some (u, v)) (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) : InI64 (x * y) ∧ u ≤ x * y / 1073741824 ∧ x * y / 1073741824 ≤ v ∧
      -B62 < (prods a b c d).1 ∧ (prods a b c d).2 < B62 := by
  have hc := corners hx hy
  simp only [mulShr30] at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Int.shiftRight_eq_div_pow]
    unfold B62 at hb
    refine ⟨⟨by omega, by omega⟩, Int.ediv_le_ediv (by decide) hc.1, Int.ediv_le_ediv (by decide) hc.2, hb.1, hb.2⟩
  · simp at h

theorem atan_fold (t2 : Int64) (L H : Int) (ht2 : L ≤ t2.toInt ∧ t2.toInt ≤ H) :
    ∀ (cs : List Int) (acc : Int64) (a b : Int) (r : Int × Int), a ≤ acc.toInt ∧ acc.toInt ≤ b →
      cs.foldl (atanStep L H) (some (a, b)) = some r →
      r.1 ≤ (cs.foldl (fun acc c => Int64.ofInt c + ((acc * t2) >>> (30 : Int64))) acc).toInt ∧
      (cs.foldl (fun acc c => Int64.ofInt c + ((acc * t2) >>> (30 : Int64))) acc).toInt ≤ r.2 := by
  intro cs
  induction cs with
  | nil =>
    intro acc a b r hacc h
    simp only [List.foldl, Option.some.injEq] at h; subst h; exact hacc
  | cons c cs ih =>
    intro acc a b r hacc h
    simp only [List.foldl] at h ⊢
    cases hm : mulShr30 a b L H with
    | none => simp [atanStep, hm, atanStep_none] at h
    | some pq =>
      obtain ⟨p, q⟩ := pq
      have hs := mulShr30_sound hm hacc ht2
      simp only [atanStep, hm] at h
      split at h
      · rename_i hcb
        apply ih _ (c + p) (c + q) r _ h
        have e1 : (acc * t2).toInt = acc.toInt * t2.toInt := by rw [Int64.toInt_mul, bmod64_of hs.1]
        have h1 := hs.1
        unfold B62 at hcb
        unfold InI64 at h1
        have hc64 : InI64 c := by constructor <;> omega
        rw [Int64.toInt_add, toInt_ofInt_of hc64, toInt_shr30, e1, bmod64_of ⟨by omega, by omega⟩]
        omega
      · rw [atanStep_none] at h; simp at h

theorem mul_self_nonneg (t : Int) : 0 ≤ t * t := by
  by_cases h : 0 ≤ t
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (show 0 ≤ -t by omega) (show 0 ≤ -t by omega); rwa [Int.neg_mul_neg] at this

theorem sq_bounds {lo hi t : Int} (h : lo ≤ t ∧ t ≤ hi) :
    (if 0 ≤ lo then (lo * lo, hi * hi) else if hi ≤ 0 then (hi * hi, lo * lo) else (0, Max.max (lo * lo) (hi * hi))).1
      ≤ t * t ∧ t * t ≤
    (if 0 ≤ lo then (lo * lo, hi * hi) else if hi ≤ 0 then (hi * hi, lo * lo) else (0, Max.max (lo * lo) (hi * hi))).2 := by
  split
  · exact ⟨Int.mul_self_le_mul_self (by omega) h.1, Int.mul_self_le_mul_self (by omega) h.2⟩
  · split
    · have a := Int.mul_self_le_mul_self (show 0 ≤ -hi by omega) (show -hi ≤ -t by omega)
      have b := Int.mul_self_le_mul_self (show 0 ≤ -t by omega) (show -t ≤ -lo by omega)
      simp only [Int.neg_mul_neg] at a b; exact ⟨a, b⟩
    · refine ⟨mul_self_nonneg t, ?_⟩
      by_cases ht : 0 ≤ t
      · have := Int.mul_self_le_mul_self ht h.2; simp only; omega
      · have b := Int.mul_self_le_mul_self (show 0 ≤ -t by omega) (show -t ≤ -lo by omega)
        simp only [Int.neg_mul_neg] at b; simp only; omega

theorem atanS30I_sound {lo hi t p q : Int} (h : atanS30I lo hi = some (p, q)) (ht : lo ≤ t ∧ t ≤ hi) :
    p ≤ atanS30 t ∧ atanS30 t ≤ q := by
  unfold atanS30I at h
  split at h
  · rename_i hr
    have ht64 : InI64 t := ⟨by omega, by omega⟩
    have e := toInt_ofInt_of ht64
    have sb := sq_bounds ht
    have tt : InI64 (t * t) := by
      have h0 := mul_self_nonneg t
      have h1 : t * t ≤ 2147483648 * 2147483648 := by
        by_cases h : 0 ≤ t
        · exact Int.mul_self_le_mul_self h (by omega)
        · have := Int.mul_self_le_mul_self (show 0 ≤ -t by omega) (show -t ≤ 2147483648 by omega)
          rwa [Int.neg_mul_neg] at this
      constructor <;> omega
    have et2 : ((Int64.ofInt t * Int64.ofInt t) >>> (30 : Int64)).toInt = t * t / 1073741824 := by
      rw [toInt_shr30, Int64.toInt_mul, e, bmod64_of tt]
    have c30 : ((2 ^ 30 : Nat) : Int) = 1073741824 := rfl
    simp only [Int.shiftRight_eq_div_pow, c30] at h
    split at h
    · rename_i p' q' hf
      have hfold := atan_fold ((Int64.ofInt t * Int64.ofInt t) >>> (30 : Int64)) _ _
        ⟨by rw [et2]; exact Int.ediv_le_ediv (by decide) sb.1, by rw [et2]; exact Int.ediv_le_ediv (by decide) sb.2⟩
        atanCoef 3077586 3077586 3077586 (p', q') (by decide) hf
      have hm := mulShr30_sound h ht hfold
      unfold atanS30
      simp only
      rw [toInt_shr30, Int64.toInt_mul, e, bmod64_of hm.1]
      exact ⟨hm.2.1, hm.2.2.1⟩
    · simp at h
  · simp at h

theorem atan2_sound (hy : I.Mem y) (hx : J.Mem x) : (atan2 I J).Mem (instScalarFx.atan2 y x) := by
  cases I <;> cases J <;> simp only [atan2] <;> try trivial
  rename_i yl yh xl xh
  simp only [mem_box] at hy hx
  split
  · rename_i hc
    split
    · rename_i p q hI
      have hxpos : 0 < x.raw := by omega
      have eax : (x.raw.natAbs : Int) = x.raw := Int.natAbs_of_nonneg (by omega)
      have hay : (y.raw.natAbs : Int) ≤ x.raw.natAbs := by omega
      have hnum : (y.raw.natAbs : Int) * 1073741824 ≤ 4611686018427387904 := by omega
      have fd : floorDiv ((y.raw.natAbs : Int) * 1073741824) (x.raw.natAbs : Int)
          = (y.raw.natAbs : Int) * 1073741824 / x.raw := by
        rw [floorDiv_eq _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega), eax]
      have tlo : (if yl ≤ 0 ∧ 0 ≤ yh then (0 : Int) else Min.min (yl.natAbs : Int) yh.natAbs) * 1073741824 / xh
          ≤ (y.raw.natAbs : Int) * 1073741824 / x.raw := by
        apply Int.le_trans (Int.ediv_le_ediv (by omega) (show _ ≤ (y.raw.natAbs : Int) * 1073741824 by split <;> omega))
        exact ediv_anti_pos (by omega) hxpos hx.2
      have thi : (y.raw.natAbs : Int) * 1073741824 / x.raw ≤ Max.max (-yl) yh * 1073741824 / xl := by
        apply Int.le_trans (Int.ediv_le_ediv hxpos (show _ ≤ Max.max (-yl) yh * 1073741824 by omega))
        exact ediv_anti_pos (by omega) (by omega) hx.1
      have ha := atanS30I_sound hI ⟨tlo, thi⟩
      have m1 := Int.ediv_le_ediv (show (0 : Int) < 16384 by decide) ha.1
      have m2 := Int.ediv_le_ediv (show (0 : Int) < 16384 by decide) ha.2
      have key : (atan2Fx y x).raw = if y.raw < 0 then
          -(atanS30 ((y.raw.natAbs : Int) * 1073741824 / x.raw) / 16384)
          else atanS30 ((y.raw.natAbs : Int) * 1073741824 / x.raw) / 16384 := by
        unfold atan2Fx
        have nz : (y.raw.natAbs == 0 && x.raw.natAbs == 0) = false := by simp; omega
        have nb : ¬ (y.raw.natAbs > x.raw.natAbs) := by omega
        have nx : ¬ (x.raw < 0) := by omega
        simp only [nz, nb, nx, Bool.false_eq_true, ite_false, fd]

      show (if 0 ≤ yl then box (p / 16384) (q / 16384) else if yh < 0 then box (-(q / 16384)) (-(p / 16384))
        else box (Min.min (p / 16384) (-(q / 16384))) (Max.max (q / 16384) (-(p / 16384)))).Mem (atan2Fx y x)
      split <;> (try split) <;> simp only [mem_box, key] <;> split <;> omega
    · trivial
  · trivial

end Iv
end Jsb
