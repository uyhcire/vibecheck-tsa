import ExpProofs.CiProof.PsdForm
import Ci.Goals

/-! Generic reduction of `Ci.Goals.TInvariant L` to pointwise obligations, for a terminal set that is a Lyapunov
sublevel set intersected with side conditions.

The terminal set `L.inT` is related to real data by two bridge hypotheses (`hin`, `hout`) that allow the integer
implementation to round: inside T the form is at most `rIn²`, and anything with form at most `rOut²` (and the side
conditions) is in T. The model obligations are, for every `(s, m)` in T:

* `hsafe`: the tick is safe and climbs;
* `hside`: the tick's image satisfies the side conditions;
* `henc`: the tick's image coordinates are `A z + e` for some matrix `A` with a contraction certificate
  `ρ² P − Aᵀ P' A ⪰ 0` (P at the state, P' at the image) and a remainder `e` with `eᵀ P' e ≤ ε²`,
  where `ρ rIn + ε ≤ rOut`. -/

namespace ExpProofs.CiProof
open Ci Ci.Goals Matrix

variable {n : Type} [Fintype n]

theorem tInvariant_of_lyap (L : Ci.Law) (side : ExpJsb.State × L.σ → Prop) (z : ExpJsb.State × L.σ → (n → ℝ))
    (P : ExpJsb.State × L.σ → Matrix n n ℝ) (rIn rOut : ℝ) (hr : 0 ≤ rIn)
    (hPsd : ∀ p, (P p).PosSemidef ∧ (P p)ᵀ = P p)
    (hin : ∀ p, L.inT p = true → side p ∧ qf (P p) (z p) ≤ rIn ^ 2)
    (hout : ∀ p, side p → qf (P p) (z p) ≤ rOut ^ 2 → L.inT p = true)
    (hsafe : ∀ s m, L.inT (s, m) = true → (tickT L s m).safe = true ∧ (tickT L s m).climb = true)
    (hside : ∀ s m, L.inT (s, m) = true → side ((tickT L s m).s, (tickT L s m).m))
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix n n ℝ) (e : n → ℝ) (ρ ε : ℝ),
      z ((tickT L s m).s, (tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((tickT L s m).s, (tickT L s m).m)) e ≤ ε ^ 2 ∧ ρ * rIn + ε ≤ rOut) :
    TInvariant L := by
  intro s m hT
  refine ⟨(hsafe s m hT).1, (hsafe s m hT).2, ?_⟩
  obtain ⟨A, e, ρ, ε, hz, hc, hρ, hε, he, hm⟩ := henc s m hT
  have hzin := (hin (s, m) hT).2
  have hq : qf (P ((tickT L s m).s, (tickT L s m).m)) (A *ᵥ z (s, m) + e) ≤ rOut ^ 2 := by
    have hz' : qf (P (s, m)) (z (s, m)) ≤ rIn ^ 2 := hzin
    -- contract with radius rIn, then enlarge to rOut
    have key : Real.sqrt (qf (P ((tickT L s m).s, (tickT L s m).m)) (A *ᵥ z (s, m) + e)) ≤ rOut := by
      have hP' := hPsd ((tickT L s m).s, (tickT L s m).m)
      have hA : qf (P ((tickT L s m).s, (tickT L s m).m)) (A *ᵥ z (s, m)) ≤ (ρ * rIn) ^ 2 := by
        have h1 := qf_nonneg hc (z (s, m))
        have h2 : qf (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A) (z (s, m)) =
            ρ ^ 2 * qf (P (s, m)) (z (s, m)) - qf (Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A) (z (s, m)) := by
          unfold qf; rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        rw [qf_mulVec]
        nlinarith [h1, h2, hz', sq_nonneg ρ]
      have hsA := Real.sqrt_le_iff.mpr ⟨by positivity, hA⟩
      have hse := Real.sqrt_le_iff.mpr ⟨hε, he⟩
      have ht := sqrt_qf_add_le hP'.1 hP'.2 (A *ᵥ z (s, m)) e
      linarith
    have h0 := qf_nonneg (hPsd ((tickT L s m).s, (tickT L s m).m)).1 (A *ᵥ z (s, m) + e)
    calc _ = Real.sqrt (qf (P ((tickT L s m).s, (tickT L s m).m)) (A *ᵥ z (s, m) + e)) ^ 2 :=
          (Real.sq_sqrt h0).symm
      _ ≤ rOut ^ 2 := by gcongr
  exact hout _ (hside s m hT) (hz ▸ hq)

/-- The invariance half alone, with radii that may depend on the state (the integer set may round, and its radius
may vary with altitude): if T's members satisfy the form bound `rIn`, the side conditions are preserved, and the
tick is a contraction `A z + e` in the form with `ρ rIn + ε ≤ rOut` at the image, the image is in T. -/
theorem inT_next_of_lyap (L : Ci.Law) (side : ExpJsb.State × L.σ → Prop) (z : ExpJsb.State × L.σ → (n → ℝ))
    (P : ExpJsb.State × L.σ → Matrix n n ℝ) (rIn rOut : ExpJsb.State × L.σ → ℝ) (hr : ∀ p, 0 ≤ rIn p)
    (hPsd : ∀ p, (P p).PosSemidef ∧ (P p)ᵀ = P p)
    (hin : ∀ p, L.inT p = true → side p ∧ qf (P p) (z p) ≤ rIn p ^ 2)
    (hout : ∀ p, side p → qf (P p) (z p) ≤ rOut p ^ 2 → L.inT p = true)
    (hside : ∀ s m, L.inT (s, m) = true → side ((tickT L s m).s, (tickT L s m).m))
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix n n ℝ) (e : n → ℝ) (ρ ε : ℝ),
      z ((tickT L s m).s, (tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((tickT L s m).s, (tickT L s m).m)) e ≤ ε ^ 2 ∧
      ρ * rIn (s, m) + ε ≤ rOut ((tickT L s m).s, (tickT L s m).m)) :
    ∀ s m, L.inT (s, m) = true → L.inT ((tickT L s m).s, (tickT L s m).m) = true := by
  intro s m hT
  obtain ⟨A, e, ρ, ε, hz, hc, hρ, hε, he, hm⟩ := henc s m hT
  have hzin := (hin (s, m) hT).2
  have hrIn := hr (s, m)
  set p' := ((tickT L s m).s, (tickT L s m).m)
  have hP' := hPsd p'
  have hA : qf (P p') (A *ᵥ z (s, m)) ≤ (ρ * rIn (s, m)) ^ 2 := by
    have h1 := qf_nonneg hc (z (s, m))
    have h2 : qf (ρ ^ 2 • P (s, m) - Aᵀ * P p' * A) (z (s, m)) =
        ρ ^ 2 * qf (P (s, m)) (z (s, m)) - qf (Aᵀ * P p' * A) (z (s, m)) := by
      unfold qf; rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [qf_mulVec]
    nlinarith [h1, h2, hzin, sq_nonneg ρ]
  have hsA := Real.sqrt_le_iff.mpr ⟨by positivity, hA⟩
  have hse := Real.sqrt_le_iff.mpr ⟨hε, he⟩
  have ht := sqrt_qf_add_le hP'.1 hP'.2 (A *ᵥ z (s, m)) e
  have key : Real.sqrt (qf (P p') (A *ᵥ z (s, m) + e)) ≤ rOut p' := by linarith
  have h0 := qf_nonneg hP'.1 (A *ᵥ z (s, m) + e)
  have hq : qf (P p') (z p') ≤ rOut p' ^ 2 := by
    rw [hz]
    calc _ = Real.sqrt (qf (P p') (A *ᵥ z (s, m) + e)) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ rOut p' ^ 2 := by gcongr
  exact hout p' (hside s m hT) hq

end ExpProofs.CiProof
