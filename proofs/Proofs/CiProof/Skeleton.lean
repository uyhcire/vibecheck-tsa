import Proofs.CiProof.Reduce
import Ci.proof.T

/-! Skeleton of `TInvariant Ci.Proof.lawT`: the final theorem composed from named obligations through
`tInvariant_of_lyap`. Every `sorry` below is an open obligation; see `docs/ci/log-proof.md` for status and the
measured margins. NOT claimed in `CiClaims.lean`.

Obligations:
* bridge (`inT_sound`, `inT_complete`): the integer `inT` against the real data, exact up to the floor in the
  altitude interpolation of the form (hence `rIn² = (r2 + 1)/2^K`, `rOut² = r2/2^K`). Mechanical.
* `pNode_psd`: each node matrix of `TData.pTab` is symmetric positive semidefinite. Mechanical (exact LDLᵀ).
* model (`tick_safe_climb`, `tick_side`, `tick_encl`): the content. Numerically `tick_side` and `tick_encl`
  are FALSE for the current data at the fast-coordinate tolerance edge (see the log), so `TData` must be
  redesigned before they can be discharged. -/

namespace Proofs.CiProof.Skel
open Ci Ci.Goals Ci.Proof Matrix Jsb

abbrev L : Ci.Law := Ci.Proof.lawT

/-- Slow-coordinate deviation `k` (raw) from the climb manifold at the state's altitude, as `inT` computes it. -/
def dev (p : State × Ci.Lawfirst.Mem) (k : Nat) : Int :=
  let h := p.1.h.raw
  let span : Int := 10 * 65536
  let i := (h / span).toNat
  coord p.1 p.2 TData.fields[k]! - Ci.Proof.lerp (TData.centre[i]!)[k]! (TData.centre[i + 1]!)[k]! (h - i * span) span

def z (p : State × Ci.Lawfirst.Mem) : Fin 7 → ℝ := fun k => (dev p k.val : ℝ)

/-- Node matrix `j` of the form, real, unscaled raw units times 2^K. -/
def pNode (j : Nat) : Matrix (Fin 7) (Fin 7) ℝ := fun a b => (((TData.pTab[j]!)[a.val]!)[b.val]! : ℝ)

/-- Interpolation weight in [0, 1] between nodes `j` and `j + 1`. -/
noncomputable def wt (h : Int) : ℝ :=
  let spanP : Int := 100 * 65536
  max 0 (min 1 (((h - (h / spanP).toNat * spanP : Int) : ℝ) / (spanP : ℝ)))

noncomputable def P (p : State × Ci.Lawfirst.Mem) : Matrix (Fin 7) (Fin 7) ℝ :=
  let j := (p.1.h.raw / (100 * 65536)).toNat
  ((2 : ℝ) ^ TData.pK)⁻¹ • ((1 - wt p.1.h.raw) • pNode j + wt p.1.h.raw • pNode (j + 1))

/-- Side conditions: altitude band, stall bit, stored α command, and the fast-coordinate tolerances. -/
def side (p : State × Ci.Lawfirst.Mem) : Prop :=
  hLoT ≤ p.1.h.raw ∧ p.1.h.raw ≤ hHiT ∧ p.1.stall.raw = 0 ∧ -900000 ≤ p.2.ac ∧ p.2.ac ≤ 900000 ∧
  ∀ k < TData.fields.size - TData.nSlow,
    let j := (p.1.h.raw / (100 * 65536)).toNat
    let fP := p.1.h.raw - j * (100 * 65536)
    let d : Array Int := (List.range TData.nSlow).toArray.map (dev p)
    let pred := Ci.Proof.lerp (gmul (TData.gTab[j]!) d k) (gmul (TData.gTab[j + 1]!) d k) fP (100 * 65536) / (2 ^ TData.gK : Int)
    (-(TData.tol[k]!) ≤ dev p (TData.nSlow + k) - pred ∧ dev p (TData.nSlow + k) - pred ≤ (TData.tol[k]!))

noncomputable def rIn : ℝ := Real.sqrt (((TData.r2 + 1 : Int) : ℝ) / (2 : ℝ) ^ TData.pK)
noncomputable def rOut : ℝ := Real.sqrt (((TData.r2 : Int) : ℝ) / (2 : ℝ) ^ TData.pK)

theorem pNode_psd (j : Nat) : (pNode j).PosSemidef ∧ (pNode j)ᵀ = pNode j := by
  sorry

theorem P_psd (p : State × Ci.Lawfirst.Mem) : (P p).PosSemidef ∧ (P p)ᵀ = P p := by
  have w0 : 0 ≤ wt p.1.h.raw := le_max_left _ _
  have w1 : wt p.1.h.raw ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  obtain ⟨a0, s0⟩ := pNode_psd ((p.1.h.raw / (100 * 65536)).toNat)
  obtain ⟨a1, s1⟩ := pNode_psd ((p.1.h.raw / (100 * 65536)).toNat + 1)
  have hk : (0 : ℝ) ≤ ((2 : ℝ) ^ TData.pK)⁻¹ := by positivity
  refine ⟨?_, ?_⟩
  · unfold P
    exact ((a0.smul (by linarith)).add (a1.smul w0)).smul hk
  · unfold P
    rw [transpose_smul, transpose_add, transpose_smul, transpose_smul, s0, s1]

theorem inT_sound (p : State × Ci.Lawfirst.Mem) (h : L.inT p = true) : side p ∧ qf (P p) (z p) ≤ rIn ^ 2 := by
  sorry

theorem inT_complete (p : State × Ci.Lawfirst.Mem) (hs : side p) (hq : qf (P p) (z p) ≤ rOut ^ 2) :
    L.inT p = true := by
  sorry

theorem tick_safe_climb (s : State) (m : Ci.Lawfirst.Mem) (hT : L.inT (s, m) = true) :
    (tickT L s m).safe = true ∧ (tickT L s m).climb = true := by
  sorry

theorem tick_side (s : State) (m : Ci.Lawfirst.Mem) (hT : L.inT (s, m) = true) :
    side ((tickT L s m).s, (tickT L s m).m) := by
  sorry

theorem tick_encl (s : State) (m : Ci.Lawfirst.Mem) (hT : L.inT (s, m) = true) :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (e : Fin 7 → ℝ) (ρ ε : ℝ),
      z ((tickT L s m).s, (tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((tickT L s m).s, (tickT L s m).m)) e ≤ ε ^ 2 ∧ ρ * rIn + ε ≤ rOut := by
  sorry

/-- The final theorem, modulo the obligations above. -/
theorem tinv : TInvariant L :=
  tInvariant_of_lyap L side z P rIn rOut (Real.sqrt_nonneg _) P_psd inT_sound inT_complete
    tick_safe_climb tick_side tick_encl

end Proofs.CiProof.Skel
