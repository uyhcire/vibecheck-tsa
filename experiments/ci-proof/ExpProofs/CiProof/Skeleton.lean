import ExpProofs.CiProof.Reduce
import Ci.proof.Final

/-! The planned route to the open obligation `Ci.Proof.TickInT` (and hence `TInvariant Ci.Proof.lawT` via the proved
`Ci.Proof.tInvariant_of_tickInT`): a conditional theorem, fully proved, whose hypotheses are the remaining
obligations. Nothing here is claimed.

* `side`: the band, fast-coordinate and cell-box checks of `inT` (everything but the slow ellipsoid);
* `z`, `P`, `rIn`, `rOut`: the slow deviations and the interpolated form and radius as reals;
* bridges `hin`/`hout`: `quadOk` against the real form (exact up to the floors in the altitude interpolation, hence
  the `+ 1` in `rIn`); mechanical;
* `hPsd`: each node matrix of `TData.pTab` is symmetric positive semidefinite (true numerically: they come out of
  the LMI with `P ⪰ I`); mechanical, e.g. by an exact LDLᵀ certificate;
* `hside` and `henc`: the content. `henc` asks for an affine enclosure of the tick in T's own coordinates with a
  contraction certificate; numerically the form contracts by ρ ≈ 0.990 per tick (interval-sampled LMI) and the
  worst observed one-tick ratio over T is 0.986, so the enclosure's remainder must be below about 0.5 % of r. -/

namespace ExpProofs.CiProof.Skel
open Ci Ci.Goals Ci.Proof Matrix ExpJsb

abbrev L : Ci.Law := Ci.Proof.lawT

def z (p : State × Ci.Lawfirst.Mem) : Fin 7 → ℝ := fun k => (dev p k.val : ℝ)

/-- Node matrix `j` of the form (raw slow deviations, scaled by 2^K). -/
def pNode (j : Nat) : Matrix (Fin 7) (Fin 7) ℝ := fun a b => ((((TData.pTab[j]!)[a.val]!)[b.val]! : Int) : ℝ)

/-- Interpolation weight in [0, 1] between nodes `j` and `j + 1`. -/
noncomputable def wt (h : Int) : ℝ := max 0 (min 1 ((nodeF h : ℝ) / (100 * 65536 : ℝ)))

noncomputable def P (p : State × Ci.Lawfirst.Mem) : Matrix (Fin 7) (Fin 7) ℝ :=
  ((2 : ℝ) ^ TData.pK)⁻¹ • ((1 - wt p.1.h.raw) • pNode (nodeJ p.1.h.raw) + wt p.1.h.raw • pNode (nodeJ p.1.h.raw + 1))

/-- Radius² (scaled by 2^K) at the state's altitude, as `quadOk` interpolates it. -/
def r2At (p : State × Ci.Lawfirst.Mem) : Int :=
  lerp TData.r2Tab[nodeJ p.1.h.raw]! TData.r2Tab[nodeJ p.1.h.raw + 1]! (nodeF p.1.h.raw) (100 * 65536)

noncomputable def rIn (p : State × Ci.Lawfirst.Mem) : ℝ := Real.sqrt (((r2At p + 1 : Int) : ℝ) / (2 : ℝ) ^ TData.pK)
noncomputable def rOut (p : State × Ci.Lawfirst.Mem) : ℝ := Real.sqrt (((r2At p : Int) : ℝ) / (2 : ℝ) ^ TData.pK)

def side (p : State × Ci.Lawfirst.Mem) : Prop := bandOk p = true ∧ fastOk p = true ∧ boxOk p = true

/-- `TickInT` from the remaining obligations. -/
theorem tickInT_of_obligations
    (hPsd : ∀ p, (P p).PosSemidef ∧ (P p)ᵀ = P p)
    (hin : ∀ p, L.inT p = true → side p ∧ qf (P p) (z p) ≤ rIn p ^ 2)
    (hout : ∀ p, side p → qf (P p) (z p) ≤ rOut p ^ 2 → L.inT p = true)
    (hside : ∀ s m, L.inT (s, m) = true → side ((tickT L s m).s, (tickT L s m).m))
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (e : Fin 7 → ℝ) (ρ ε : ℝ),
      z ((tickT L s m).s, (tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((tickT L s m).s, (tickT L s m).m)) e ≤ ε ^ 2 ∧
      ρ * rIn (s, m) + ε ≤ rOut ((tickT L s m).s, (tickT L s m).m)) :
    TickInT :=
  inT_next_of_lyap L side z P rIn rOut (fun _ => Real.sqrt_nonneg _) hPsd hin hout hside henc

/-- And so `TInvariant lawT` from the same obligations. -/
theorem tInvariant_of_obligations
    (hPsd : ∀ p, (P p).PosSemidef ∧ (P p)ᵀ = P p)
    (hin : ∀ p, L.inT p = true → side p ∧ qf (P p) (z p) ≤ rIn p ^ 2)
    (hout : ∀ p, side p → qf (P p) (z p) ≤ rOut p ^ 2 → L.inT p = true)
    (hside : ∀ s m, L.inT (s, m) = true → side ((tickT L s m).s, (tickT L s m).m))
    (henc : ∀ s m, L.inT (s, m) = true → ∃ (A : Matrix (Fin 7) (Fin 7) ℝ) (e : Fin 7 → ℝ) (ρ ε : ℝ),
      z ((tickT L s m).s, (tickT L s m).m) = A *ᵥ z (s, m) + e ∧
      (ρ ^ 2 • P (s, m) - Aᵀ * P ((tickT L s m).s, (tickT L s m).m) * A).PosSemidef ∧
      0 ≤ ρ ∧ 0 ≤ ε ∧ qf (P ((tickT L s m).s, (tickT L s m).m)) e ≤ ε ^ 2 ∧
      ρ * rIn (s, m) + ε ≤ rOut ((tickT L s m).s, (tickT L s m).m)) :
    TInvariant L :=
  tInvariant_of_tickInT (tickInT_of_obligations hPsd hin hout hside henc)

end ExpProofs.CiProof.Skel
