import Ci.proof.Sub
import Ci.proof.TData
import Jsb.Conformance

/-! ci-proof terminal set: a neighbourhood of the law's climb manifold. At altitude h the centre `c(h)` is the
manifold state (table at 2 m spacing, linear interpolation). With `d` the deviation of the 7 slow coordinates
(vx, vz, dz, q, rpm, tmap, integrator eI) from `c(h)`, the set requires

* `dᵀ P(h) d ≤ r(h)²` (r = 4.5 up to 2200 m, 3.6 from 2400 m), where `P(h)` interpolates per-altitude Lyapunov matrices of the linearised one-tick map;
* the fast coordinates (dx, udot, wdot, ah, au, qd, ah1, au1, pvz, pvz2) slaved to the slow ones: their residual
  `e` from `c(h) + G(h) d` has a component along a kink direction `k(h)` bounded by `τk(h)` (this covers the
  breakpoints of the piecewise-linear lift and drag tables, which the linear slaving cannot follow), and the rest of
  `e` bounded componentwise by `τ⊥(h)`;
* 10 m ≤ h < 2680 m, stall bit 0, and the stored α command within ±900000 raw (so its slew clamp is inactive);
* the state and `eI` inside the bounding box of the above over the state's 50 m altitude cell (`boxOk`); redundant
  by construction, it lets the one-tick safety proof work on boxes.

All arithmetic is on integers: table lookups, two 7×7 quadratic forms, two 10×7 products and a few dot products. -/

namespace Ci.Proof
open Vibecheck Jsb Ci.Lawfirst

-- centre table: frozen-altitude equilibria of the climb (h held fixed), see `Ci/proof/py/frozen_tab.py`
def hLoT : Int := 10 * 65536
def hHiT : Int := 2680 * 65536

/-- Raw value of coordinate `i` (state field index, 19 = integrator memory). -/
def coord (s : State) (m : Mem) (i : Nat) : Int :=
  match i with
  | 0 => s.x.raw | 1 => s.h.raw | 2 => s.vx.raw | 3 => s.vz.raw | 4 => s.dx.raw | 5 => s.dz.raw | 6 => s.q.raw
  | 7 => s.rpm.raw | 8 => s.tmap.raw | 9 => s.udot.raw | 10 => s.wdot.raw | 11 => s.stall.raw | 12 => s.ah.raw
  | 13 => s.au.raw | 14 => s.qd.raw | 15 => s.ah1.raw | 16 => s.au1.raw | 17 => s.pvz.raw | 18 => s.pvz2.raw
  | _ => m.eI

/-- `a + (b − a) · num / den`, floored. -/
def lerp (a b num den : Int) : Int := a + (b - a) * num / den

def quad (P : Array (Array Int)) (d : Array Int) : Int := Id.run do
  let mut acc : Int := 0
  for i in [0:7] do
    for j in [0:7] do
      acc := acc + P[i]![j]! * d[i]! * d[j]!
  return acc

def gmul (G : Array (Array Int)) (d : Array Int) (k : Nat) : Int := Id.run do
  let mut acc : Int := 0
  for j in [0:7] do
    acc := acc + G[k]![j]! * d[j]!
  return acc

/-- Altitude band, stall bit, stored α command. -/
def bandOk (p : State × Mem) : Bool :=
  hLoT ≤ p.1.h.raw && p.1.h.raw < hHiT && p.1.stall.raw == 0 && -900000 ≤ p.2.ac && p.2.ac ≤ 900000

open TData in
/-- Deviation (raw) of coordinate `k` of `TData.fields` from the climb manifold at the state's altitude. -/
def dev (p : State × Mem) (k : Nat) : Int :=
  let h := p.1.h.raw
  let span : Int := 2 * 65536
  let i := (h / span).toNat
  coord p.1 p.2 fields[k]! - lerp (centre[i]!)[k]! (centre[i + 1]!)[k]! (h - i * span) span

/-- The slow deviations `d`. -/
def dSlow (p : State × Mem) : Array Int := (List.range TData.nSlow).toArray.map (dev p)

/-- Node index and offset of the 100 m interpolation of the form and the fast-coordinate data. -/
def nodeJ (h : Int) : Nat := (h / (100 * 65536)).toNat
def nodeF (h : Int) : Int := h - nodeJ h * (100 * 65536)

open TData in
/-- The slow ellipsoid: `dᵀ P(h) d ≤ r(h)²`, both interpolated at 100 m nodes. -/
def quadOk (p : State × Mem) : Bool :=
  let h := p.1.h.raw
  let j := nodeJ h
  let fP := nodeF h
  let d := dSlow p
  lerp (quad pTab[j]! d) (quad pTab[j + 1]! d) fP (100 * 65536) ≤ lerp r2Tab[j]! r2Tab[j + 1]! fP (100 * 65536)

open TData in
/-- The fast coordinates slaved to the slow ones: residual e = (fast − c(h) − G(h) d); its component along the kink
direction k(h) (from the breakpoints of the lift and drag tables) is bounded loosely, the rest tightly. -/
def fastOk (p : State × Mem) : Bool := Id.run do
  let h := p.1.h.raw
  let j := nodeJ h
  let fP := nodeF h
  let spanP : Int := 100 * 65536
  let d := dSlow p
  let nf := fields.size - nSlow
  let es : Array Int := (List.range nf).toArray.map fun k =>
    dev p (nSlow + k) - lerp (gmul gTab[j]! d k) (gmul gTab[j + 1]! d k) fP spanP / (2 ^ gK : Int)
  let dotK := fun (kv : Array Int) => Id.run do
    let mut acc : Int := 0
    for k in [0:nf] do
      acc := acc + kv[k]! * es[k]!
    return acc
  let lam := lerp (dotK kTab[j]!) (dotK kTab[j + 1]!) fP spanP
  let tk := lerp tkTab[j]! tkTab[j + 1]! fP spanP
  let mut ok := -tk ≤ lam && lam ≤ tk
  for k in [0:nf] do
    let kb := lerp (kbTab[j]!)[k]! (kbTab[j + 1]!)[k]! fP spanP
    let perp := es[k]! - lam * kb / (2 ^ 50 : Int)
    let t := lerp (tpTab[j]!)[k]! (tpTab[j + 1]!)[k]! fP spanP
    if !(-t ≤ perp && perp ≤ t) then ok := false
  return ok

/-- The conditions above other than the cell box (the band is checked first, so no table is read out of range). -/
def restOk (p : State × Mem) : Bool := bandOk p && quadOk p && fastOk p

instance (I : Iv) (x : Fx) : Decidable (I.Mem x) := by cases I <;> unfold Iv.Mem <;> infer_instance
instance (S : StateOf Iv) (s : StateOf Fx) : Decidable (S.Mem s) := by unfold StateOf.Mem; infer_instance
instance (B : CLOf Iv) (c : CLOf Fx) : Decidable (B.Mem c) := by unfold CLOf.Mem; infer_instance

/-- Width of the altitude cells of `TData.boxTab`. -/
def cellSpan : Int := 50 * 65536

/-- Cell of altitude `h` (raw). -/
def cellIdx (h : Int) : Nat := ((h - hLoT) / cellSpan).toNat

/-- Box `i` of `TData.boxTab` as an interval state (x unconstrained); the 20th coordinate is the memory `eI`. -/
def cellBox (i : Nat) : CLOf Iv :=
  let b := TData.boxTab[i]!
  let f (k : Nat) : Iv := .box b[k]! b[19 + k]!
  ⟨⟨.top, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩,
   .box b[38]! b[39]!⟩

/-- The state and memory as a point of `cellBox`'s space. -/
def pt (p : State × Mem) : CLOf Fx := ⟨p.1, ⟨p.2.eI⟩⟩

def boxOk (p : State × Mem) : Bool :=
  decide (cellIdx p.1.h.raw < TData.boxTab.size) && decide (-900000 ≤ p.2.ac ∧ p.2.ac ≤ 900000) &&
  decide ((cellBox (cellIdx p.1.h.raw)).Mem (pt p))

/-- The terminal set: the cell box (redundant, for the safety proof) and the conditions above. -/
def inT (p : State × Mem) : Bool := restOk p && boxOk p

/-- The ci-proof law with the climb-manifold terminal set. -/
def lawT : Ci.Law :=
  { σ := Mem, name := "ciproof-T", init := initP p1, step := step, inT := inT, enc := encM, dec := decM }

end Ci.Proof
