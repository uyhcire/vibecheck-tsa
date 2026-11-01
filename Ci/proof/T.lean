import Ci.proof.Sub
import Ci.proof.TData

/-! ci-proof terminal set: a neighbourhood of the law's climb manifold. At altitude h the centre `c(h)` is the
manifold state (table at 10 m spacing, linear interpolation). With `d` the deviation of the 7 slow coordinates
(vx, vz, dz, q, rpm, tmap, integrator eI) from `c(h)`, the set requires

* `dᵀ P(h) d ≤ r²`, where `P(h)` interpolates per-altitude Lyapunov matrices of the linearised one-tick map;
* every fast coordinate (dx, udot, wdot, ah, au, qd, ah1, au1, pvz, pvz2) within `tol(h)` of `c(h) + G(h) d`, its
  value slaved to the slow ones (`tol(h)` covers the kinks of the piecewise-linear lift and drag tables);
* 10 m ≤ h ≤ 2640 m, stall bit 0, and the stored α command within ±900000 raw (so its slew clamp is inactive).

All arithmetic is on integers: two table lookups, two 7×7 quadratic forms and a 10×7 product. -/

namespace Ci.Proof
open Vibecheck Jsb Ci.Lawfirst

-- centre table: frozen-altitude equilibria of the climb (h held fixed), see `Ci/proof/py/frozen_tab.py`
def hLoT : Int := 10 * 65536
def hHiT : Int := 2640 * 65536

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

open TData in
def inT (p : State × Mem) : Bool := Id.run do
  let s := p.1
  let m := p.2
  let h := s.h.raw
  if !(hLoT ≤ h && h ≤ hHiT && s.stall.raw == 0 && -900000 ≤ m.ac && m.ac ≤ 900000) then return false
  -- centre at h
  let span : Int := 10 * 65536
  let i := (h / span).toNat
  let f := h - i * span
  let c0 := centre[i]!
  let c1 := centre[i + 1]!
  let dev := fun (k : Nat) => coord s m fields[k]! - lerp c0[k]! c1[k]! f span
  let d : Array Int := (List.range nSlow).toArray.map dev
  -- slow ellipsoid, P interpolated at 100 m nodes
  let spanP : Int := 100 * 65536
  let j := (h / spanP).toNat
  let fP := h - j * spanP
  let q0 := quad pTab[j]! d
  let q1 := quad pTab[j + 1]! d
  if lerp q0 q1 fP spanP > r2 then return false
  -- fast coordinates slaved to the slow ones
  let mut ok := true
  for k in [0:fields.size - nSlow] do
    let g0 := gmul gTab[j]! d k
    let g1 := gmul gTab[j + 1]! d k
    let pred := lerp g0 g1 fP spanP / (2 ^ gK : Int)
    let e := dev (nSlow + k) - pred
    let t := lerp (tolTab[j]!)[k]! (tolTab[j + 1]!)[k]! fP spanP
    if !(-t ≤ e && e ≤ t) then ok := false
  return ok

/-- The ci-proof law with the climb-manifold terminal set. -/
def lawT : Ci.Law :=
  { σ := Mem, name := "ciproof-T", init := initP p1, step := step, inT := inT, enc := encM, dec := decM }

end Ci.Proof
