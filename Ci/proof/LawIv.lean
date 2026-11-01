import Ci.proof.Law

/-! Interval bound on the ci-proof law's elevator over a box of states and memories: the interval twin of
`Ci.Proof.stepP`, on `Int × Int` pairs (lo, hi). Every operation is monotone or evaluated at the corners, so the
result encloses the law's output for every state in the box (soundness: `Proofs.CiProof.LawIvSound`). -/

namespace Ci.Proof.LawIv
open Vibecheck Jsb Ci.Lawfirst

abbrev I := Int × Int

def add (a b : I) : I := (a.1 + b.1, a.2 + b.2)
def sub (a b : I) : I := (a.1 - b.2, a.2 - b.1)
def const (c : Int) : I := (c, c)
/-- Product of two intervals (no rescaling). -/
def mul (a b : I) : I :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))
/-- `x / d` for a positive constant `d` (floor division, monotone). -/
def divC (a : I) (d : Int) : I := (a.1 / d, a.2 / d)
/-- `n / d` for an interval `d` of positive values: extremes at the corners. -/
def divI (n d : I) : I :=
  (min (min (n.1 / d.1) (n.1 / d.2)) (min (n.2 / d.1) (n.2 / d.2)),
   max (max (n.1 / d.1) (n.1 / d.2)) (max (n.2 / d.1) (n.2 / d.2)))
def maxC (a : I) (c : Int) : I := (max a.1 c, max a.2 c)
def minI (a b : I) : I := (min a.1 b.1, min a.2 b.2)
def clamp (lo hi : Int) (a : I) : I := (clampI lo hi a.1, clampI lo hi a.2)
def clampIv (lo : Int) (hi : I) (a : I) : I := (max lo (min hi.1 a.1), max lo (min hi.2 a.2))
def isqrt (a : I) : I := ((Nat.sqrt a.1.toNat : Int), (Nat.sqrt a.2.toNat : Int))
/-- Square of an interval. -/
def sq (a : I) : I := if 0 ≤ a.1 then (a.1 * a.1, a.2 * a.2) else if a.2 ≤ 0 then (a.2 * a.2, a.1 * a.1)
  else (0, max (a.1 * a.1) (a.2 * a.2))

/-- Box of the law's inputs: state fields used by the law and its memory. -/
structure Box where
  vx : I
  vz : I
  dx : I
  dz : I
  q : I
  ah : I
  au : I
  /-- density from the atmosphere table over the box's altitudes -/
  rho : I
  eI : I

/-- Elevator (raw, before the scoreboard's clamp) of `stepP p1`, as an interval; `none` when a guard of the law
cannot be decided on the box (a division by a possibly non-positive quantity). -/
def elev (b : Box) : Option I :=
  let u := add (mul b.vx b.dx) (mul b.vz b.dz)
  let w := sub (mul b.vx b.dz) (mul b.vz b.dx)
  if !(0 < u.1 && 0 < b.vx.1) then none else
  let ta := divI (mul w (const 65536)) u
  let v := isqrt (add (sq b.vx) (sq b.vz))
  let tg := divI (mul b.vz (const 65536)) b.vx
  let raw := sub (add (add (const p1.aRef) (divC (mul (const p1.kV) (maxC (sub v (const p1.vC)) (-vBand))) 65536))
      (divC (mul (const p1.kG) (sub (const p1.gC) tg)) 65536))
    (divC (mul (const p1.kGL) (maxC (sub tg (const p1.gMax)) 0)) 65536)
  -- load factor of the stored accelerations, for the aN cap
  let ln := sub (mul (add b.au (const Ci.gRaw)) b.dx) (mul b.ah b.dz)
  let n := divC ln Ci.gRaw
  -- the load-factor cap: aN = a0 + (ta − a0)·nL/n
  if !(19661 < n.1 && p1.a0 < ta.1) then none else
  -- nL is nLimUp when vz > 0, else nLim; aN is non-decreasing in nL (ta > a0, n > 0)
  let nL : I := if 0 < b.vz.1 then const p1.nLimUp else if b.vz.2 ≤ 0 then const p1.nLim else (p1.nLimUp, p1.nLim)
  let aN := add (const p1.a0) (divI (mul (sub ta (const p1.a0)) nL) n)
  let ac := clampIv p1.aMin (min p1.aMax aN.1, min p1.aMax aN.2) raw
  let err := sub ac ta
  let rho := b.rho
  let v2 := divC (add (sq b.vx) (sq b.vz)) 65536
  let ne := divC (mul (divC (mul (divC (mul rho v2) 65536) (add ta (const 3789))) 65536) (const 317)) 65536
  if !(65536 ≤ v.1) then none else
  let qRef := divI (mul (const Ci.gRaw) (sub ne (const 65536))) v
  let e := sub (add (add b.eI (divC (mul (const p1.kF) ac) 65536)) (divC (mul (const p1.kA) err) 65536))
    (divC (mul (const p1.kQ) (sub b.q qRef)) 65536)
  some (clamp (-65536) 65536 e)

end Ci.Proof.LawIv
