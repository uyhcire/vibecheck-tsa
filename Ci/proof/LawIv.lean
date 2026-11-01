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

def uI (b : Box) : I := add (mul b.vx b.dx) (mul b.vz b.dz)
def wI (b : Box) : I := sub (mul b.vx b.dz) (mul b.vz b.dx)
def taI (b : Box) : I := divI (mul (wI b) (const 65536)) (uI b)
def v2sI (b : Box) : I := add (sq b.vx) (sq b.vz)
def vI (b : Box) : I := isqrt (v2sI b)
def tgI (b : Box) : I := divI (mul b.vz (const 65536)) b.vx
def rawI (b : Box) : I :=
  sub (add (add (const p1.aRef) (divC (mul (const p1.kV) (maxC (sub (vI b) (const p1.vC)) (-vBand))) 65536))
      (divC (mul (const p1.kG) (sub (const p1.gC) (tgI b))) 65536))
    (divC (mul (const p1.kGL) (maxC (sub (tgI b) (const p1.gMax)) 0)) 65536)
/-- Load factor of the stored accelerations (raw g), for the law's load-factor cap. -/
def nI (b : Box) : I := divC (sub (mul (add b.au (const Ci.gRaw)) b.dx) (mul b.ah b.dz)) Ci.gRaw
/-- nL is nLimUp when vz > 0, else nLim. -/
def nLI (b : Box) : I := if 0 < b.vz.1 then const p1.nLimUp else if b.vz.2 ≤ 0 then const p1.nLim else (p1.nLimUp, p1.nLim)
def aNI (b : Box) : I := add (const p1.a0) (divI (mul (sub (taI b) (const p1.a0)) (nLI b)) (nI b))
def acI (b : Box) : I := clampIv p1.aMin (min p1.aMax (aNI b).1, min p1.aMax (aNI b).2) (rawI b)
def neI (b : Box) : I :=
  divC (mul (divC (mul (divC (mul b.rho (divC (v2sI b) 65536)) 65536) (add (taI b) (const 3789))) 65536) (const 317)) 65536
def qRefI (b : Box) : I := divI (mul (const Ci.gRaw) (sub (neI b) (const 65536))) (vI b)
def eRawI (b : Box) : I :=
  sub (add (add b.eI (divC (mul (const p1.kF) (acI b)) 65536)) (divC (mul (const p1.kA) (sub (acI b) (taI b))) 65536))
    (divC (mul (const p1.kQ) (sub b.q (qRefI b))) 65536)

/-- Guards under which the interval evaluation is valid: positive denominators, an active load-factor branch. -/
def guards (b : Box) : Bool :=
  0 < (uI b).1 && 0 < b.vx.1 && 19661 < (nI b).1 && p1.a0 < (taI b).1 && 65536 ≤ (vI b).1

/-- Elevator (raw, before the scoreboard's clamp) of `stepP p1`, as an interval; `none` when a guard fails. -/
def elev (b : Box) : Option I := if guards b then some (clamp (-65536) 65536 (eRawI b)) else none

end Ci.Proof.LawIv
