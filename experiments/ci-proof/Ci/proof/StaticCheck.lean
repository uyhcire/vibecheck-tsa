import Ci.proof.T

/-! The table-only half of the static fit of T inside its cell boxes: for each 10 m cell, the box contains the
centre rows of the cell widened by the certified bound on each deviation (slow: `slowB − 1`; fast: the slaving
term `|G|·B`, the kink term and the tolerance, with floors). `staticOk` is evaluated by the kernel per cell; the
other half (the deviations obey those bounds) is `ExpProofs.CiProof.StaticBox`. -/

namespace Ci.Proof
open ExpVibecheck ExpJsb

def iabs (x : Int) : Int := max x (-x)

/-- Bound on a slow deviation in node interval `j`. -/
def sbound (j k : Nat) : Int := (TData.slowB[j]!)[k]! - 1

/-- `Σ_i |G_jj[kk][i]| · sbound j i`. -/
def gabs (j jj kk : Nat) : Int := ((List.range 7).map fun i => iabs ((TData.gTab[jj]!)[kk]!)[i]! * sbound j i).sum

/-- Bound on a fast deviation `kk` in node interval `j`. -/
def fbound (j kk : Nat) : Int :=
  max (gabs j j kk) (gabs j (j + 1) kk) / (2 ^ TData.gK : Int) + 1 +
  max TData.tkTab[j]! TData.tkTab[j + 1]! * max (iabs (TData.kbTab[j]!)[kk]!) (iabs (TData.kbTab[j + 1]!)[kk]!) / (2 ^ 50 : Int) + 1 +
  max (TData.tpTab[j]!)[kk]! (TData.tpTab[j + 1]!)[kk]!

def fieldBound (j k : Nat) : Int := if k < 7 then sbound j k else fbound j (k - 7)

def boxLo (ci f : Nat) : Int := if f = 19 then (TData.boxTab[ci]!)[38]! else (TData.boxTab[ci]!)[f]!
def boxHi (ci f : Nat) : Int := if f = 19 then (TData.boxTab[ci]!)[39]! else (TData.boxTab[ci]!)[19 + f]!

def cellLo (ci : Nat) : Int := hLoT + ci * cellSpan

def staticOk (ci : Nat) : Bool :=
  let a := cellLo ci
  let j := nodeJ a
  ((List.range 5).all fun r =>
    let ii := (a / (2 * 65536)).toNat + r
    (List.range 17).all fun k =>
      let f := TData.fields[k]!
      let c0 := (TData.centre[ii]!)[k]!
      let c1 := (TData.centre[ii + 1]!)[k]!
      decide (boxLo ci f ≤ min c0 c1 - fieldBound j k) && decide (max c0 c1 + fieldBound j k ≤ boxHi ci f)) &&
  decide (boxLo ci 1 ≤ a) && decide (min (a + cellSpan) hHiT ≤ boxHi ci 1) &&
  decide (boxLo ci 11 ≤ 0) && decide (0 ≤ boxHi ci 11) && decide (nodeJ (a + cellSpan - 1) = j) &&
  decide (a % (2 * 65536) = 0) && decide (0 ≤ a)

end Ci.Proof
