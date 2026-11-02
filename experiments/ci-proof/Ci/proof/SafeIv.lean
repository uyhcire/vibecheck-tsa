import Ci.proof.T
import Ci.proof.LawIv
import ExpJsb.Conformance

/-! Interval check of the one-tick safety and climb clauses of `Ci.Proof.lawT` over a box of states.

`ok B` evaluates the law's elevator on the box (`LawIv.elev`), then flies the 8 substeps of the tick on intervals
(`ExpJsb.step` over `Iv`, whose soundness is `ExpJsb.step_sound`) and checks `safeOk` and the climb clause at each substep
on intervals. The climb clause's `h rose` needs the altitude increment `shr(ab3(vz, pvz, pvz2), 7)`; `ab3` is
evaluated as `(12 vz + 11 (vz − pvz) − 5 (pvz − pvz2)) / 12` with the two differences tracked as their own
intervals, since `vz' − pvz' = shr(3 au − au1, 8)` and `pvz' − pvz2' = vz − pvz` exactly. The box's 20th coordinate
(`CLOf.elev`) carries the law memory `eI`. -/

namespace Ci.Proof.SafeIv
open ExpVibecheck ExpJsb Ci.Lawfirst
open Ci.Proof.LawIv (I mul)

def lo : Iv → Int | .box a _ => a | .top => 0
def hi : Iv → Int | .box _ b => b | .top => 0
def isBox : Iv → Bool | .box _ _ => true | .top => false
def pr (v : Iv) : I := (lo v, hi v)

/-- `alphaOk` on intervals. -/
def alphaI (S : StateOf Iv) : Bool :=
  let u := LawIv.add (mul (pr S.vx) (pr S.dx)) (mul (pr S.vz) (pr S.dz))
  let w := LawIv.sub (mul (pr S.vx) (pr S.dz)) (mul (pr S.vz) (pr S.dx))
  decide (0 < u.1) && decide (w.2 * 65536 ≤ Ci.alphaTanMax * u.1)

/-- `loadOk` on intervals. -/
def loadI (S : StateOf Iv) : Bool :=
  let l := LawIv.sub (mul (LawIv.add (pr S.au) (Ci.gRaw, Ci.gRaw)) (pr S.dx)) (mul (pr S.ah) (pr S.dz))
  decide (10 * l.2 ≤ Ci.loadMaxX10 * Ci.gRaw * 65536)

/-- `speedOk` on intervals. -/
def speedI (S : StateOf Iv) : Bool :=
  decide (Ci.vFloor * Ci.vFloor ≤ (LawIv.sq (pr S.vx)).1 + (LawIv.sq (pr S.vz)).1)

/-- `safeOk` on intervals. -/
def safeI (S : StateOf Iv) : Bool :=
  isBox S.vx && isBox S.vz && isBox S.dx && isBox S.dz && isBox S.au && isBox S.ah && isBox S.stall && isBox S.h &&
  alphaI S && loadI S && speedI S && decide (lo S.stall = 0) && decide (hi S.stall = 0) &&
  decide (Ci.clearance ≤ lo S.h) && decide (hi S.h ≤ Ci.hMax)

/-- Altitude increment of a substep from `vz` and the two tracked differences. -/
def dhI (vz : Iv) (d1 d2 : I) : I :=
  (ExpJsb.Iv.shrZ ((12 * lo vz + 11 * d1.1 - 5 * d2.2) / 12) 7, ExpJsb.Iv.shrZ ((12 * hi vz + 11 * d1.2 - 5 * d2.1) / 12) 7)

/-- The 8 substeps: safety and climb at each; `hb` bounds the altitude (tracked with the same increments), and at the
end it must lie in T's band. -/
def plantOK (U : InputOf Iv) : Nat → StateOf Iv → I → I → I → Bool
  | 0, _, _, _, hb => decide (hLoT ≤ hb.1) && decide (hb.2 < hHiT)
  | n + 1, S, d1, d2, hb =>
    let dh := dhI S.vz d1 d2
    let nx := ExpJsb.step 7 true U S
    let nd1 := ExpJsb.Iv.shr (ExpJsb.Iv.sub (ExpJsb.Iv.mul (.box 196608 196608) S.au) S.au1) 8
    isBox S.vz && isBox nd1 && isBox nx.vz && isBox nx.h &&
    safeI nx && (decide (Ci.climbVz ≤ lo nx.vz) && decide (1 ≤ dh.1) || decide (Ci.climbTop ≤ lo nx.h)) &&
    plantOK U n nx (lo nd1, hi nd1) d1 (hb.1 + dh.1, hb.2 + dh.2)

/-- Density interval over the box's altitudes (the table is evaluated at both ends and at every node between). -/
def rhoI (h : Iv) : I :=
  let r0 := (ExpJsb.Iv.atm ExpJsb.C172.atmRho h)
  (lo r0, hi r0)

/-- Throttle interval: `thrH` is non-increasing in h. -/
def thrI (h : Iv) : I := (thrH (hi h), thrH (lo h))

def ok (B : CLOf Iv) : Bool :=
  let S := B.s
  if !(isBox S.vx && isBox S.vz && isBox S.dx && isBox S.dz && isBox S.q && isBox S.ah && isBox S.au &&
       isBox S.h && isBox S.pvz && isBox S.pvz2 && isBox B.elev && isBox (ExpJsb.Iv.atm ExpJsb.C172.atmRho S.h)) then false else
  let b : LawIv.Box := ⟨pr S.vx, pr S.vz, pr S.dx, pr S.dz, pr S.q, pr S.ah, pr S.au, rhoI S.h, pr B.elev⟩
  match LawIv.elev b with
  | none => false
  | some e =>
    let t := thrI S.h
    let U : InputOf Iv := ⟨.box e.1 e.2, .box t.1 t.2, .box 0 0, .box 0 0⟩
    plantOK U 8 S (LawIv.sub (pr S.vz) (pr S.pvz)) (LawIv.sub (pr S.pvz) (pr S.pvz2)) (pr S.h)

end Ci.Proof.SafeIv
