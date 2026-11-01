import Ci.Interface

/-! CI referee: safety definition and rollout semantics, exact integer arithmetic on raw `Fx` (scoreboard-owned). -/

namespace Ci
open Vibecheck Jsb

/-- tan(0.28 rad) in raw units; 0.28 rad is the CL peak of `C172.tbl_x_5`. -/
def alphaTanMax : Int := 18845
/-- 9.80665 m/s² -/
def gRaw : Int := 642689
def loadMaxX10 : Int := 38
/-- Airspeed floor, m/s (raw). -/
def vFloor : Int := 27 * 65536
/-- Height above the flat terrain at h = 0 that every rollout substep must keep, m (raw). -/
def clearance : Int := 5 * 65536
/-- Vertical speed that a terminal set must keep at every substep, m/s (raw). -/
def climbVz : Int := 2 * 65536
def budgetTicks : Nat := 640

def alphaOk (s : State) : Bool :=
  let u := s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw
  let w := s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw
  0 < u && w * 65536 ≤ alphaTanMax * u

/-- Body-normal specific force times `g · 2^32`: `((au + g)·cos θ − ah·sin θ)`. -/
def loadNum (s : State) : Int := (s.au.raw + gRaw) * s.dx.raw - s.ah.raw * s.dz.raw

def loadOk (s : State) : Bool := 10 * loadNum s ≤ loadMaxX10 * gRaw * 65536

def speedOk (s : State) : Bool := vFloor * vFloor ≤ s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw

def envOk (s : State) : Bool := alphaOk s && loadOk s && speedOk s && s.stall.raw == 0

def safeOk (s : State) : Bool := envOk s && clearance ≤ s.h.raw

def sub (u : Input) (s : State) : State := Jsb.step 7 true u s

structure TickR (σ : Type) where
  s : State
  m : σ
  safe : Bool
  climb : Bool

def subT (u : Input) : Nat → State → Bool → Bool → State × Bool × Bool
  | 0, s, ok, cl => (s, ok, cl)
  | n + 1, s, ok, cl =>
    let s' := sub u s
    subT u n s' (ok && safeOk s') (cl && climbVz ≤ s'.vz.raw && s.h.raw < s'.h.raw)

/-- `safe`: all 8 substeps pass `safeOk`; `climb`: at each, vz ≥ `climbVz` and h rose. -/
def tickT (L : Law) (s : State) (m : L.σ) : TickR L.σ :=
  let r := L.step m s
  let (s', ok, cl) := subT (clampInput r.1) 8 s true true
  ⟨s', r.2, ok, cl⟩

/-- Outcome of one law's rollout from a commit. `fail` is the first unsafe substep (tick·8 + j). -/
structure Roll where
  reached : Bool
  ticks : Nat
  fail : Option Nat
  hMin : Int
  maxTanA : Int
  maxLoadNum : Int
  minV2 : Int
  deriving Repr, Inhabited

def Roll.accepted (r : Roll) : Bool := r.reached && r.fail.isNone

structure Acc where
  idx : Nat
  fail : Option Nat
  hMin : Int
  maxTanA : Int
  maxLoadNum : Int
  minV2 : Int

def Acc.obs (a : Acc) (s : State) : Acc :=
  let u := s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw
  let w := s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw
  let ta := if u > 0 then w * 65536 / u else 1000000000
  { idx := a.idx + 1,
    fail := if a.fail.isNone && !safeOk s then some a.idx else a.fail,
    hMin := min a.hMin s.h.raw, maxTanA := max a.maxTanA ta, maxLoadNum := max a.maxLoadNum (loadNum s),
    minV2 := min a.minV2 (s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw) }

def subObs (u : Input) : Nat → State → Acc → State × Acc
  | 0, s, a => (s, a)
  | n + 1, s, a => let s' := sub u s; subObs u n s' (a.obs s')

def rollLaw (L : Law) (c : Commit) (n : Nat) : Roll :=
  let rec go : Nat → Nat → L.σ → State → Acc → Roll
    | fuel, k, m, s, a =>
      if L.inT (s, m) then ⟨true, k, a.fail, a.hMin, a.maxTanA, a.maxLoadNum, a.minV2⟩ else
      match fuel with
      | 0 => ⟨false, k, a.fail, a.hMin, a.maxTanA, a.maxLoadNum, a.minV2⟩
      | fuel + 1 =>
        let r := L.step m s
        let (s', a') := subObs (clampInput r.1) 8 s a
        if a'.fail.isSome then ⟨false, k + 1, a'.fail, a'.hMin, a'.maxTanA, a'.maxLoadNum, a'.minV2⟩
        else go fuel (k + 1) r.2 s' a'
  go n 0 (L.init c) c.s ⟨0, none, c.s.h.raw, -1000000000, -1000000000000000000, 1000000000000000000⟩

def check (S : Submission) (c : Commit) : Option (Nat × Roll) × Nat :=
  let rec go : List Law → Nat → Nat → Option (Nat × Roll) × Nat
    | [], _, t => (none, t)
    | L :: Ls, i, t =>
      let r := rollLaw L c S.horizon
      if r.accepted then (some (i, r), t + r.ticks) else go Ls (i + 1) (t + r.ticks)
  go S.laws 0 0

/-- Domain of commit states the benchmark draws from. -/
def commitOk (c : Commit) : Bool :=
  envOk c.s && 500 * 65536 ≤ c.s.h.raw && c.s.h.raw ≤ 2000 * 65536 &&
  c.s.vx.raw * c.s.vx.raw + c.s.vz.raw * c.s.vz.raw ≤ (80 * 65536) * (80 * 65536) &&
  c.pilot.elev == (clampInput c.pilot).elev && c.pilot.thr == (clampInput c.pilot).thr &&
  c.pilot.beta.raw == 0 && c.pilot.phi.raw == 0

def Commit.atHeight (c : Commit) (h : Int) : Commit := { c with s := { c.s with h := ⟨h⟩, x := ⟨0⟩ } }

end Ci
