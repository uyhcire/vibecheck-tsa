import Ci.lawfirst.Law

/-! lawfirst submission pieces: the law instance and its terminal set. -/

namespace Ci.Lawfirst
open Vibecheck Jsb

def p1 : P := { vC := 32 * 65536, nLim := 235929, gMax := 29491, kGL := 65536, kVlo := 0, qss := true, aRef := 6500, kI := 6554, nLimUp := 183500 }

/-- Terminal set: settled climb near the law's climb-out, consistent derivative and history fields. -/
def climbT (p : State × Mem) : Bool :=
  let s := p.1
  let ta := tanA s
  within s.vz.raw (3 * 65536) (12 * 65536) && within s.q.raw (-3000) 3000 && within s.rpm.raw (2300 * 65536) (3000 * 65536) &&
  within s.vx.raw (30 * 65536) (38 * 65536) && within ta 0 13000 && within p.2.eI (-20000) 10000 &&
  s.stall.raw == 0 && Ci.clearance + 65536 ≤ s.h.raw &&
  within (s.ah.raw - s.ah1.raw) (-1000) 1000 && within (s.au.raw - s.au1.raw) (-1000) 1000 &&
  within (s.vz.raw - s.pvz.raw) (-300) 300 && within (s.pvz.raw - s.pvz2.raw) (-300) 300

/-- Load factor predicted from α, airspeed and density (raw n): `0.004838 · ρ · V² · (tan α + 0.0578)`, a fit to
the law's escapes (`harness/LfData.lean`). It uses only the state's true kinematics, not the derivative fields. -/
def nEst (s : State) (ta : Int) : Int :=
  let rho := (Jsb.atmLookup Jsb.C172.atmRho s.h).raw
  let v2 := (s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw) / 65536
  rho * v2 / 65536 * (ta + 3789) / 65536 * 317 / 65536

/-- tan α a quarter second ahead: α̇ ≈ q − g (n − 1) / V. -/
def alphaAhead (s : State) (ta n : Int) : Int :=
  let v := max 65536 (speedRaw s)
  ta + (s.q.raw - Ci.gRaw * (n - 65536) / v) / 4

/-- Post-recovery set: climbing, fast enough, engine spooled up, moderate α, pitch rate and load factor, consistent
derivative and history fields. On every benchmark escape (stride 3) the law never descends again from these
states (`harness/LfData.lean`). -/
def recoverT (p : State × Mem) : Bool :=
  let s := p.1
  let ta := tanA s
  let v2 := s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw
  let vHi : Int := 62 * 65536
  let atLeast (v : Int) : Bool := v * v ≤ v2
  -- one of: climbing ≥ 0.5 m/s at ≥ 31 m/s with the engine spooled up (≥ 2000 rpm); climbing ≥ 2 m/s at ≥ 32 m/s
  -- with the engine above idle (≥ 800 rpm; zoom escapes start at idle); climbing ≥ 2.5 m/s at ≥ 29.5 m/s with
  -- ≥ 1000 rpm, or ≥ 0.5 m/s with ≥ 2200 rpm (slow escapes). Horizontal speed ≥ 30.5 (29 for the slow case) bounds the energy spent on a zoom.
  let spooled := 32768 ≤ s.vz.raw && 2000 * 65536 ≤ s.rpm.raw && atLeast (31 * 65536) && 1998848 ≤ s.vx.raw
  let fastIdle := 2 * 65536 ≤ s.vz.raw && 800 * 65536 ≤ s.rpm.raw && atLeast (32 * 65536) && 1998848 ≤ s.vx.raw
  let slowClimb := (163840 ≤ s.vz.raw && 1000 * 65536 ≤ s.rpm.raw || 32768 ≤ s.vz.raw && 2200 * 65536 ≤ s.rpm.raw) &&
    atLeast 1933312 && 29 * 65536 ≤ s.vx.raw
  -- energy floor V² ≥ 27.5² + 2·vz² (as in competitor wildcard's T): enough speed to push over above the floor
  let eLo : Int := 1802240
  (spooled || fastIdle || slowClimb) && eLo * eLo + 2 * (s.vz.raw * s.vz.raw) ≤ v2 &&
  s.vz.raw ≤ 40 * 65536 && s.rpm.raw ≤ 3000 * 65536 &&
  v2 ≤ vHi * vHi && within ta (-3932) 13107 &&
  within s.q.raw (-22938) 22938 && nRaw s ≤ 209715 && nEst s ta ≤ 203162 &&
  nEst s (alphaAhead s ta (nEst s ta)) ≤ 222822 && within p.2.eI (-22938) 9830 &&
  s.stall.raw == 0 && Ci.clearance + 32768 ≤ s.h.raw &&
  within (s.ah.raw - s.ah1.raw) (-32768) 32768 && within (s.au.raw - s.au1.raw) (-32768) 32768 &&
  within (s.vz.raw - s.pvz.raw) (-19661) 19661 && within (s.pvz.raw - s.pvz2.raw) (-19661) 19661

def law1 : Ci.Law :=
  { σ := Mem, name := "lawfirst-alpha", init := initP p1, step := stepP p1, inT := fun q => climbT q || recoverT q,
    enc := encM, dec := decM }

end Ci.Lawfirst
