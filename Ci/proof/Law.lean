import Ci.lawfirst.Sub

/-! ci-proof: the lawfirst escape law (`Ci.Lawfirst.p1`) with two changes that make its climb-out smooth and
bounded, so that a terminal set around it can be proved:

1. the speed term of the α command is `kV · max(v − vC, −vBand)`, continuous, instead of lawfirst's switch to gain
   0 below `vC` (that switch sat right at the climb speed, so the climb dynamics had a kink on the climb itself);
2. the throttle comes back by 0.002 per metre above 2500 m, so the climb ends at a stable level-flight altitude
   (about 2620 m) instead of creeping up to the model's service ceiling.

All arithmetic is on raw `Fx` integers. -/

namespace Ci.Proof
open Vibecheck Jsb Ci.Lawfirst

/-- Speed deficit (raw m/s) below which the speed term stops growing. -/
def vBand : Int := 2 * 65536

/-- Altitude (raw) where the throttle starts to come back. -/
def hThr : Int := 2500 * 65536

/-- Throttle (raw): full up to `hThr`, then 0.002 per metre less, floored at idle. -/
def thrH (h : Int) : Int := clampI 0 65536 (65536 - max 0 (h - hThr) / 500)

/-- lawfirst's `alphaCmd` with the continuous speed term. -/
def alphaCmd (p : P) (s : State) : Int :=
  let ta := tanA s
  let v := speedRaw s
  let tg := tanG s
  let raw := p.aRef + p.kV * max (v - p.vC) (-vBand) / 65536 + p.kG * (p.gC - tg) / 65536 -
    p.kGL * max 0 (tg - p.gMax) / 65536
  let n := nRaw s
  let nL := if s.vz.raw > 0 && p.nLimUp ≥ 0 then p.nLimUp else p.nLim
  let aN := if n > 19661 && ta > p.a0 then p.a0 + (ta - p.a0) * nL / n else p.aMax
  clampI p.aMin (min p.aMax aN) raw

/-- lawfirst's `stepP` with the new α command and the scheduled throttle. -/
def stepP (p : P) (m : Mem) (s : State) : Input × Mem :=
  let ta := tanA s
  let ac := clampI (m.ac - p.rDn) (m.ac + p.rUp) (alphaCmd p s)
  let err := ac - ta
  let qRef := if p.qss then Ci.gRaw * (nRaw s - 65536) / max 65536 (speedRaw s) else 0
  let e := m.eI + p.kF * ac / 65536 + p.kA * err / 65536 - p.kQ * (s.q.raw - qRef) / 65536
  let eI' := clampI (-65536) 65536 (m.eI + p.kI * err / 65536)
  (⟨⟨clampI (-65536) 65536 e⟩, ⟨thrH s.h.raw⟩, ⟨0⟩, ⟨0⟩⟩, ⟨eI', ac⟩)

def step : Mem → State → Input × Mem := stepP p1

end Ci.Proof
