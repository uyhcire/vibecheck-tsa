import Jsb.Model

/-! Escape autopilot for the longitudinal c172p model: full throttle, pitch to a climb attitude that grows with
excess speed, pitch-rate damping, elevator rate-limited. Generic over `Scalar`, like the model. -/

namespace Jsb
open Vibecheck

variable {α : Type} [Scalar α]

/-- Closed-loop state: aircraft state and the elevator command applied on the previous tick. -/
structure CLOf (α : Type) where
  s : StateOf α
  elev : α

namespace Escape

/-- reference speed, m/s (raw) -/
def vRef : Int := 38 * 65536
/-- climb attitude `sin θ` at the reference speed (raw) -/
def dzRef : Int := 9830
/-- extra `sin θ` per m/s above the reference speed (raw) -/
def kV : Int := 1311
/-- elevator per unit `sin θ` error (raw) -/
def kTheta : Int := 4 * 65536
/-- elevator per rad/s of pitch rate (raw) -/
def kQ : Int := 98304
/-- elevator change limit per tick (raw) -/
def rate : Int := 4096

/-- Elevator the law asks for before rate limiting, clipped to [-1, 1]. -/
def target (s : StateOf α) : α :=
  let dzC := Scalar.lit dzRef + Scalar.lit kV * (s.vx - Scalar.lit vRef)
  max (-1) (min 1 (Scalar.lit kTheta * (dzC - s.dz) - Scalar.lit kQ * s.q))

/-- Rate-limited elevator command. -/
def command (c : CLOf α) : α :=
  c.elev + max (-Scalar.lit rate) (min (Scalar.lit rate) (target c.s - c.elev))

def input (c : CLOf α) : InputOf α := ⟨command c, 1, 0, 0⟩

/-- One closed-loop 1/16 s tick in escape mode. -/
def tick (c : CLOf α) : CLOf α := ⟨tickAB (input c) c.s, command c⟩

end Escape
end Jsb
