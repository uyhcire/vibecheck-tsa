import Envelope.Escape

/-! The filter: a small mode machine around `escapeClear`. -/

namespace Envelope
variable {ι : Type}

/-- Mode for this tick: keep an escape; else pass `u` if its worst case keeps the escape clear, else escape. -/
def filter (P : Params ι) (m : Mode) (s : State) (u : ι) : Mode :=
  match m with
  | .escape k => .escape k
  | .free => if escapeClear P s u then .free else .escape 0

end Envelope
