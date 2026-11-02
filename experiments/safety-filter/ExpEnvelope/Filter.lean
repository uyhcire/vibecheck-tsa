import ExpEnvelope.Escape

/-! The filter: a small mode machine around `escapeClear`. -/

namespace ExpEnvelope
variable {ι : Type}

/-- Mode for this tick: pass `u` whenever its worst case keeps the escape clear (handing control back
from an escape); otherwise keep the committed escape, or commit one. -/
def filter (P : Params ι) (m : Mode) (s : State) (u : ι) : Mode :=
  if escapeClear P s u then .free
  else
    match m with
    | .escape k => .escape k
    | .free => .escape 0

end ExpEnvelope
