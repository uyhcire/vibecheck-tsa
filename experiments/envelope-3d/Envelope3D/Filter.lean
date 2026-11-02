import Envelope3D.Escape

/-! The filter: a small mode machine around `escapeClear`, with hand-back. -/

namespace Envelope3D
variable {ι : Type}

def escMode (P : Params ι) (k : Nat) (ref s : State) : Mode :=
  if escDone P k (Box.point s) then .climbOut s else .escape k ref

def filter (P : Params ι) (m : Mode) (s : State) (u : ι) : Mode :=
  if escapeClear P s u then .free
  else
    match m with
    | .free => escMode P 0 s s
    | .escape k ref => escMode P k ref s
    | .climbOut c => .climbOut c

end Envelope3D
