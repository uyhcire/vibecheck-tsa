import Envelope3D.Relation

/-! Worst-case escape: a box recurrence checked tick by tick against the grid, ending in a climb-out. -/

namespace Envelope3D
variable {ι : Type}

structure Box where
  xlo : Rat
  xhi : Rat
  ylo : Rat
  yhi : Rat
  hLo : Rat
  vxlo : Rat
  vxhi : Rat
  vylo : Rat
  vyhi : Rat
  vzLo : Rat
  VLo : Rat
  bankHi : Rat
  deriving Repr

namespace Box

def point (s : State) : Box :=
  ⟨s.x, s.x, s.y, s.y, s.h, s.vx, s.vx, s.vy, s.vy, s.vz, s.V, absR s.bank⟩

def Contains (b : Box) (s : State) : Prop :=
  b.xlo ≤ s.x ∧ s.x ≤ b.xhi ∧ b.ylo ≤ s.y ∧ s.y ≤ b.yhi ∧ b.hLo ≤ s.h ∧
    b.vxlo ≤ s.vx ∧ s.vx ≤ b.vxhi ∧ b.vylo ≤ s.vy ∧ s.vy ≤ b.vyhi ∧ b.vzLo ≤ s.vz ∧
    b.VLo ≤ s.V ∧ absR s.bank ≤ b.bankHi

def Sub (b c : Box) : Prop :=
  c.xlo ≤ b.xlo ∧ b.xhi ≤ c.xhi ∧ c.ylo ≤ b.ylo ∧ b.yhi ≤ c.yhi ∧ c.hLo ≤ b.hLo ∧
    c.vxlo ≤ b.vxlo ∧ b.vxhi ≤ c.vxhi ∧ c.vylo ≤ b.vylo ∧ b.vyhi ≤ c.vyhi ∧ c.vzLo ≤ b.vzLo ∧
    c.VLo ≤ b.VLo ∧ b.bankHi ≤ c.bankHi

def NonInv (b : Box) : Prop :=
  b.xlo ≤ b.xhi ∧ b.ylo ≤ b.yhi ∧ b.vxlo ≤ b.vxhi ∧ b.vylo ≤ b.vyhi

end Box

def freeBox (P : Params ι) (u : ι) (s : State) : Box :=
  let f := P.free u
  let vxl := s.vx - P.dt * f.hAcc
  let vxh := s.vx + P.dt * f.hAcc
  let vyl := s.vy - P.dt * f.hAcc
  let vyh := s.vy + P.dt * f.hAcc
  let vzl := s.vz - f.vzDrop
  { xlo := s.x + P.dt * min s.vx vxl - P.pSlack
    xhi := s.x + P.dt * max s.vx vxh + P.pSlack
    ylo := s.y + P.dt * min s.vy vyl - P.pSlack
    yhi := s.y + P.dt * max s.vy vyh + P.pSlack
    hLo := s.h + P.dt * min s.vz vzl - P.hSlack
    vxlo := vxl, vxhi := vxh, vylo := vyl, vyhi := vyh, vzLo := vzl
    VLo := s.V - f.vDrop
    bankHi := absR s.bank + f.bankStep }

def freeRef (P : Params ι) (u : ι) (s : State) : Ref :=
  let f := P.free u
  ⟨s.vz - f.vzDrop, s.vz + f.vzRise, s.V - f.vDrop, absR s.bank + f.bankStep,
    s.vx - P.dt * f.hAcc, s.vx + P.dt * f.hAcc, s.vy - P.dt * f.hAcc, s.vy + P.dt * f.hAcc⟩

def escStep (P : Params ι) (R : Ref) (k : Nat) (σ' : Sched) (b : Box) : Box :=
  let vxl := scaleLo P R.vxlo - σ'.sp
  let vxh := scaleHi P R.vxhi + σ'.sp
  let vyl := scaleLo P R.vylo - σ'.sp
  let vyh := scaleHi P R.vyhi + σ'.sp
  { xlo := b.xlo + P.dt * min b.vxlo vxl - P.pSlack
    xhi := b.xhi + P.dt * max b.vxhi vxh + P.pSlack
    ylo := b.ylo + P.dt * min b.vylo vyl - P.pSlack
    yhi := b.yhi + P.dt * max b.vyhi vyh + P.pSlack
    hLo := b.hLo + P.dt * min b.vzLo σ'.vz - P.hSlack
    vxlo := vxl, vxhi := vxh, vylo := vyl, vyhi := vyh, vzLo := σ'.vz
    VLo := VFloor P R
    bankHi := bankCap P R (k + 1) }

def escIter (P : Params ι) (R : Ref) : Nat → Box → Sched → Nat → Box
  | _, b, _, 0 => b
  | k, b, σ, j + 1 =>
    let σ' := schedNext P R k σ
    escIter P R (k + 1) (escStep P R k σ' b) σ' j

def tickOK (P : Params ι) (b c : Box) : Bool :=
  decide (P.grid.maxOver (min b.xlo c.xlo) (max b.xhi c.xhi) (min b.ylo c.ylo) (max b.yhi c.yhi) +
    P.margin < min b.hLo c.hLo - P.sag)

def climbOutClear (P : Params ι) (b : Box) : Bool :=
  decide (P.grid.maxOver (b.xlo - P.climbR) (b.xhi + P.climbR) (b.ylo - P.climbR) (b.yhi + P.climbR) +
    P.margin < b.hLo - P.climbDrop - P.sag)

-- A landing terminal would be a second disjunct here, with its own mode and proof obligation.
def escDone (P : Params ι) (k : Nat) (b : Box) : Bool :=
  decide (P.delayTicks ≤ k) && decide (b.bankHi ≤ P.bankLevel) && decide (P.base.climb ≤ b.vzLo) &&
    climbOutClear P b

def escLoop (P : Params ι) (R : Ref) : Nat → Nat → Box → Sched → Bool
  | n, k, b, σ =>
    escDone P k b ||
      match n with
      | 0 => false
      | n + 1 =>
        let σ' := schedNext P R k σ
        let c := escStep P R k σ' b
        tickOK P b c && escLoop P R n (k + 1) c σ'

def escapeOK (P : Params ι) (R : Ref) (b : Box) : Bool :=
  decide (P.vMin + P.commitVMargin ≤ R.VLo) && decide (R.vzHi ≤ P.commitVzMax) &&
    escLoop P R P.horizon 0 b (sched P R 0)

def escapeClear (P : Params ι) (s : State) (u : ι) : Bool :=
  tickOK P (Box.point s) (freeBox P u s) && escapeOK P (freeRef P u s) (freeBox P u s)

def Init (P : Params ι) (s : State) : Prop := escapeOK P (Ref.ofState s) (Box.point s) = true

instance (P : Params ι) (s : State) : Decidable (Init P s) := by unfold Init; infer_instance

end Envelope3D
