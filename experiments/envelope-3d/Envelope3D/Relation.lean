import Envelope3D.Params

/-! The 3D envelope relation; escape clauses bound the state against the commit state `ref`. -/

namespace Envelope3D
variable {ι : Type}

structure Ref where
  vzLo : Rat
  vzHi : Rat
  VLo : Rat
  bankHi : Rat
  vxlo : Rat
  vxhi : Rat
  vylo : Rat
  vyhi : Rat
  deriving Repr

def Ref.ofState (s : State) : Ref :=
  ⟨s.vz, s.vz, s.V, absR s.bank, s.vx, s.vx, s.vy, s.vy⟩

def Ref.Within (R' R : Ref) : Prop :=
  R.vzLo ≤ R'.vzLo ∧ R'.vzHi ≤ R.vzHi ∧ R.VLo ≤ R'.VLo ∧ R'.bankHi ≤ R.bankHi ∧
    R.vxlo ≤ R'.vxlo ∧ R'.vxhi ≤ R.vxhi ∧ R.vylo ≤ R'.vylo ∧ R'.vyhi ≤ R.vyhi

def VFloor (P : Params ι) (R : Ref) : Rat :=
  max P.vMin (R.VLo - P.escVDrop - P.noseHighVDrop * max 0 R.vzHi)

def climbOf (P : Params ι) (R : Ref) : Rat := (P.perf (VFloor P R)).climb

def bankCap (P : Params ι) (R : Ref) (j : Nat) : Rat :=
  max P.bankLevel (R.bankHi + P.bankGrow - P.rollStep * ((j - P.delayTicks : Nat) : Rat))

def pullAt (P : Params ι) (R : Ref) (k : Nat) : Rat :=
  if bankCap P R k ≤ P.bankLevel then (P.perf (VFloor P R)).pull else P.rollPull

structure Sched where
  vz : Rat
  sp : Rat
  deriving Repr

def schedNext (P : Params ι) (R : Ref) (k : Nat) (σ : Sched) : Sched :=
  ⟨if k < P.delayTicks then σ.vz else min (climbOf P R) (σ.vz + P.dt * pullAt P R k),
    σ.sp + P.dt * P.latAcc (bankCap P R k)⟩

def sched (P : Params ι) (R : Ref) : Nat → Sched
  | 0 => ⟨R.vzLo - P.delayVzDrop, P.velSlack⟩
  | j + 1 => schedNext P R j (sched P R j)

def scaleLo (P : Params ι) (v : Rat) : Rat := min (P.gsLo * v) (P.gsHi * v)
def scaleHi (P : Params ι) (v : Rat) : Rat := max (P.gsLo * v) (P.gsHi * v)

def Common (P : Params ι) (s s' : State) : Prop :=
  absR s'.vx ≤ P.vgMax ∧ absR s'.vy ≤ P.vgMax ∧
  s.x + P.dt * min s.vx s'.vx - P.pSlack ≤ s'.x ∧ s'.x ≤ s.x + P.dt * max s.vx s'.vx + P.pSlack ∧
  s.y + P.dt * min s.vy s'.vy - P.pSlack ≤ s'.y ∧ s'.y ≤ s.y + P.dt * max s.vy s'.vy + P.pSlack ∧
  s.h + P.dt * min s.vz s'.vz - P.hSlack ≤ s'.h

def ModeOK (P : Params ι) : Mode → State → ι → State → Prop
  | .free, s, u, s' =>
    absR (s'.vx - s.vx) ≤ P.dt * (P.free u).hAcc ∧ absR (s'.vy - s.vy) ≤ P.dt * (P.free u).hAcc ∧
    s.vz - (P.free u).vzDrop ≤ s'.vz ∧ s'.vz ≤ s.vz + (P.free u).vzRise ∧
    s.V - (P.free u).vDrop ≤ s'.V ∧ absR (s'.bank - s.bank) ≤ (P.free u).bankStep
  | .escape k ref, _, _, s' =>
    (sched P (Ref.ofState ref) (k + 1)).vz ≤ s'.vz ∧ VFloor P (Ref.ofState ref) ≤ s'.V ∧
    absR s'.bank ≤ bankCap P (Ref.ofState ref) (k + 1) ∧
    scaleLo P ref.vx - (sched P (Ref.ofState ref) (k + 1)).sp ≤ s'.vx ∧
    s'.vx ≤ scaleHi P ref.vx + (sched P (Ref.ofState ref) (k + 1)).sp ∧
    scaleLo P ref.vy - (sched P (Ref.ofState ref) (k + 1)).sp ≤ s'.vy ∧
    s'.vy ≤ scaleHi P ref.vy + (sched P (Ref.ofState ref) (k + 1)).sp
  | .climbOut c, _, _, s' =>
    absR (s'.x - c.x) ≤ P.climbR ∧ absR (s'.y - c.y) ≤ P.climbR ∧ c.h - P.climbDrop ≤ s'.h ∧
    P.climbVz ≤ s'.vz

def Allowed (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) : Prop :=
  Common P s s' ∧ ModeOK P m s u s'

def monitor (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) : Bool :=
  let common :=
    decide (absR s'.vx ≤ P.vgMax) && decide (absR s'.vy ≤ P.vgMax) &&
    decide (s.x + P.dt * min s.vx s'.vx - P.pSlack ≤ s'.x) &&
    decide (s'.x ≤ s.x + P.dt * max s.vx s'.vx + P.pSlack) &&
    decide (s.y + P.dt * min s.vy s'.vy - P.pSlack ≤ s'.y) &&
    decide (s'.y ≤ s.y + P.dt * max s.vy s'.vy + P.pSlack) &&
    decide (s.h + P.dt * min s.vz s'.vz - P.hSlack ≤ s'.h)
  let mode := match m with
    | .free =>
      decide (absR (s'.vx - s.vx) ≤ P.dt * (P.free u).hAcc) &&
      decide (absR (s'.vy - s.vy) ≤ P.dt * (P.free u).hAcc) &&
      decide (s.vz - (P.free u).vzDrop ≤ s'.vz) && decide (s'.vz ≤ s.vz + (P.free u).vzRise) &&
      decide (s.V - (P.free u).vDrop ≤ s'.V) && decide (absR (s'.bank - s.bank) ≤ (P.free u).bankStep)
    | .escape k ref =>
      let R := Ref.ofState ref
      let σ := sched P R (k + 1)
      decide (σ.vz ≤ s'.vz) && decide (VFloor P R ≤ s'.V) && decide (absR s'.bank ≤ bankCap P R (k + 1)) &&
      decide (scaleLo P ref.vx - σ.sp ≤ s'.vx) && decide (s'.vx ≤ scaleHi P ref.vx + σ.sp) &&
      decide (scaleLo P ref.vy - σ.sp ≤ s'.vy) && decide (s'.vy ≤ scaleHi P ref.vy + σ.sp)
    | .climbOut c =>
      decide (absR (s'.x - c.x) ≤ P.climbR) && decide (absR (s'.y - c.y) ≤ P.climbR) &&
      decide (c.h - P.climbDrop ≤ s'.h) && decide (P.climbVz ≤ s'.vz)
  common && mode

theorem monitor_iff (P : Params ι) (m : Mode) (s : State) (u : ι) (s' : State) :
    monitor P m s u s' = true ↔ Allowed P m s u s' := by
  cases m <;> simp [monitor, Allowed, Common, ModeOK, and_assoc]

end Envelope3D
