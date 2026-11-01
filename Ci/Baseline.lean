import Ci.Rules
import Jsb.Escape

/-! Reference submissions: the current escape law with a steady-climb box, and with a crude interior bound. -/

namespace Ci.Baseline
open Vibecheck Jsb

def escStep (m : Fx) (s : State) : Input × Fx :=
  let c : CLOf Fx := ⟨s, m⟩
  (Escape.input c, Escape.command c)

def within (x lo hi : Int) : Bool := lo ≤ x && x ≤ hi

/-- Raw-unit box around the steady climb (vx 40.4, vz 6.2 m/s). -/
def climbBox (p : State × Fx) : Bool :=
  let s := p.1
  within s.vx.raw 2600000 2700000 && within s.vz.raw 340000 470000 &&
  within s.dz.raw 11500 15500 && within s.q.raw (-2000) 2000 && within p.2.raw (-30000) 0 &&
  within s.rpm.raw (2400 * 65536) (3000 * 65536) && s.stall.raw == 0 && Ci.clearance ≤ s.h.raw &&
  within (s.ah.raw - s.ah1.raw) (-1000) 1000 && within (s.au.raw - s.au1.raw) (-1000) 1000 &&
  within (s.vz.raw - s.pvz.raw) (-300) 300 && within (s.pvz.raw - s.pvz2.raw) (-300) 300

def encFx (m : Fx) : Array Int := #[m.raw]
def decFx (a : Array Int) : Option Fx := if a.size == 1 then some ⟨a[0]!⟩ else none

def boxLaw : Ci.Law :=
  { σ := Fx, name := "escape+climbbox", init := fun c => c.pilot.elev, step := escStep, inT := climbBox,
    enc := encFx, dec := decFx }

def box : Ci.Submission := { name := "baseline-box", laws := [boxLaw], horizon := 640 }

/-- Box-baseline worst loss (raw m, -1 = some throttle rejected) at typical-grid node (V = 30 + 3i, γ = -0.5 + 0.1j),
index 8i + j; regenerate with `ciscore --fit`. -/
def lossTbl : Array Int := #[2192425, 1842104, 1536885, 1265357, 1036536, 854560, 699674, 582613, 1976255, 1576555, 1204647, 876320, 607508, 389128, 185871, 9748, 1846577, 1405837, 991310, 617653, 295802, 57785, 0, 0, 1790952, 1334108, 907231, 524852, 204574, 344, 0, 0, 1792175, 1314474, 879656, 500629, 190864, 366, 0, 0, 1808248, 1324566, 883063, 499439, 194235, 338, 0, 0, -1, 1345861, 896362, 510908, 201137, 299, 0, 0, -1, -1, 916687, 524206, 207637, 264, 0, 0, -1, -1, -1, 537978, 213090, 247, 0, 0, -1, -1, -1, -1, -1, 233, 0, 0, -1, -1, -1, -1, -1, -1, 0, 0]

def tanG : Array Int := #[-35802, -27708, -20273, -13285, -6576, 0, 6576, 13285]

def kNum : Int := 2
def marginH : Int := 30 * 65536

/-- Cell of the current (V, γ) on the typical grid: the lower-left node indices. -/
def cell (s : State) : Option (Nat × Nat) := Id.run do
  let v2 := s.vx.raw * s.vx.raw + s.vz.raw * s.vz.raw
  let mut iv : Option Nat := none
  for i in [0:10] do
    let a : Int := (30 + 3 * i) * 65536
    if a * a ≤ v2 && v2 < (a + 3 * 65536) * (a + 3 * 65536) then iv := some i
  let mut ig : Option Nat := none
  for j in [0:7] do
    if tanG[j]! * s.vx.raw ≤ s.vz.raw * 65536 && s.vz.raw * 65536 < tanG[j + 1]! * s.vx.raw then ig := some j
  match iv, ig with
  | some i, some j => some (i, j)
  | _, _ => none

/-- Crude interior: `h ≥ kNum · (worst loss of the 4 surrounding nodes) + marginH + clearance`, guards: α ≤ 0.2, |q| ≤ 0.3, V < 48, rpm ≥ 600. -/
def interiorT (p : State × Fx) : Bool :=
  let s := p.1
  match cell s with
  | none => false
  | some (i, j) =>
    let ls := [lossTbl[8 * i + j]!, lossTbl[8 * i + j + 1]!, lossTbl[8 * (i + 1) + j]!, lossTbl[8 * (i + 1) + j + 1]!]
    let u := s.vx.raw * s.dx.raw + s.vz.raw * s.dz.raw
    let w := s.vx.raw * s.dz.raw - s.vz.raw * s.dx.raw
    ls.all (· ≥ 0) && s.stall.raw == 0 && 600 * 65536 ≤ s.rpm.raw && within s.q.raw (-19661) 19661 && within p.2.raw (-65536) 65536 &&
    0 < u && w * 65536 ≤ 13286 * u && i + 1 ≤ 5 &&
    within (s.ah.raw - s.ah1.raw) (-6554) 6554 && within (s.au.raw - s.au1.raw) (-6554) 6554 &&
    within (s.vz.raw - s.pvz.raw) (-3277) 3277 && within (s.pvz.raw - s.pvz2.raw) (-3277) 3277 &&
    kNum * ls.foldl max 0 + marginH + Ci.clearance ≤ s.h.raw

def interiorLaw : Ci.Law :=
  { boxLaw with name := "escape+climbbox+interior", inT := fun p => climbBox p || interiorT p }

def interior : Ci.Submission := { name := "baseline-interior", laws := [interiorLaw], horizon := 640 }

end Ci.Baseline
