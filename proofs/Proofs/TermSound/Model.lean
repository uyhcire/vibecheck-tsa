import Proofs.TermSound.Quad

/-! Rung 1 point-mass model of the escape law's settled climbs; see `docs/termsound/rung1.md`. -/

namespace Proofs.TermSound

noncomputable section

def h : ℝ := 1 / 128
def g : ℝ := 49 / 5
def ur : ℝ := 35
def kD : ℝ := 1 / 20
def kG : ℝ := 5 / 2
def kV : ℝ := 7 / 10
def v0 : ℝ := 21 / 4
def E1 : ℝ := 7 / 4000
def tau : ℝ := 1 / 2

def ER : ℝ := -1 / 2
def EH : ℝ := -3 / 2

def uStar (E0 z : ℝ) : ℝ := ur + E0 - E1 * z
def vzStar (E0 z : ℝ) : ℝ := v0 + kV * (E0 - E1 * z)

def aZero (E0 : ℝ) : ℝ := g / ur * (v0 + kV * E0) + kD * E0
def aZ : ℝ := (kD + g * kV / ur) * E1

structure St where
  x : ℝ
  y : ℝ
  z : ℝ
  psi : ℝ
  u : ℝ
  vz : ℝ
  l : ℝ

instance : Add St := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z, a.psi + b.psi, a.u + b.u, a.vz + b.vz, a.l + b.l⟩⟩

@[simp] theorem St.add_x (a b : St) : (a + b).x = a.x + b.x := rfl
@[simp] theorem St.add_y (a b : St) : (a + b).y = a.y + b.y := rfl
@[simp] theorem St.add_z (a b : St) : (a + b).z = a.z + b.z := rfl
@[simp] theorem St.add_psi (a b : St) : (a + b).psi = a.psi + b.psi := rfl
@[simp] theorem St.add_u (a b : St) : (a + b).u = a.u + b.u := rfl
@[simp] theorem St.add_vz (a b : St) : (a + b).vz = a.vz + b.vz := rfl
@[simp] theorem St.add_l (a b : St) : (a + b).l = a.l + b.l := rfl

def accU (E0 : ℝ) (s : St) : ℝ := aZero E0 - aZ * s.z - kD * (s.u - ur) - g / ur * s.vz
def accVz (s : St) : ℝ := kG * (v0 + kV * (s.u - ur) - s.vz)

def dU : ℝ := 5 / 10 ^ 5
def dVZ : ℝ := 1 / 10 ^ 4
def dZ : ℝ := 1 / 10 ^ 4
def dL : ℝ := 1 / 10 ^ 5
def dPSI : ℝ := 1 / 10 ^ 6
def dP : ℝ := 1 / 10 ^ 4

def Small (d : St) : Prop :=
  |d.x| ≤ dP ∧ |d.y| ≤ dP ∧ |d.z| ≤ dZ ∧ |d.psi| ≤ dPSI ∧ |d.u| ≤ dU ∧ |d.vz| ≤ dVZ ∧ |d.l| ≤ dL

/-- `tan 29.7°`, the commanded bank of the 30° escapes (`ESC_BANK = 0.52`). -/
def lc : ℝ := 4 / 7

def omega (s : St) : ℝ := g * s.l / s.u
def radius (s : St) : ℝ := s.u ^ 2 / (g * s.l)
def cis (a : ℝ) : ℂ := Complex.exp (a * Complex.I)
def pos (s : St) : ℂ := ⟨s.x, s.y⟩

def stepHelix (s : St) : St :=
  let psi' := s.psi + h * omega s
  let p' := pos s + (radius s : ℂ) * Complex.I * (cis s.psi - cis psi')
  { x := p'.re, y := p'.im, z := s.z + h * s.vz, psi := psi', u := s.u + h * accU EH s,
    vz := s.vz + h * accVz s, l := s.l + h / tau * (lc - s.l) }

/-- `KPSI`; the law's ±0.15 clamp is inactive in `Dyn`. -/
def kChi : ℝ := 1

def stepRay (s : St) : St :=
  { x := s.x + h * s.u * Real.cos s.psi, y := s.y + h * s.u * Real.sin s.psi, z := s.z + h * s.vz,
    psi := s.psi + h * (g * s.l / s.u), u := s.u + h * accU ER s, vz := s.vz + h * accVz s,
    l := s.l + h / tau * (-kChi * s.psi - s.l) }

end

end Proofs.TermSound
