import Proofs.TermSound.Checks
import CityGate.TermSkeleton

/-! The TermSoundR skeleton's `Abs` with the rung-1 point mass: `Abs.DynAbstractInv` proved for helix and ray. -/

namespace Proofs.TermSound.Glue

open Complex CityGate CityGate.SpecBridge CityGate.TermSkeleton CitySafety.EndSets

noncomputable section

/-! ## The reading `π` -/

/-- An exact real from a double, if finite. -/
def realOf (f : Float) : Option ℝ := (CitySafety.ratOf f).map fun q => (q : ℝ)

/-- Track angle is from east (`arg (vE + i vN)`); `l` is `tan` of the bank. -/
def piSt (x : Ctl × Plane) : Option St := do
  let (px, py, pz) ← exactPos x.2
  let o := x.2.ob
  let vN ← realOf (Esc.obN o)
  let vE ← realOf (Esc.obE o)
  let vD ← realOf (Esc.obD o)
  let vt ← realOf o[6]!
  let phi ← realOf o[7]!
  pure ⟨(px : ℝ), (py : ℝ), (pz : ℝ), arg ⟨vE, vN⟩, vt, -vD, Real.tan phi⟩

/-! ## The disturbance -/

def diff (a b : St) : St := ⟨a.x - b.x, a.y - b.y, a.z - b.z, a.psi - b.psi, a.u - b.u, a.vz - b.vz, a.l - b.l⟩

theorem add_diff (a b : St) : b + diff a b = a := by
  obtain ⟨_, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _⟩ := b
  show St.mk _ _ _ _ _ _ _ = _
  simp only [diff, add_sub_cancel]

/-! ## The helix kind -/

/-- A helix tube's rung-1 constants: centre, entry altitude, centre slack at entry (`δ`), release altitude. -/
def c0Of (H : Helix) : ℂ := ⟨(H.cx : ℝ), (H.cy : ℝ)⟩

def dynHA (H : Helix) (s : St) : Prop :=
  0 ≤ (H.z0 : ℝ) ∧ (H.z0 : ℝ) ≤ H.zTop ∧ (H.zTop : ℝ) ≤ ZT ∧ DynH (c0Of H) H.z0 H.δ H.zTop s

def helixAbs (Fast : Helix → Ctl × Plane → Prop) : Abs Helix St where
  π := piSt
  F _ := stepHelix
  Near _ b a := Small (diff a b)
  DynA := dynHA
  Fast := Fast

/-- **`dyn_abstract_inv` for the helix kind, proved.** -/
theorem helixAbs_inv (Fast : Helix → Ctl × Plane → Prop) : (helixAbs Fast).DynAbstractInv := by
  intro H a a' ⟨h0, h1, h2, hd⟩ hn
  refine ⟨h0, h1, h2, ?_⟩
  have hn' : Small (diff a' (stepHelix a)) := hn
  have := dynH_robust h0 h1 h2 hd hn'
  rwa [add_diff] at this

/-! ## The ray kind, in the ray's own frame -/

/-- The ray's direction angle from east. -/
def angOf (R : Ray) : ℝ := arg ⟨(R.a : ℝ), (R.b : ℝ)⟩

def p0Of (R : Ray) : ℂ := ⟨(R.px : ℝ), (R.py : ℝ)⟩

/-- A map-frame state in the ray's frame: origin at its start, `x` along it, heading relative to it. -/
def toLocal (R : Ray) (s : St) : St :=
  let w := (pos s - p0Of R) * cis (-angOf R)
  ⟨w.re, w.im, s.z, s.psi - angOf R, s.u, s.vz, s.l⟩

def fromLocal (R : Ray) (s : St) : St :=
  let w := pos s * cis (angOf R) + p0Of R
  ⟨w.re, w.im, s.z, s.psi + angOf R, s.u, s.vz, s.l⟩

theorem cis_mul_neg (a : ℝ) : cis a * cis (-a) = 1 := by
  simp only [cis, ← Complex.exp_add]; push_cast; simp

theorem toLocal_fromLocal (R : Ray) (s : St) : toLocal R (fromLocal R s) = s := by
  obtain ⟨x, y, z, psi, u, vz, l⟩ := s
  have hp : pos (fromLocal R ⟨x, y, z, psi, u, vz, l⟩) = pos ⟨x, y, z, psi, u, vz, l⟩ * cis (angOf R) + p0Of R := by
    apply Complex.ext <;> simp [pos, fromLocal]
  have hw : (pos (fromLocal R ⟨x, y, z, psi, u, vz, l⟩) - p0Of R) * cis (-angOf R) = ⟨x, y⟩ := by
    rw [hp, add_sub_cancel_right, mul_assoc, cis_mul_neg, mul_one]; rfl
  simp only [toLocal, hw]
  show St.mk x y z (psi + angOf R - angOf R) u vz l = _
  rw [add_sub_cancel_right]

/-- `DynR` in the ray's frame (start at along-track 0), with `dynR_robust`'s side conditions. -/
def dynRA (R : Ray) (s : St) : Prop :=
  0 ≤ (R.z0 : ℝ) ∧ (R.z0 : ℝ) ≤ R.zTop ∧ (R.zTop : ℝ) ≤ ZT ∧ DynR 0 R.z0 R.w R.zTop (toLocal R s)

/-- The ray kind: the model step is `stepRay` in the ray's frame, the disturbance `Small` in that frame. -/
def rayAbs (Fast : Ray → Ctl × Plane → Prop) : Abs Ray St where
  π := piSt
  F R s := fromLocal R (stepRay (toLocal R s))
  Near R b a := Small (diff (toLocal R a) (toLocal R b))
  DynA := dynRA
  Fast := Fast

/-- **`dyn_abstract_inv` for the ray kind, proved.** -/
theorem rayAbs_inv (Fast : Ray → Ctl × Plane → Prop) : (rayAbs Fast).DynAbstractInv := by
  intro R a a' ⟨h0, h1, h2, hd⟩ hn
  refine ⟨h0, h1, h2, ?_⟩
  have hn' : Small (diff (toLocal R a') (stepRay (toLocal R a))) := by
    have := hn; simp only [rayAbs, toLocal_fromLocal] at this; exact this
  have := dynR_robust h0 h1 h2 hd hn'
  rwa [add_diff] at this

/-! ## The ends, and the headline with `dyn_abstract_inv` discharged -/

/-- Helix and ray kinds from rung 1; the street kind reuses the ray's model (a placeholder, as its tube does). -/
def glueEnds (FH : Helix → Ctl × Plane → Prop) (FR FS : Ray → Ctl × Plane → Prop) : Ends St :=
  ⟨helixAbs FH, rayAbs FR, rayAbs FS⟩

/-- `TermSoundR` with `dyn_abstract_inv` discharged by rung 1. -/
theorem termSoundR_glue (FH : Helix → Ctl × Plane → Prop) (FR FS : Ray → Ctl × Plane → Prop)
    (hRH : (helixAbs FH).ResidualBound) (hFH : (helixAbs FH).FastBounded) (hCH : (helixAbs FH).DynConf Helix.Conf)
    (hRR : (rayAbs FR).ResidualBound) (hFR : (rayAbs FR).FastBounded) (hCR : (rayAbs FR).DynConf Ray.Conf)
    (hRS : (rayAbs FS).ResidualBound) (hFS : (rayAbs FS).FastBounded) (hCS : (rayAbs FS).DynConf Ray.Conf)
    {T : Ctl × Plane → Bool} (hT : EndTestCertified (glueEnds FH FR FS) T) (hL : TermLink T) :
    GateSafety.TermSoundR cityGate (CrashH 7) GInit :=
  termSoundR_of (glueEnds FH FR FS)
    ⟨⟨helixAbs_inv FH, hRH, hFH, hCH⟩, ⟨rayAbs_inv FR, hRR, hFR, hCR⟩, ⟨rayAbs_inv FS, hRS, hFS, hCS⟩⟩ hT hL

/-! ## Non-vacuity: rung 1's trim states are members of `DynA` -/

theorem Rstar300 : Rstar 300 = ((8698805 / 44800 : ℚ) : ℝ) := by
  norm_num [Rstar, uStar, EH, ur, E1, g, lc]

def trimTube : Helix := ⟨0, 8698805 / 44800, 194, 0, 1 / 3, 300, 1000⟩

example : dynHA trimTube trimH := by
  have hc : c0Of trimTube = c0H := by
    apply Complex.ext
    · simp [c0Of, trimTube, c0H, centre, trimH, pos, cis]
    · have : c0H.im = Rstar 300 := by simp [c0H, centre, trimH, pos, cis]
      rw [this, Rstar300]; simp [c0Of, trimTube]
  refine ⟨by norm_num [trimTube], by norm_num [trimTube], by norm_num [trimTube, ZT], ?_⟩
  rw [hc]
  have := trimH_mem
  simpa [trimTube] using this

def eastTube : Ray := ⟨0, 0, 1, 0, 5, 0, 300, 0, 1000⟩

example : dynRA eastTube trimR := by
  have hl : toLocal eastTube trimR = trimR := by
    have ha : angOf eastTube = 0 := by
      simp only [angOf, eastTube, Rat.cast_one, Rat.cast_zero]
      exact Complex.arg_one
    simp only [toLocal, ha, neg_zero, sub_zero]
    have hp : p0Of eastTube = 0 := by apply Complex.ext <;> simp [p0Of, eastTube]
    rw [hp, sub_zero]
    simp [cis, pos, trimR]
  refine ⟨by norm_num [eastTube], by norm_num [eastTube], by norm_num [eastTube, ZT], ?_⟩
  rw [hl]
  simpa [eastTube] using trimR_mem

end

end Proofs.TermSound.Glue
