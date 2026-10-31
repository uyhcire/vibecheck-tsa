import Jsb.Model
import Jsb.IntervalSound
import Jsb.KernelRfl

/-! Enclosure theorem for the model, via the paired instance `Enc` whose ops project to `Fx` and `Iv` ops. -/

namespace Jsb
open Vibecheck

structure Enc where
  v : Fx
  i : Iv
  h : i.Mem v

instance : Scalar Enc where
  add a b := ⟨instScalarFx.add a.v b.v, Iv.add a.i b.i, Iv.add_sound a.h b.h⟩
  sub a b := ⟨instScalarFx.sub a.v b.v, Iv.sub a.i b.i, Iv.sub_sound a.h b.h⟩
  neg a := ⟨instScalarFx.neg a.v, Iv.neg a.i, Iv.neg_sound a.h⟩
  mul a b := ⟨instScalarFx.mul a.v b.v, Iv.mul a.i b.i, Iv.mul_sound a.h b.h⟩
  div a b := ⟨instScalarFx.div a.v b.v, Iv.div a.i b.i, Iv.div_sound a.h b.h⟩
  max a b := ⟨instScalarFx.max a.v b.v, Iv.max a.i b.i, Iv.max_sound a.h b.h⟩
  min a b := ⟨instScalarFx.min a.v b.v, Iv.min a.i b.i, Iv.min_sound a.h b.h⟩
  lit r := ⟨instScalarFx.lit r, Iv.lit r, Iv.lit_sound r⟩
  mulR a b := ⟨instScalarFx.mulR a.v b.v, Iv.mulR a.i b.i, Iv.mulR_sound a.h b.h⟩
  shr a k := ⟨instScalarFx.shr a.v k, Iv.shr a.i k, Iv.shr_sound a.h k⟩
  ab3 a b c := ⟨instScalarFx.ab3 a.v b.v c.v, Iv.ab3 a.i b.i c.i, Iv.ab3_sound a.h b.h c.h⟩
  abs a := ⟨instScalarFx.abs a.v, Iv.abs a.i, Iv.abs_sound a.h⟩
  sqrt a := ⟨instScalarFx.sqrt a.v, Iv.sqrt a.i, Iv.sqrt_sound a.h⟩
  atan2 a b := ⟨instScalarFx.atan2 a.v b.v, Iv.atan2 a.i b.i, Iv.atan2_sound a.h b.h⟩
  tbl1 t a := ⟨instScalarFx.tbl1 t a.v, Iv.tbl1 t a.i, Iv.tbl1_sound t a.h⟩
  tbl2 t a b := ⟨instScalarFx.tbl2 t a.v b.v, Iv.tbl2 t a.i b.i, Iv.tbl2_sound t a.h b.h⟩
  atm t a := ⟨instScalarFx.atm t a.v, Iv.atm t a.i, Iv.atm_sound t a.h⟩
  selLt a b t e := ⟨instScalarFx.selLt a.v b.v t.v e.v, Iv.selLt a.i b.i t.i e.i, Iv.selLt_sound a.h b.h t.h e.h⟩
  selLe a b t e := ⟨instScalarFx.selLe a.v b.v t.v e.v, Iv.selLe a.i b.i t.i e.i, Iv.selLe_sound a.h b.h t.h e.h⟩
  rnC a b := ⟨instScalarFx.rnC a.v b.v, Iv.rnC a.i b.i, Iv.rnC_sound a.h b.h⟩
  rnS a b := ⟨instScalarFx.rnS a.v b.v, Iv.rnS a.i b.i, Iv.rnS_sound a.h b.h⟩

def StateOf.map {α β : Type} (f : α → β) (s : StateOf α) : StateOf β :=
  ⟨f s.x, f s.h, f s.vx, f s.vz, f s.dx, f s.dz, f s.q, f s.rpm, f s.tmap, f s.udot, f s.wdot, f s.stall,
   f s.ah, f s.au, f s.qd, f s.ah1, f s.au1, f s.pvz, f s.pvz2⟩

def InputOf.map {α β : Type} (f : α → β) (u : InputOf α) : InputOf β := ⟨f u.elev, f u.thr, f u.beta, f u.phi⟩

def StateOf.Mem (S : StateOf Iv) (s : StateOf Fx) : Prop :=
  S.x.Mem s.x ∧ S.h.Mem s.h ∧ S.vx.Mem s.vx ∧ S.vz.Mem s.vz ∧ S.dx.Mem s.dx ∧ S.dz.Mem s.dz ∧ S.q.Mem s.q ∧
  S.rpm.Mem s.rpm ∧ S.tmap.Mem s.tmap ∧ S.udot.Mem s.udot ∧ S.wdot.Mem s.wdot ∧ S.stall.Mem s.stall ∧
  S.ah.Mem s.ah ∧ S.au.Mem s.au ∧ S.qd.Mem s.qd ∧ S.ah1.Mem s.ah1 ∧ S.au1.Mem s.au1 ∧ S.pvz.Mem s.pvz ∧
  S.pvz2.Mem s.pvz2

def InputOf.Mem (U : InputOf Iv) (u : InputOf Fx) : Prop :=
  U.elev.Mem u.elev ∧ U.thr.Mem u.thr ∧ U.beta.Mem u.beta ∧ U.phi.Mem u.phi

def StateOf.zip (s : StateOf Fx) (S : StateOf Iv) (h : S.Mem s) : StateOf Enc :=
  ⟨⟨s.x, S.x, h.1⟩, ⟨s.h, S.h, h.2.1⟩, ⟨s.vx, S.vx, h.2.2.1⟩, ⟨s.vz, S.vz, h.2.2.2.1⟩, ⟨s.dx, S.dx, h.2.2.2.2.1⟩,
   ⟨s.dz, S.dz, h.2.2.2.2.2.1⟩, ⟨s.q, S.q, h.2.2.2.2.2.2.1⟩, ⟨s.rpm, S.rpm, h.2.2.2.2.2.2.2.1⟩,
   ⟨s.tmap, S.tmap, h.2.2.2.2.2.2.2.2.1⟩, ⟨s.udot, S.udot, h.2.2.2.2.2.2.2.2.2.1⟩,
   ⟨s.wdot, S.wdot, h.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨s.stall, S.stall, h.2.2.2.2.2.2.2.2.2.2.2.1⟩,
   ⟨s.ah, S.ah, h.2.2.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨s.au, S.au, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
   ⟨s.qd, S.qd, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨s.ah1, S.ah1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
   ⟨s.au1, S.au1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨s.pvz, S.pvz, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
   ⟨s.pvz2, S.pvz2, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩⟩

def InputOf.zip (u : InputOf Fx) (U : InputOf Iv) (h : U.Mem u) : InputOf Enc :=
  ⟨⟨u.elev, U.elev, h.1⟩, ⟨u.thr, U.thr, h.2.1⟩, ⟨u.beta, U.beta, h.2.2.1⟩, ⟨u.phi, U.phi, h.2.2.2⟩⟩

theorem StateOf.mem_of (e : StateOf Enc) : (e.map Enc.i).Mem (e.map Enc.v) :=
  ⟨e.x.h, e.h.h, e.vx.h, e.vz.h, e.dx.h, e.dz.h, e.q.h, e.rpm.h, e.tmap.h, e.udot.h, e.wdot.h, e.stall.h,
   e.ah.h, e.au.h, e.qd.h, e.ah1.h, e.au1.h, e.pvz.h, e.pvz2.h⟩

theorem iter_comm {β γ : Type} (n : Nat) (f : β → β) (g : γ → γ) (p : β → γ) (hf : ∀ x, p (f x) = g (p x))
    (x : β) : p (iter n f x) = iter n g (p x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [iter]; rw [ih, hf]

theorem step_v (k : Nat) (ab : Bool) (u : InputOf Enc) (e : StateOf Enc) :
    (step k ab u e).map Enc.v = step k ab (u.map Enc.v) (e.map Enc.v) := by
  cases ab <;> kernel_rfl

theorem step_i (k : Nat) (ab : Bool) (u : InputOf Enc) (e : StateOf Enc) :
    (step k ab u e).map Enc.i = step k ab (u.map Enc.i) (e.map Enc.i) := by
  cases ab <;> kernel_rfl

theorem step_sound (k : Nat) (ab : Bool) {u : InputOf Fx} {U : InputOf Iv} {s : StateOf Fx} {S : StateOf Iv}
    (hu : U.Mem u) (hs : S.Mem s) : (step k ab U S).Mem (step k ab u s) := by
  have h := StateOf.mem_of (step k ab (u.zip U hu) (s.zip S hs))
  rwa [step_v, step_i] at h

theorem iter_step_sound (n k : Nat) (ab : Bool) {u : InputOf Fx} {U : InputOf Iv} (hu : U.Mem u) :
    ∀ {s : StateOf Fx} {S : StateOf Iv}, S.Mem s → (iter n (step k ab U) S).Mem (iter n (step k ab u) s) := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (step_sound k ab hu h)

theorem tickAB_sound {u : InputOf Fx} {U : InputOf Iv} {s : StateOf Fx} {S : StateOf Iv}
    (hu : U.Mem u) (hs : S.Mem s) : (tickAB U S).Mem (tickAB u s) :=
  iter_step_sound 8 7 true hu hs

end Jsb
