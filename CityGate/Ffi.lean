import GateSafety.Parallel
import CityGate.Gate

/-! The city gate for a C host (`libcityjsb`, `c/citygate_abi.c`): one JSBSim frame of the gated closed loop per
call. `frameOut_fst` proves the next state is `cityGate.frame`, the frame `city_safe` is about; the candidates'
rollouts run one after another or in parallel rounds (`chooseOut`). -/

namespace CityGate
open GateSafety

/-- The closed-loop state: the aircraft, the proposal layer's memory, and the held controller. -/
abbrev GateState := Plane × (Mem × Ctl)

/-- Frames per round when candidates are checked in rounds (`Gate.chooseR`). -/
def ROUND_FRAMES : Nat := 64

/-- The candidate chosen this frame. `par = 0`: one after another on this thread, stopping at the first that
verifies (`Gate.choose` itself). `par ≥ 1`: in rounds of `ROUND_FRAMES` frames, up to `par` candidates at once in
their own tasks, dropping candidates behind one that verified (`Gate.chooseR`). Either way it is `Gate.choose`. -/
def chooseOut (par : Nat) (g : GateState) (u : Surf) : Option Ctl :=
  if par = 0 then cityGate.choose g.1 g.2.1 g.2.2 u else cityGate.chooseR ROUND_FRAMES par g.1 g.2.1 g.2.2 u

theorem chooseOut_eq (par : Nat) (g : GateState) (u : Surf) : chooseOut par g u = cityGate.choose g.1 g.2.1 g.2.2 u := by
  unfold chooseOut; split
  · rfl
  · exact Gate.chooseR_eq _ _ _ _ _ _ _

/-- One frame under the pilot's input `u`: the next closed-loop state, and `[applied elev, ail, rud, thr,
accepted (1 if a candidate was taken this frame, else 0), obs (22, `CityJsb.obs` layout), map x, y, z]`. -/
def frameOut (par : Nat) (g : GateState) (u : Surf) : GateState × FloatArray :=
  let r := cityGate.frameWith (chooseOut par g u) g u
  let a := r.2.2
  let p := r.1.1.pos
  (r.1, ⟨#[a.elev, a.ail, a.rud, a.thr, if r.2.1.isSome then 1 else 0] ++ r.1.1.ob.data ++ #[p.1, p.2.1, p.2.2]⟩)

/-- The host runs exactly the gate's frame, however it checks the candidates. -/
theorem frameOut_fst (par : Nat) (g : GateState) (u : Surf) : (frameOut par g u).1 = cityGate.frame g u :=
  frameWith_fst cityGate _ g u (chooseOut_eq par g u)

@[export citygate_new_lean]
def newE (x y z v gam psi phi n thr : Float) : GateState := startState x y z v gam psi phi n thr

/-- The allowed-start check (`CityGate.Init`). -/
@[export citygate_start_ok_lean]
def startOkE (g : GateState) : Bool := cityGate.rolloutOK cityGate.horizon (cityGate.start g.1, g.1)

@[export citygate_frame_lean]
def frameE (g : GateState) (par : UInt32) (elev ail rud thr : Float) : GateState × FloatArray :=
  frameOut par.toNat g ⟨elev, ail, rud, thr⟩

/-- `predictPath` as `[x0, y0, z0, x1, …]`. -/
@[export citygate_path_lean]
def pathE (g : GateState) : FloatArray :=
  ⟨(predictPath g).foldl (fun a q => (a.push q.1).push q.2.1 |>.push q.2.2) #[]⟩

/-- The current observation and map position, `[obs (22), x, y, z]`, without stepping. -/
@[export citygate_obs_lean]
def obsE (g : GateState) : FloatArray := let p := g.1.pos; ⟨g.1.ob.data ++ #[p.1, p.2.1, p.2.2]⟩

/-- Filter off: one frame of the aircraft alone under `u`, outside the gate (nothing is proved about such frames).
Output as `frameE`, with `accepted` 0. -/
@[export citygate_bypass_lean]
def bypassE (g : GateState) (elev ail rud thr : Float) : GateState × FloatArray :=
  let s := g.1.step ⟨elev, ail, rud, thr⟩
  let p := s.pos
  ((s, g.2), ⟨#[elev, ail, rud, thr, 0] ++ s.ob.data ++ #[p.1, p.2.1, p.2.2]⟩)

/-- Filter back on: the closed loop starts afresh from the current aircraft, a new start (check it with `startOkE`). -/
@[export citygate_restart_lean]
def restartE (g : GateState) : GateState := (g.1, (cityGate.m₀, cityGate.start g.1))

/-- Tooling only (trace comparison): the proposal memory and the held controller, as numbers. -/
@[export citygate_trace_lean]
def traceE (g : GateState) : FloatArray :=
  let m := g.2.1
  let c := g.2.2
  let l := c.law
  let b := fun (x : Bool) => if x then (1 : Float) else 0
  ⟨#[m.frame.toFloat, b m.committed, m.runFrames.toFloat, m.sinceHandback.toFloat, m.rr.toFloat, m.prevDir,
    c.pilot.elev, c.pilot.ail, c.pilot.rud, c.pilot.thr, c.pf.toFloat, l.esc.toFloat, l.t, l.ia, l.ib, l.iphi,
    l.psiRef, l.axis, l.side, l.nextTry, b l.captured, c.lk.toFloat, c.hist.size.toFloat, c.psiPrev, c.extra,
    c.cap.toFloat]⟩

end CityGate
