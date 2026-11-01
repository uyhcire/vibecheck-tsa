import GateSafety.Parallel
import CityGate.Gate

/-! The city gate for a C host (`libcityjsb`, `c/citygate_abi.c`): one JSBSim frame of the gated closed loop per
call. `frameOut_fst` proves the next state is `cityGate.frame`, the frame `city_safe` is about; the candidates'
rollouts run in parallel (`GateSafety.frameP`, `Task.spawn`). -/

namespace CityGate
open GateSafety

/-- The closed-loop state: the aircraft, the proposal layer's memory, and the held controller. -/
abbrev GateState := Plane × (Mem × Ctl)

/-- One frame under the pilot's input `u`: the next closed-loop state, and `[applied elev, ail, rud, thr,
accepted (1 if a candidate was taken this frame, else 0), obs (22, `CityJsb.obs` layout), map x, y, z]`. -/
def frameOut (g : GateState) (u : Surf) : GateState × FloatArray :=
  let r := cityGate.frameP g u
  let a := r.2.2
  let p := r.1.1.pos
  (r.1, ⟨#[a.elev, a.ail, a.rud, a.thr, if r.2.1.isSome then 1 else 0] ++ r.1.1.ob.data ++ #[p.1, p.2.1, p.2.2]⟩)

/-- The host runs exactly the gate's frame. -/
theorem frameOut_fst (g : GateState) (u : Surf) : (frameOut g u).1 = cityGate.frame g u :=
  frameP_fst cityGate g u

@[export citygate_new_lean]
def newE (x y z v gam psi phi n thr : Float) : GateState := startState x y z v gam psi phi n thr

/-- The allowed-start check (`CityGate.Init`). -/
@[export citygate_start_ok_lean]
def startOkE (g : GateState) : Bool := cityGate.rolloutOK cityGate.horizon (cityGate.start g.1, g.1)

@[export citygate_frame_lean]
def frameE (g : GateState) (elev ail rud thr : Float) : GateState × FloatArray := frameOut g ⟨elev, ail, rud, thr⟩

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

end CityGate
