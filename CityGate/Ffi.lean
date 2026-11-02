import GateSafety.Parallel
import CityGate.Probe

/-! The city gate for a C host (`libcityjsb`, `c/citygate_abi.c`): one JSBSim frame of the gated closed loop per
call, on the default city or on a map the host passes in (`siteNewE`, San Francisco). `frameOut_fst` proves the
next state is `(gateOn S).frame`, the frame `city_safe` (default city) and `site_safe` (any map) are about; the
candidates' rollouts run one after another or in parallel rounds (`chooseOut`). -/

namespace CityGate
open GateSafety

/-- The closed-loop state: the aircraft, the proposal layer's memory, and the held controller. -/
abbrev GateState := Plane × (Mem × Ctl)

/-- The candidate chosen this frame. `par = 0`: one after another on this thread, stopping at the first that
verifies (`Gate.choose` itself). `par ≥ 1`: in rounds of `round` frames, up to `par` candidates at once in
their own tasks, dropping candidates behind one that verified (`Gate.chooseR`). Either way it is `Gate.choose`. -/
def chooseOut (S : Site) (par round : Nat) (g : GateState) (u : Surf) : Option Ctl :=
  if par = 0 then (gateOn S).choose g.1 g.2.1 g.2.2 u else (gateOn S).chooseR round par g.1 g.2.1 g.2.2 u

theorem chooseOut_eq (S : Site) (par round : Nat) (g : GateState) (u : Surf) :
    chooseOut S par round g u = (gateOn S).choose g.1 g.2.1 g.2.2 u := by
  unfold chooseOut; split
  · rfl
  · exact Gate.chooseR_eq _ _ _ _ _ _ _

/-- One frame under the pilot's input `u`: the next closed-loop state, and `[applied elev, ail, rud, thr,
accepted (1 if a candidate was taken this frame, else 0), obs (22, `CityJsb.obs` layout), map x, y, z]`. -/
def frameOut (S : Site) (par round : Nat) (g : GateState) (u : Surf) : GateState × FloatArray :=
  let r := (gateOn S).frameWith (chooseOut S par round g u) g u
  let a := r.2.2
  let p := r.1.1.pos
  (r.1, ⟨#[a.elev, a.ail, a.rud, a.thr, if r.2.1.isSome then 1 else 0] ++ r.1.1.ob.data ++ #[p.1, p.2.1, p.2.2]⟩)

/-- The host runs exactly the gate's frame, however it checks the candidates. -/
theorem frameOut_fst (S : Site) (par round : Nat) (g : GateState) (u : Surf) :
    (frameOut S par round g u).1 = (gateOn S).frame g u :=
  frameWith_fst (gateOn S) _ g u (chooseOut_eq S par round g u)

/-! ### Maps -/

/-- The default city. -/
@[export citygate_grid_site_lean]
def gridSiteE (_ : Unit) : Site := gridSite

/-- The exact rational value of a finite double (0 for NaN or an infinity, which `siteOf` rejects first). -/
def ratF (f : Float) : Rat := (CitySafety.ratOf f).getD 0

/-- `ratF` without `ratOf`'s `2 ^ 1075`. -/
def ratFFast (f : Float) : Rat := ((decN f.toBits).map fun x => sgn x.1 (VcFilter.dyadic x.2.1 x.2.2)).getD 0

@[csimp] theorem ratF_eq_fast : @ratF = @ratFFast := by
  funext f; simp only [ratF, ratFFast, ratOf_eq, ratOfBits_decN]

/-- A map from the host (`World` in `flight/src/world.rs`, via `flight/src/leangate.rs`): the rectangle
`[x0, x1] × [y0, y1]` (`x0`, `y0` whole metres), its terrain vertex heights (`tnx × tny`, 20 m apart from
`(x0, y0)`, row-major), its buildings as boxes (6 numbers each: x min, y min, x max, y max, z min, z max; for San
Francisco the boxes covering its prisms, `flight/src/covering.rs`), and its 2.5 m raster (`rnx × rny` cells,
row-major) and top, for the end-of-escape test. The doubles are read exactly; the box index has 16 m cells. `none`
if a number is not finite, the corner is not whole metres, or a size does not match. -/
def siteOf (x0 y0 x1 y1 : Float) (tnx tny : Nat) (terr boxes : FloatArray) (rnx rny : Nat) (raster : FloatArray)
    (top : Float) : Option Site := do
  let fin := fun (f : Float) => !f.isNaN && !f.isInf
  unless fin x0 && fin y0 && x0.floor == x0 && y0.floor == y0 && x0.abs < 1e6 && y0.abs < 1e6 do failure
  unless terr.size == tnx * tny && boxes.size % 6 == 0 && raster.size == rnx * rny do failure
  unless terr.data.all fin && boxes.data.all fin do failure
  let gx0 : Int := (ratF x0).floor
  let gy0 : Int := (ratF y0).floor
  let nb := boxes.size / 6
  let fb : Nat → Box Float := fun k =>
    ⟨boxes[6 * k]!, boxes[6 * k + 1]!, boxes[6 * k + 2]!, boxes[6 * k + 3]!, boxes[6 * k + 4]!, boxes[6 * k + 5]!⟩
  let M : GateMap := ⟨gx0, gy0, tnx, tny, nb, fun k => (fb k).map ratF, terr.data.map ratF⟩
  let I : CellIndex := ⟨16 * gx0, 16 * gy0, (tnx - 1) * 20 / 16 + 1, (tny - 1) * 20 / 16 + 1, 256⟩
  let bs := (List.range nb).map fun k => roundOutF (fb k)
  have hb : bs = M.boxesI := by simp only [bs, M, GateMap.boxesI, roundOutF_eq]; rfl
  if h : 2 ≤ M.nx ∧ 2 ≤ M.ny ∧ 0 < I.cx ∧ 0 < I.cy then
    some ⟨GateGeo.ofBoxesI M I bs hb h.1 h.2.1 h.2.2.1 h.2.2.2 (by simp [I]), ⟨x0, y0, x1, y1, rnx, rny, raster, top⟩⟩
  else none

@[export citygate_site_new_lean]
def siteNewE (x0 y0 x1 y1 : Float) (tnx tny : UInt32) (terr boxes : FloatArray) (rnx rny : UInt32)
    (raster : FloatArray) (top : Float) : Option Site :=
  siteOf x0 y0 x1 y1 tnx.toNat tny.toNat terr boxes rnx.toNat rny.toNat raster top

/-! ### The closed loop -/

@[export citygate_new_lean]
def newE (S : Site) (x y z v gam psi phi n thr : Float) : GateState := startStateOn S x y z v gam psi phi n thr

/-- The allowed-start check (`CityGate.InitOn`). -/
@[export citygate_start_ok_lean]
def startOkE (S : Site) (g : GateState) : Bool := (gateOn S).rolloutOK (gateOn S).horizon ((gateOn S).start g.1, g.1)

@[export citygate_frame_lean]
def frameE (S : Site) (g : GateState) (par round : UInt32) (elev ail rud thr : Float) : GateState × FloatArray :=
  frameOut S par.toNat round.toNat g ⟨elev, ail, rud, thr⟩

/-- `predictPath` as `[x0, y0, z0, x1, …]`. -/
@[export citygate_path_lean]
def pathE (S : Site) (g : GateState) : FloatArray :=
  ⟨(predictPathOn S g).foldl (fun a q => (a.push q.1).push q.2.1 |>.push q.2.2) #[]⟩

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
def restartE (S : Site) (g : GateState) : GateState := (g.1, ((gateOn S).m₀, (gateOn S).start g.1))

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

/-- Tooling only: a rollout check's verdict and the frames it flies. -/
def countRoll (G : Gate Plane Surf Ctl Mem) : Nat → Ctl × Plane → Nat → Bool × Nat
  | 0, x, k => (G.clear x && G.term x, k)
  | n + 1, x, k =>
    if !G.clear x then (false, k) else if G.term x then (true, k)
    else countRoll G n (G.fly x) (k + 1)

/-- Tooling only: the plant frames this gate frame steps when it checks candidates one after another (its own
frame included), and in the low 32 bits instead of the high ones the longest rollout up to the first that verifies
(the critical path when all candidates run at once). -/
@[export citygate_frames_lean]
def framesE (S : Site) (g : GateState) (elev ail rud thr : Float) : UInt64 :=
  let G := gateOn S
  let cs := G.propose g.2.1 g.1 g.2.2 ⟨elev, ail, rud, thr⟩
  let rec go : List Ctl → Nat → Nat → Nat × Nat
    | [], k, m => (k, m)
    | c :: r, k, m =>
      let (ok, f) := countRoll G G.horizon (c, g.1) 0
      if ok then (k + f, max m f) else go r (k + f) (max m f)
  let (k, m) := go cs 1 0
  (k.toUInt64 <<< 32) ||| (m + 1).toUInt64

/-- Tooling only (the San Francisco spot check, `flight/src/bin/leanspot.rs`): escape `esc` flown from the
current aircraft as a fresh candidate (the pilot's surfaces latched for no frames), for at most `maxFrames` frames,
with the gate's checks every frame. Output: per frame flown `[x, y, z, elev, ail, rud, thr]` (the position after
the frame and the surfaces applied), then `[frames, end]` with `end` 0 when the clearance test failed, 1 the cap or
the street test, 3 the end-of-escape test passed, 4 the frames ran out. -/
@[export citygate_rollout_lean]
def rolloutE (S : Site) (g : GateState) (esc maxFrames : UInt32) : FloatArray := Id.run do
  let G := gateOn S
  let mut x : Ctl × Plane := (Ctl.fresh ⟨0, 0, 0, 0⟩ 0 (Esc.Law.new esc.toNat) 0.0 HORIZON_FRAMES, g.1)
  let mut out : Array Float := #[]
  let mut fin : Float := 4
  let mut n := 0
  for _ in [0:maxFrames.toNat] do
    if !(decide (x.1.lk ≤ x.1.cap) && x.1.streetOK x.2) then fin := 1; break
    if !clearAtOn S.geo x.1.extra x.2 then fin := 0; break
    if G.term x then fin := 3; break
    let (u, c) := G.ctl x.1 x.2
    let p := x.2.step u
    x := (c, p)
    n := n + 1
    let q := p.pos
    out := out ++ #[q.1, q.2.1, q.2.2, u.elev, u.ail, u.rud, u.thr]
  return ⟨out ++ #[n.toFloat, fin]⟩

end CityGate
