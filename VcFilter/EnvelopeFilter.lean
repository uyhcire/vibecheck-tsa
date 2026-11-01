import VcFilter.Exact
import VcFilter.Config

/-! The envelope filter behind the C ABI (mappings: `docs/vcfilter-envelope.md`). -/

namespace VcFilter
open Envelope Envelope.Checks

/-- Monitor flag bits (low half: this tick; `<<< 16`: latched since reset). -/
def flagVxMin : UInt32 := 1
def flagVxMax : UInt32 := 2
def flagXLo : UInt32 := 4
def flagXHi : UInt32 := 8
def flagHGain : UInt32 := 16
def flagVzFloor : UInt32 := 32
def flagVFloor : UInt32 := 64
def flagInit : UInt32 := 128
def flagBadObs : UInt32 := 256
def flagSubstep : UInt32 := 512

/-- The bits of the `Allowed` clauses that fail on `s → s'` (same conjuncts as `monitor`, in order). -/
def clauseFlags (P : Params Stick) (m : Mode) (s : State) (u : Stick) (s' : State) : UInt32 :=
  let bit (ok : Bool) (b : UInt32) : UInt32 := if ok then 0 else b
  bit (decide (P.vxMin ≤ s'.vx)) flagVxMin ||| bit (decide (s'.vx ≤ P.vxMax)) flagVxMax |||
  bit (decide (s.x + P.dt * P.vxMin ≤ s'.x)) flagXLo ||| bit (decide (s'.x ≤ s.x + P.dt * P.vxMax)) flagXHi |||
  bit (decide (s.h + P.dt * min s.vz s'.vz - P.hSlack ≤ s'.h)) flagHGain |||
  bit (decide (vzFloor P m u s.vz s.V ≤ s'.vz)) flagVzFloor ||| bit (decide (VFloor P m u s.V ≤ s'.V)) flagVFloor

structure Prev where
  applied : Mode
  s : State
  u : Stick

structure FState where
  mode : Mode
  prev : Option Prev
  latched : UInt32
  escapes : Nat
  tick : Nat

def FState.init : FState := ⟨.free, none, 0, 0, 0⟩

/-- Verdict codes, as in `vcfilter.h`. -/
def vPass : Nat := 0
def vEscape : Nat := 2
def vMonitorFail : Nat := 3

/-- Smallest terrain slack (m) of one swept tick from `b` to `c`, beyond `margin` and `sag`. -/
def tickSlack (P : Params Stick) (b c : Box) : Rat :=
  min b.hLo c.hLo - P.sag - (P.terrain.maxOver (min b.xlo c.xlo) (max b.xhi c.xhi) + P.margin)

/-- Smallest `tickSlack` along the worst-case escape loop of `escLoop`. -/
def escSlack (P : Params Stick) : Nat → Nat → Box → Option Rat
  | n, k, b =>
    if escDone P k b then some (b.hLo - P.sag - P.terrain.maxAhead b.xlo - P.margin)
    else match n with
      | 0 => none
      | n + 1 => let c := b.esc P k; (escSlack P n (k + 1) c).map (min (tickSlack P b c))

/-- Reported margin (m, ≥ 0): worst-case terrain slack of the escape the filter relies on now. -/
def marginOf (P : Params Stick) (m : Mode) (s : State) (u : Stick) : Rat :=
  let slack := match m with
    | .free =>
      let b := Box.point s
      let c := b.next P .free u
      if P.vMin ≤ c.VLo then (escSlack P P.horizon 0 c).map (min (tickSlack P b c)) else none
    | .escape k =>
      let b := Box.point s
      if P.vMin ≤ b.VLo then escSlack P (P.horizon - k) k b else none
  max 0 (slack.getD 0)

def outRecord (ret : Int) (verdict : Nat) (esc : Bool) (flags : UInt32) (margin : Rat) (st : FState)
    (applied : Mode) (P : Params Stick) (V : Rat) : FloatArray :=
  let pf := P.perf V
  ⟨#[Float.ofInt ret, Float.ofNat verdict, if esc then 1 else 0, flags.toFloat, ratToFloat margin,
    Float.ofNat st.escapes, Float.ofNat applied.phase, ratToFloat pf.pull, ratToFloat pf.climb,
    ratToFloat P.vMin, Float.ofNat st.tick]⟩

def commitEscape : Mode → Mode
  | .free => .escape 0
  | .escape k => .escape k

def step (c : Cfg) (st : FState) (obs : Option State) (u : Stick) (subs : Option (List State)) :
    FState × FloatArray :=
  let P := c.P
  match obs with
  | none =>
    let a := commitEscape st.mode
    let escapes := if st.mode == .free then st.escapes + 1 else st.escapes
    let latched := st.latched ||| flagBadObs
    let st' : FState := ⟨a.advance, none, latched, escapes, st.tick + 1⟩
    (st', outRecord (-1) vMonitorFail true (flagBadObs ||| (latched <<< 16)) 0 ⟨a, none, latched, escapes, st.tick⟩
      a P P.vMin)
  | some s =>
    let flags : UInt32 := match st.prev with
      | some p => clauseFlags P p.applied p.s p.u s |||
        (if subs.all (substepOK P p.s s) then 0 else flagSubstep)
      | none => if st.tick == 0 && !decide (Init P s) then flagInit else 0
    let monOk := match st.prev with
      | some p => monitor P p.applied p.s p.u s && subs.all (substepOK P p.s s)
      | none => true
    let a := filter P st.mode s u
    let escapes := if st.mode == .free && a != .free then st.escapes + 1 else st.escapes
    let latched := st.latched ||| flags
    let verdict := if flags != 0 || !monOk then vMonitorFail else if a == .free then vPass else vEscape
    let st' : FState := ⟨a.advance, some ⟨a, s, u⟩, latched, escapes, st.tick + 1⟩
    (st', outRecord 0 verdict (a != .free) (flags ||| (latched <<< 16)) (marginOf P a s u)
      ⟨a, none, latched, escapes, st.tick⟩ a P s.V)

/-- The ABI observation `[x, h, vx, vz, V]` as an exact state. -/
def stateOfObs (o : FloatArray) : Option State := do
  if o.size < 5 then none
  return ⟨← ratOfFloat o[0]!, ← ratOfFloat o[1]!, ← ratOfFloat o[2]!, ← ratOfFloat o[3]!,
    ← ratOfFloat o[4]!⟩

@[export vcf_env_config]
def configExport (json : String) : Except String Cfg := Cfg.ofString json

@[export vcf_env_init]
def initExport (_ : Unit) : FState := FState.init

/-- Substep states, 5 entries each; `none` (a failed check) if any entry is not finite. -/
def statesOfArray (a : FloatArray) : Option (List State) :=
  (List.range (a.size / 5)).mapM fun i =>
    stateOfObs ⟨#[a[5 * i]!, a[5 * i + 1]!, a[5 * i + 2]!, a[5 * i + 3]!, a[5 * i + 4]!]⟩

@[export vcf_env_tick]
def tickExport (c : Cfg) (st : FState) (obs : FloatArray) (present : UInt8) (elev : Float) (subs : FloatArray) :
    FState × FloatArray :=
  let s := if present == 0 then none else stateOfObs obs
  let u := match ratOfFloat elev with
    | some e => c.classify e
    | none => .dive
  step c st s u (statesOfArray subs)

/-! ### Checks -/

theorem clauseFlags_zero_iff_monitor (P : Params Stick) (m : Mode) (s : State) (u : Stick) (s' : State) :
    (clauseFlags P m s u s' == 0) = monitor P m s u s' := by
  simp only [clauseFlags, monitor]
  repeat' split
  all_goals simp_all <;> decide

def runTicks (c : Cfg) (st : FState) : List (State × Float) → List FloatArray
  | [] => []
  | (s, e) :: rest =>
    let (st', out) := tickExport c st ⟨#[ratToFloat s.x, ratToFloat s.h, ratToFloat s.vx, ratToFloat s.vz,
      ratToFloat s.V]⟩ 1 e ⟨#[]⟩
    out :: runTicks c st' rest

def cfg0 : Cfg := match Cfg.ofString "" with | .ok c => c | .error _ => ⟨P0, P0_wf, none⟩

#guard (runTicks cfg0 .init [(⟨0, 300, 50, 0, 55⟩, 0), (⟨6, 300, 50, 0, 55⟩, 0)]).map (·[1]!) == [0, 0]
#guard (runTicks cfg0 .init [(⟨200, 223, 50, -5, 55⟩, 0), (⟨206, 222.4, 50, -5.4, 54.9⟩, 0)]).map (·[1]!) == [2, 2]
#guard (runTicks cfg0 .init [(⟨0, 300, 50, 0, 55⟩, 0), (⟨7, 300, 64, 0, 55⟩, 0)]).map (·[3]!) == [0, 2 + 2 * 65536]
#guard ((tickExport cfg0 .init ⟨#[0, 0 / 0, 50, 0, 55]⟩ 1 0 ⟨#[]⟩).2.toList.take 3) == [-1, 3, 1]
#guard let st := (tickExport cfg0 .init ⟨#[0, 300, 50, 0, 55]⟩ 1 0 ⟨#[]⟩).1
  [⟨#[3, 300, 50, 0, 55]⟩, ⟨#[3, 299, 50, 0, 55]⟩].map (fun subs => (tickExport cfg0 st ⟨#[6, 300, 50, 0, 55]⟩ 1 0 subs).2[3]!)
    == [0, 512 + 512 * 65536]

end VcFilter
