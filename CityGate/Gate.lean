import GateSafety.Spec
import CityGate.ClearFast
import CityGate.Law

/-! The city gate as a `GateSafety.Gate`: `flight/src/envfilter.rs`'s exact-rollout gatekeeper (escapes,
end-of-escape test, resume, direction preference, hold, hand-back margin), one JSBSim frame at a time. Every
3 frames (about the demo's 20 ms tick) it checks candidates "the pilot's surfaces for 3 frames, then escape law
`l`"; in between it flies what it holds. The rollout bookkeeping `rollout_law` keeps locally (frames flown,
samples, the track unwrap) lives in the controller state, so `term` and `clear` see it. -/

namespace CityGate
open GateSafety Esc

/-- A controller: the pilot's latched surfaces for `pf` more frames, then escape law `law`. With the rollout
bookkeeping since the candidate was created: law frames flown `lk`, the last `2·HALF + 1` path samples, the last
unwrapped track sample, extra clearance margin (m), and the law frames the rollout may use. -/
structure Ctl where
  pilot : Surf
  pf : Nat
  law : Law
  lk : Nat
  hist : Array Hist
  psiPrev : Float
  extra : Float
  cap : Nat
  deriving Inhabited

/-- Frames between checks (≈ the demo's 20 ms tick), and the frames a candidate holds the pilot's surfaces. -/
def CHECK_EVERY : Nat := 3
/-- `HORIZON` (16 s) and `RESUME_CAP` in JSBSim frames. -/
def HORIZON_FRAMES : Nat := 2048
def RESUME_CAP : Nat := 1100
/-- `HOLD_TICKS` (15 ticks = 0.3 s) and `RESUME_TICKS` (100 ticks = 2 s), in frames. -/
def HOLD_FRAMES : Nat := 38
def RESUME_FRAMES : Nat := 256
def HANDBACK_EXTRA : Float := 3.0
/-- Candidates per check (CPU). -/
def MAX_CANDS : Nat := 4
/-- Candidates per check while committed: the committed escape continued, then fresh escapes round robin. Fewer
bounds the slow checks, where every candidate runs to its end, at the price of later hand-backs. -/
def MAX_CANDS_COMMITTED : Nat := 2

def Ctl.fresh (pilot : Surf) (pf : Nat) (law : Law) (extra : Float) (cap : Nat) : Ctl :=
  { pilot, pf, law, lk := 0, hist := #[], psiPrev := NAN, extra, cap }

/-- Record the path sample of `p` (`rollout_law`'s `push`), keeping the last `2·HALF + 1`. -/
def Ctl.record (c : Ctl) (p : Plane) : Ctl :=
  let o := p.ob
  let (x, y, z) := p.pos
  let psi0 := Float.atan2 (obN o) (obE o)
  let psi := if c.psiPrev.isNaN then psi0 else c.psiPrev + wrap (psi0 - c.psiPrev)
  let h : Hist := { t := c.lk.toFloat * DT_JSB, x, y, z, psi, vh := (obN o * obN o + obE o * obE o).sqrt,
                    vz := -(obD o) }
  let hist := c.hist.push h
  let hist := if hist.size > 2 * HALF + 1 then hist.extract (hist.size - (2 * HALF + 1)) hist.size else hist
  { c with hist, psiPrev := psi }

/-- `x` clamped to `[lo, hi]`, NaN to `lo`: `CitySafety.clampTo`, so the spec's clamp of an output is a no-op. -/
def clampIn (lo hi x : Float) : Float := if lo ≤ x then (if x ≤ hi then x else hi) else lo

/-- Surfaces clamped to their ranges (`CitySafety.Surfaces.clamp`); a no-op on finite in-range values. -/
def Surf.clamp (u : Surf) : Surf :=
  ⟨clampIn (-1) 1 u.elev, clampIn (-1) 1 u.ail, clampIn (-1) 1 u.rud, clampIn 0 1 u.thr⟩

/-- One frame on map `E`: the latched pilot surfaces, or a frame of the law (recording a sample every `SAMPLE` law
frames), clamped to their ranges. -/
def Ctl.ctl (c : Ctl) (p : Plane) (E : EMap := gridE) : Surf × Ctl :=
  if c.pf > 0 then (c.pilot.clamp, { c with pf := c.pf - 1 })
  else
    let c := if c.lk % SAMPLE == 0 then c.record p else c
    let (u, law) := c.law.step p E
    (u.clamp, { c with law, lk := c.lk + 1 })

/-- The street escape fails a rollout that captures no street axis (`rollout_law`'s early return). -/
def Ctl.streetOK (c : Ctl) (p : Plane) : Bool :=
  c.pf > 0 || c.law.esc != STREET || !(c.law.capture p.ob).axis.isNaN

/-- End-of-escape test on the schedule of `rollout_law`: from `T_TERM` every `TERM_EVERY` frames while turning,
`terminal` on the samples including this one. Leaving the map is not an end: the terrain continues past its edge. -/
def Ctl.term (c : Ctl) (p : Plane) (E : EMap := gridE) : Bool :=
  if c.pf > 0 || c.lk % SAMPLE != 0 then false
  else if c.lk ≥ 768 && c.lk % TERM_EVERY == 0 && c.law.turning then terminalOK E c.law.dir (c.record p).hist
  else false

/-- The proposal layer's memory: frame counter, whether the held controller is a committed escape, frames since
the commit, frames since the last hand-back, the round-robin start while committed, the last turn direction. -/
structure Mem where
  frame : Nat
  committed : Bool
  runFrames : Nat
  sinceHandback : Nat
  rr : Nat
  prevDir : Float
  deriving Inhabited

/-- Turn direction of a law's terminal set, or of its escape before the street escape picks a side. -/
def lawDir (l : Law) : Float := if l.dir != 0.0 then l.dir else ESC_DIR[l.esc]!

/-- `Gate::pref_dir`. -/
def prefDir (m : Mem) (p : Plane) (w : Ctl) : Float :=
  let d := lawDir w.law
  if d != 0.0 then d else if (p.ob[7]!).abs > 0.1 then signum p.ob[7]! else m.prevDir

/-- A check happens on this frame (every `CHECK_EVERY` frames, except during a commit's hold). -/
def Mem.checks (m : Mem) : Bool := m.frame % CHECK_EVERY == 0 && !(m.committed && m.runFrames < HOLD_FRAMES)

/-- `Gate::candidate_laws`: the committed escape continued (or, shortly after a hand-back, the resumed witness),
then fresh escapes round the list from the start, those turning the preferred way first; at most `MAX_CANDS`, or
`MAX_CANDS_COMMITTED` while committed. Returns the laws and how many are fresh. -/
def candidateLaws (m : Mem) (p : Plane) (w : Ctl) : List Law × Nat :=
  let wl := w.law
  let first := if m.committed || wl.t == 0.0 || m.sinceHandback < RESUME_FRAMES then [wl] else []
  let pref := prefDir m p w
  let start := if m.committed then m.rr else wl.esc
  let order := (List.range N_ESC).map fun i => (start + i) % N_ESC
  let ordered := order.filter (fun e => ESC_DIR[e]! * pref ≥ 0.0) ++ order.filter (fun e => !(ESC_DIR[e]! * pref ≥ 0.0))
  let fresh := (ordered.filter fun e => !first.any fun l => l.t == 0.0 && l.esc == e).map Law.new
  let laws := (first ++ fresh).take (if m.committed then MAX_CANDS_COMMITTED else MAX_CANDS)
  (laws, laws.length - first.length)

def proposeC (m : Mem) (p : Plane) (w : Ctl) (u : Surf) : List Ctl :=
  if !m.checks then []
  else (candidateLaws m p w).1.map fun l =>
    Ctl.fresh u CHECK_EVERY l (if m.committed then HANDBACK_EXTRA else 0.0)
      (if l.t > 0.0 then RESUME_CAP else HORIZON_FRAMES)

def updateM (m : Mem) (p : Plane) (w : Ctl) (_u : Surf) (accepted : Bool) : Mem :=
  let m' := { m with frame := m.frame + 1 }
  if m.checks && accepted then
    if m.committed then { m' with committed := false, sinceHandback := 0 }
    else { m' with sinceHandback := m.sinceHandback + 1 }
  else if m.checks && !m.committed then
    let d := lawDir w.law
    { m' with committed := true, runFrames := 1, prevDir := if d != 0.0 then d else m.prevDir }
  else if m.committed then
    let d := lawDir w.law
    let rr := if m.checks then (m.rr + Nat.max (candidateLaws m p w).2 1) % N_ESC else m.rr
    { m' with runFrames := m.runFrames + 1, rr, prevDir := if d != 0.0 then d else m.prevDir }
  else { m' with sinceHandback := m.sinceHandback + 1 }

def MEM0 : Mem := { frame := 0, committed := false, runFrames := 0, sinceHandback := 1000000, rr := 0, prevDir := 0.0 }

/-- A map for the gate: its exact geometry (what `clearAtOn` checks, and `CrashOn` is about) and Rust's
representation of it (the raster the end-of-escape test and the street escape read). -/
structure Site where
  geo : GateGeo
  esc : EMap

/-- The default city. -/
def gridSite : Site := ⟨gridGeo, gridE⟩

/-- The gate on map `S`, without its starting controller (which is searched with this gate's rollout check). -/
def gate0On (S : Site) : Gate Plane Surf Ctl Mem where
  step := Plane.step
  ctl c p := c.ctl p S.esc
  clear x := (decide (x.1.lk ≤ x.1.cap) && x.1.streetOK x.2) && clearAtOn S.geo x.1.extra x.2
  term x := x.1.term x.2 S.esc
  horizon := CHECK_EVERY + HORIZON_FRAMES
  propose := proposeC
  update := updateM
  start _ := default
  m₀ := MEM0

/-- `Gate::new`: the first escape that verifies from `p`, else escape 0 (Rust picks the one that survives longest;
either way such a start is outside `Init`). -/
def startCtlOn (S : Site) (p : Plane) : Ctl :=
  let c := fun e => Ctl.fresh ⟨0, 0, 0, 0⟩ 0 (Law.new e) 0.0 HORIZON_FRAMES
  match (List.range N_ESC).find? fun e => (gate0On S).rolloutOK (gate0On S).horizon (c e, p) with
  | some e => c e
  | none => c 0

/-- The city gate on map `S`. -/
def gateOn (S : Site) : Gate Plane Surf Ctl Mem := { gate0On S with start := startCtlOn S }

def gate0 : Gate Plane Surf Ctl Mem := gate0On gridSite
def startCtl (p : Plane) : Ctl := startCtlOn gridSite p
/-- The city gate in the default city. -/
def cityGate : Gate Plane Surf Ctl Mem := gateOn gridSite

/-- `(gateOn S).clear` passes only where `clearAtOn S.geo` does. -/
theorem gateOn_clear (S : Site) (x : Ctl × Plane) (h : (gateOn S).clear x = true) :
    ∃ e, clearAtOn S.geo e x.2 = true := by
  refine ⟨x.1.extra, ?_⟩
  simp only [gateOn, gate0On, Bool.and_eq_true] at h
  exact h.2

/-- `cityGate.clear` passes only where `clearAt` does. -/
theorem cityGate_clear (x : Ctl × Plane) (h : cityGate.clear x = true) : ∃ e, clearAt e x.2 = true :=
  gateOn_clear gridSite x h

/-- `alpha_for`: angle of attack for lift `n` g at airspeed `v` (rough c172p lift curve). -/
def alphaFor (n v : Float) : Float :=
  let qbar := 0.5 * 1.225 * v * v
  let cl := n * 1043.0 * 9.81 / (qbar * 16.2)
  clamp ((cl - 0.31) / 4.6) (-0.05) 0.25

/-- The aircraft at the start, as `JsbPlant::new` builds it from a point-mass state: map point, altitude, airspeed,
flight path, heading (counter-clockwise from east), bank (positive left), load factor, throttle. Its first frame
flies the fly-by-wire's first output (all observations zero: elevator `-clamp(0.21 n)`, the rest centred). -/
def startPlane (x y z v gam psi phi n thr : Float) : Plane :=
  let v := fmax v 20.0
  let st := CityJsb.init z v gam (PI / 2.0 - psi) (-phi) (alphaFor (fmax n 0.5) v)
  let raw := 1.0 * (0.21 * n + 0.84 * 0.0 - 0.21 * 0.0) - 24.0 * 0.0
  ({ st, ob := FloatArray.empty, ox := x, oy := y } : Plane).step ⟨-(clamp raw (-1.0) 1.0), 0.0, 0.0, clamp thr 0.0 1.0⟩

def startStateOn (S : Site) (x y z v gam psi phi n thr : Float) : Plane × (Mem × Ctl) :=
  let s := startPlane x y z v gam psi phi n thr
  (s, ((gateOn S).m₀, (gateOn S).start s))

def startState (x y z v gam psi phi n thr : Float) : Plane × (Mem × Ctl) := startStateOn gridSite x y z v gam psi phi n thr

theorem startState_eq (x y z v gam psi phi n thr : Float) :
    startState x y z v gam psi phi n thr =
      (startPlane x y z v gam psi phi n thr, (cityGate.m₀, cityGate.start (startPlane x y z v gam psi phi n thr))) :=
  rfl

/-- Display only (called every 0.1 s): points (east, north, up; m) every `SAMPLE` frames along the held controller's escape,
for at most 5 s (640 frames), until its end-of-escape test passes or its frames run out. -/
def predictPathOn (S : Site) (g : Plane × (Mem × Ctl)) : Array (Float × Float × Float) := Id.run do
  let G := gateOn S
  let mut x := (g.2.2, g.1)
  let mut out : Array (Float × Float × Float) := #[g.1.pos]
  for k in [0:640] do
    if G.term x || !decide (x.1.lk ≤ x.1.cap) then break
    x := G.fly x
    if (k + 1) % SAMPLE == 0 then out := out.push x.2.pos
  return out

def predictPath (g : Plane × (Mem × Ctl)) : Array (Float × Float × Float) := predictPathOn gridSite g

end CityGate
