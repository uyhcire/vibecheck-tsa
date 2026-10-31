import Vibecheck
import App.Gfx

open Vibecheck

namespace App

def W : Float := 1280
def H : Float := 720
def stepNs : UInt64 := 62500000

def runwayNames : Array String := #["HOME", "MESA", "VALLEY"]

def runwayIndex (r : Runway) : Nat := (runways.toArray.findIdx? (· == r)).getD 0

inductive Outcome
  | flying
  | landed (name : String)
  | crashed (why : CrashKind)

structure Particle where
  x : Float
  y : Float
  vx : Float
  vy : Float
  life : Float

structure Game where
  s : State
  prev : State
  stick : Float := 0
  throttle : Float := 0
  filterOn : Bool := true
  paused : Bool := false
  ghost : Bool := true
  help : Bool := true
  fast : Bool := false
  autopilot : Bool := false
  autoAt : Option Nat := none
  autoRunway : Option Runway := none
  ghostPath : Array (Float × Float) := #[]
  ghostRunway : Option Runway := none
  safeNow : Bool := true
  overrideSteps : Nat := 0
  interventions : Nat := 0
  steps : Nat := 0
  pilot : Input := Autoland.park
  applied : Input := Autoland.park
  airborne : Bool := false
  outcome : Outcome := .flying
  particles : Array Particle := #[]
  zoom : Float := 1.6
  camH : Float := 50
  stepMs : Float := 0
  scripted : Bool := false
  shots : List Nat := []
  exitAt : Option Nat := none

def Game.new : Game := { s := initState, prev := initState }

def toFx (f : Float) : Fx := ⟨(f * 65536).round.toInt64.toInt⟩

def clampF (lo hi x : Float) : Float := if x < lo then lo else if x > hi then hi else x

def lerpF (a b t : Float) : Float := a + (b - a) * t

def pitchDeg (s : State) : Float := Float.atan2 s.dz.toFloat s.dx.toFloat * 57.29578

def aoaDeg (s : State) : Float :=
  let u := s.u.toFloat
  if u < 1 then 0 else Float.atan2 s.alphaV.toFloat u * 57.29578

def refreshGhost (g : Game) : Game :=
  match escapeRunway g.s with
  | none => { g with ghostPath := #[], ghostRunway := none }
  | some r =>
    let path := (rolloutPath r horizon g.s).toArray
    let pts := path.filterMap fun st =>
      if st.x.raw % (8 * 65536) < 3 * 65536 || st.parked then some (st.x.toFloat, st.h.toFloat) else none
    let pts := if pts.size > 900 then pts.extract 0 900 else pts
    { g with ghostPath := pts, ghostRunway := some r }

def spawnExplosion (g : Game) : Game := Id.run do
  let mut ps := g.particles
  for i in [0:80] do
    let a := i.toFloat * 2.399
    let sp := 8 + (i % 7).toFloat * 6
    ps := ps.push { x := g.s.x.toFloat, y := g.s.h.toFloat, vx := sp * Float.cos a + g.s.vx.toFloat * 0.3,
                    vy := sp * Float.sin a + 12, life := 1.5 + (i % 5).toFloat * 0.3 }
  return { g with particles := ps }

/-- Scripted pilot for unattended test runs: take off, climb, then dive at the ridge. -/
def scriptPilot (g : Game) : Game :=
  let t := g.steps.toFloat / 16
  let stick := if t < 6 then 0 else if t < 12 then 0.5 else if t < 30 then 0.05 else -1
  let g := { g with stick := stick, throttle := 1 }
  match g.autoAt with
  | some a =>
    if g.steps ≥ a * 16 && !g.autopilot then
      { g with autopilot := true, autoRunway := escapeRunway g.s }
    else g
  | none => g

def physicsStep (g : Game) : IO Game := do
  let g := if g.scripted then scriptPilot g else g
  if g.s.crashed then return { g with steps := g.steps + 1 }
  let t0 ← IO.monoNanosNow
  let pilot : Input :=
    match g.autopilot, g.autoRunway with
    | true, some r => Autoland.control r g.s
    | _, _ => { stick := toFx g.stick, throttle := toFx g.throttle, brake := g.pilot.brake }
  let safeU := inS (step g.s pilot.clampAdm)
  let applied := if g.filterOn then filter g.s pilot else pilot.clampAdm
  let overridden := g.filterOn && applied != pilot.clampAdm
  let s' := step g.s applied
  let t1 ← IO.monoNanosNow
  let mut g := { g with prev := g.s, s := s', pilot := pilot, applied := applied,
                        steps := g.steps + 1, safeNow := safeU,
                        stepMs := lerpF g.stepMs ((t1 - t0).toFloat / 1e6) 0.1 }
  if overridden then
    g := { g with overrideSteps := g.overrideSteps + 1,
                  interventions := g.interventions + (if g.overrideSteps == 0 then 1 else 0) }
  else
    g := { g with overrideSteps := 0 }
  if s'.phase == .air then g := { g with airborne := true }
  match s'.phase with
  | .crashed why =>
    g := spawnExplosion { g with outcome := .crashed why }
  | _ =>
    if g.airborne && s'.parked then
      let name := match runwayAt s'.x with
        | some r => runwayNames[runwayIndex r]!
        | none => "?"
      g := { g with outcome := .landed name }
  if g.ghost && g.steps % 6 == 0 then g := refreshGhost g
  return g

def handleInput (g : Game) (k : UInt32) (dtSec : Float) : Game := Id.run do
  let mut g := g
  if Gfx.has k Gfx.pRestart then
    return { Game.new with filterOn := g.filterOn, ghost := g.ghost, help := false }
  if Gfx.has k Gfx.pFilter then g := { g with filterOn := !g.filterOn }
  if Gfx.has k Gfx.pPause then g := { g with paused := !g.paused }
  if Gfx.has k Gfx.pGhost then g := { g with ghost := !g.ghost, ghostPath := #[] }
  if Gfx.has k Gfx.pHelp then g := { g with help := !g.help }
  if Gfx.has k Gfx.pFast then g := { g with fast := !g.fast }
  if Gfx.has k Gfx.pAuto then
    g := if g.autopilot then { g with autopilot := false, autoRunway := none }
      else { g with autopilot := true, autoRunway := escapeRunway g.s }
  let target : Float :=
    if Gfx.has k Gfx.keyUp then 1 else if Gfx.has k Gfx.keyDown then -1 else 0
  let rate := 3.0 * dtSec
  let stick := if g.stick < target then min target (g.stick + rate) else max target (g.stick - rate)
  let thr :=
    if Gfx.has k Gfx.keyThrUp then g.throttle + 0.6 * dtSec
    else if Gfx.has k Gfx.keyThrDn then g.throttle - 0.6 * dtSec else g.throttle
  let brake := Gfx.has k Gfx.keyBrake
  { g with stick := stick, throttle := clampF 0 1 thr, pilot := { g.pilot with brake := brake } }

def updateParticles (g : Game) (dtSec : Float) : Game :=
  { g with particles := g.particles.filterMap fun p =>
      if p.life ≤ 0 then none
      else some { p with x := p.x + p.vx * dtSec, y := p.y + p.vy * dtSec,
                         vy := p.vy - 9.8 * dtSec, life := p.life - dtSec } }

structure Cam where
  x : Float
  h : Float
  z : Float

def Cam.sx (c : Cam) (x : Float) : Float := W * 0.33 + (x - c.x) * c.z
def Cam.sy (c : Cam) (h : Float) : Float := H * 0.58 - (h - c.h) * c.z
def Cam.wx (c : Cam) (sx : Float) : Float := c.x + (sx - W * 0.33) / c.z

def col (r g b : UInt8) (a : UInt8 := 255) : IO Unit := Gfx.color r g b a

def drawSky (c : Cam) : IO Unit := do
  let bands := 24
  for i in [0:bands] do
    let t := i.toFloat / bands.toFloat
    let alt := clampF 0 1 ((c.h - 50) / 1500)
    let r := lerpF 120 40 (t * 0.3 + alt * 0.5)
    let gg := lerpF 175 90 (t * 0.3 + alt * 0.5)
    let b := lerpF 235 170 (t * 0.2 + alt * 0.3)
    col r.toUInt8 gg.toUInt8 b.toUInt8
    Gfx.fillRect 0 (H * t) W (H / bands.toFloat + 1)

def drawFarHills (c : Cam) : IO Unit := do
  col 160 182 214
  let par := 0.25
  let n := 40
  for i in [0:n] do
    let base := (c.x * par / 150).floor + i.toFloat - 8
    let wx0 := base * 150
    let h0 := 70 + 55 * Float.sin (base * 2.3) + 35 * Float.sin (base * 0.71)
    let h1 := 70 + 55 * Float.sin ((base + 1) * 2.3) + 35 * Float.sin ((base + 1) * 0.71)
    let sx0 := W * 0.33 + (wx0 - c.x * par) * c.z * 0.5
    let sx1 := sx0 + 150 * c.z * 0.5
    let sy0 := H * 0.62 - h0 * c.z * 0.5 + (c.h - 50) * c.z * 0.15
    let sy1 := H * 0.62 - h1 * c.z * 0.5 + (c.h - 50) * c.z * 0.15
    if sx1 > -10 && sx0 < W + 10 then Gfx.quad sx0 sy0 sx1 sy1 sx1 H sx0 H

def drawClouds (c : Cam) : IO Unit := do
  col 255 255 255 170
  for i in [0:30] do
    let wx := i.toFloat * 410 + 130 * Float.sin (i.toFloat * 3.1)
    let wh := 380 + 260 * (Float.sin (i.toFloat * 1.9) + 1)
    let par := 0.6
    let sx := W * 0.33 + (wx - c.x * par) * c.z
    let sy := H * 0.58 - (wh - c.h) * c.z
    if sx > -200 && sx < W + 200 && sy > -60 && sy < H + 60 then
      let w := 70 * c.z
      Gfx.fillRect (sx - w) (sy - 8 * c.z) (2 * w) (16 * c.z)
      Gfx.fillRect (sx - w * 0.6) (sy - 18 * c.z) (1.2 * w) (14 * c.z)

def drawTerrain (c : Cam) : IO Unit := do
  let pts := terrainPts.toArray.map fun (x, z) => (x.toFloat, z.toFloat)
  let x0 := c.wx (-20)
  let x1 := c.wx (W + 20)
  for i in [0:pts.size - 1] do
    let (ax, az) := pts[i]!
    let (bx, bz) := pts[i+1]!
    if bx ≥ x0 && ax ≤ x1 then
      col 92 140 70
      Gfx.quad (c.sx ax) (c.sy az) (c.sx bx) (c.sy bz) (c.sx bx) H (c.sx ax) H
      col 70 110 55
      Gfx.quad (c.sx ax) (c.sy az + 6 * c.z) (c.sx bx) (c.sy bz + 6 * c.z) (c.sx bx) H (c.sx ax) H
      col 60 90 45
      Gfx.line (c.sx ax) (c.sy az) (c.sx bx) (c.sy bz)
  let (lx, lz) := pts[pts.size - 1]!
  if lx < x1 then
    col 92 140 70
    Gfx.fillRect (c.sx lx) (c.sy lz) (W - c.sx lx + 20) H
  let (fx, fz) := pts[0]!
  if fx > x0 then
    col 92 140 70
    Gfx.fillRect 0 (c.sy fz) (c.sx fx) H

def drawRunways (c : Cam) (target : Option Runway) : IO Unit := do
  for r in runways do
    let a := c.sx r.start.toFloat
    let b := c.sx r.stop.toFloat
    let y := c.sy r.elev.toFloat
    if b > 0 && a < W then
      col 55 55 60
      Gfx.fillRect a (y - 1) (b - a) (max 3 (4 * c.z))
      col 240 240 240
      let len := r.stop.toFloat - r.start.toFloat
      let n := (len / 40).floor.toUInt64.toNat
      for i in [0:n] do
        let wx := r.start.toFloat + i.toFloat * 40 + 10
        Gfx.fillRect (c.sx wx) (y) (20 * c.z) (max 1 c.z)
      if target == some r then
        col 80 255 120 200
        Gfx.fillRect a (y - 3) (b - a) 2
      let idx := runwayIndex r
      col 255 255 255
      Gfx.text (a + 4) (y + 10) 1.5 (runwayNames[idx]!)

def rot (cx cy ca sa sc px py : Float) : Float × Float :=
  (cx + (px * ca - py * sa) * sc, cy - (px * sa + py * ca) * sc)

def drawPlane (c : Cam) (s : State) (x h : Float) (ca sa : Float) (throttle : Float) : IO Unit := do
  let cx := c.sx x
  let cy := c.sy h
  let sc := max 3.2 (c.z * 1.5)
  let p := fun (px py : Float) => rot cx cy ca sa sc px py
  if s.fuel.raw > 0 && throttle > 0.02 then
    let (ax, ay) := p (-6) 0.6
    let (bx, by_) := p (-6 - 10 * throttle) 0
    let (dx, dy) := p (-6) (-0.6)
    col 255 170 60 220
    Gfx.tri ax ay bx by_ dx dy
  let fus := #[(9.0, 0.0), (6.0, 1.0), (-5.0, 0.8), (-6.0, 0.2), (-6.0, -0.4), (5.0, -0.9), (8.0, -0.6)]
  col 235 235 240
  for i in [1:fus.size - 1] do
    let (ax, ay) := p fus[0]!.1 fus[0]!.2
    let (bx, by_) := p fus[i]!.1 fus[i]!.2
    let (dx, dy) := p fus[i+1]!.1 fus[i+1]!.2
    Gfx.tri ax ay bx by_ dx dy
  col 200 40 40
  let (t1x, t1y) := p (-6) 0.2
  let (t2x, t2y) := p (-4) 0.5
  let (t3x, t3y) := p (-6.5) 3.2
  Gfx.tri t1x t1y t2x t2y t3x t3y
  col 40 60 120
  let (w1x, w1y) := p 2 0
  let (w2x, w2y) := p (-1.5) 0
  let (w3x, w3y) := p (-1) (-0.5)
  let (w4x, w4y) := p 2.5 (-0.4)
  Gfx.quad w1x w1y w2x w2y w3x w3y w4x w4y
  col 90 160 220
  let (c1x, c1y) := p 6 0.8
  let (c2x, c2y) := p 3.5 1.4
  let (c3x, c3y) := p 2.5 0.9
  Gfx.tri c1x c1y c2x c2y c3x c3y

def drawGhost (c : Cam) (g : Game) : IO Unit := do
  if !g.ghost then return
  col 80 255 140 200
  for (x, h) in g.ghostPath do
    let sx := c.sx x
    let sy := c.sy h
    if sx > -5 && sx < W + 5 then Gfx.fillRect (sx - 1.5) (sy - 1.5) 3 3

def drawParticles (c : Cam) (g : Game) : IO Unit := do
  for p in g.particles do
    let t := clampF 0 1 (p.life / 2)
    col 255 (lerpF 60 220 t).toUInt8 30 (lerpF 0 255 t).toUInt8
    Gfx.fillRect (c.sx p.x - 3) (c.sy p.y - 3) 6 6

def bar (x y w h frac : Float) (r g b : UInt8) : IO Unit := do
  col 0 0 0 120
  Gfx.fillRect x y w h
  col r g b
  Gfx.fillRect x y (w * clampF 0 1 frac) h
  col 255 255 255 160
  Gfx.rect x y w h 0

def fmt1 (f : Float) : String :=
  let v := (f * 10).round / 10
  let s := toString v
  match s.splitOn "." with
  | [a, b] => a ++ "." ++ (b.take 1).toString
  | _ => s

def fmt0 (f : Float) : String :=
  let v := f.round
  match (toString v).splitOn "." with
  | a :: _ => a
  | _ => toString v

def drawHud (g : Game) : IO Unit := do
  let s := g.s
  col 0 0 0 110
  Gfx.fillRect 10 10 330 200
  col 255 255 255
  let agl := s.h.toFloat - (terrain s.x).toFloat
  Gfx.text 20 20 2 s!"AIRSPEED {fmt0 s.u.toFloat} m/s"
  Gfx.text 20 42 2 s!"ALTITUDE {fmt0 agl} m AGL"
  Gfx.text 20 64 2 s!"CLIMB    {fmt1 s.vz.toFloat} m/s"
  Gfx.text 20 86 2 s!"PITCH {fmt0 (pitchDeg s)}  AOA {fmt0 (aoaDeg s)}"
  Gfx.text 20 112 2 "THR"
  bar 80 112 240 14 g.applied.throttle.toFloat 255 170 60
  Gfx.text 20 134 2 "FUEL"
  bar 80 134 240 14 (s.fuel.toFloat / P.fuelMax.toFloat) 90 200 255
  Gfx.text 20 158 2 "STICK"
  col 0 0 0 120
  Gfx.fillRect 110 156 210 18
  col 255 255 255 120
  Gfx.fillRect 214 156 2 18
  col 255 200 60
  Gfx.fillRect (214 + g.pilot.stick.toFloat * 100 - 3) 156 6 18
  col 80 255 140
  Gfx.fillRect (214 + g.applied.stick.toFloat * 100 - 2) 160 4 10
  col 200 200 200
  Gfx.text 20 182 1.5 "yellow = you, green = applied"
  if aoaDeg s > 12 && s.phase == .air then
    col 255 60 60
    Gfx.text 360 20 3 "STALL"
  col 0 0 0 110
  Gfx.fillRect (W - 380) 10 370 112
  if g.filterOn then
    col 80 255 140
    Gfx.text (W - 370) 20 2 "SAFETY FILTER: ON"
  else
    col 255 90 90
    Gfx.text (W - 370) 20 2 "SAFETY FILTER: OFF"
  if g.safeNow then
    col 80 255 140
    Gfx.text (W - 370) 44 2 "your input: SAFE"
  else
    col 255 180 60
    Gfx.text (W - 370) 44 2 "your input: UNSAFE"
  col 255 255 255
  let tgt := match g.ghostRunway with
    | some r => runwayNames[runwayIndex r]!
    | none => "NONE"
  Gfx.text (W - 370) 68 2 s!"escape: land at {tgt}"
  Gfx.text (W - 370) 92 1.5 s!"overrides {g.interventions}  step {fmt1 g.stepMs} ms"
  if g.autopilot then
    col 120 200 255
    let name := match g.autoRunway with
      | some r => runwayNames[runwayIndex r]!
      | none => "?"
    Gfx.text (W / 2 - 240) 140 2.5 s!"AUTOLAND TO {name} (A)"
  if g.overrideSteps > 0 then
    col 255 120 40 (if (g.steps / 3) % 2 == 0 then 255 else 150)
    Gfx.text (W / 2 - 300) 250 3 "VERIFIED FILTER: OVERRIDE"
  match g.outcome with
  | .crashed why =>
    col 255 80 60
    let w := match why with
      | .terrain => "hit terrain" | .hardLanding => "hard landing" | .overrun => "runway overrun"
      | .overspeed => "overspeed" | .overstress => "airframe overstress"
    Gfx.text (W / 2 - 330) 300 4 s!"CRASHED: {w}"
    Gfx.text (W / 2 - 200) 350 2 "press R to try again"
  | .landed name =>
    col 120 255 160
    Gfx.text (W / 2 - 300) 300 4 s!"LANDED AT {name}"
    Gfx.text (W / 2 - 200) 350 2 s!"fuel left {fmt0 s.fuel.toFloat}s  overrides {g.interventions}"
    Gfx.text (W / 2 - 200) 375 2 "press R to fly again"
  | .flying => pure ()
  if g.paused then
    col 255 255 255
    Gfx.text (W / 2 - 80) 200 4 "PAUSED"
  if g.help then
    col 0 0 0 150
    Gfx.fillRect 10 (H - 150) 520 140
    col 255 255 255
    Gfx.text 20 (H - 140) 1.75 "UP/DOWN      pitch up / down"
    Gfx.text 20 (H - 120) 1.75 "W/S          throttle up / down"
    Gfx.text 20 (H - 100) 1.75 "SPACE        brake"
    Gfx.text 20 (H - 80) 1.75 "F filter  A autoland  G escape path  T fast"
    Gfx.text 20 (H - 60) 1.75 "R restart   P pause   H help   ESC quit"
    Gfx.text 20 (H - 36) 1.75 "Try to crash. The Lean-verified filter won't let you."

def render (g : Game) (alpha : Float) : IO Unit := do
  let a := g.prev
  let b := g.s
  let x := lerpF a.x.toFloat b.x.toFloat alpha
  let h := lerpF a.h.toFloat b.h.toFloat alpha
  let ca := lerpF a.dx.toFloat b.dx.toFloat alpha
  let sa := lerpF a.dz.toFloat b.dz.toFloat alpha
  let cam : Cam := { x := x + 60 / g.zoom, h := g.camH, z := g.zoom }
  drawSky cam
  drawFarHills cam
  drawClouds cam
  drawTerrain cam
  drawRunways cam g.ghostRunway
  drawGhost cam g
  if !g.s.crashed then drawPlane cam b x h ca sa g.applied.throttle.toFloat
  drawParticles cam g
  drawHud g
  Gfx.present

def updateCamera (g : Game) (dtSec : Float) : Game :=
  let agl := g.s.h.toFloat - (terrain g.s.x).toFloat
  let zt := clampF 0.7 2.6 (2.6 - agl / 160)
  let z := lerpF g.zoom zt (clampF 0 1 (dtSec * 1.5))
  let ht := g.s.h.toFloat + 40 / z
  let camH := lerpF g.camH ht (clampF 0 1 (dtSec * 3))
  { g with zoom := z, camH := camH }

partial def loop (g : Game) (last : UInt64) (acc : UInt64) : IO Unit := do
  let now ← Gfx.ticks
  let frame := now - last
  let k ← Gfx.poll
  if Gfx.has k Gfx.pQuit then return
  let dtSec := frame.toFloat / 1e9
  let mut g := handleInput g k dtSec
  let mut acc := if g.paused then 0 else acc + (if g.fast then frame * 2 else frame)
  if acc > 4 * stepNs then acc := 4 * stepNs
  while acc ≥ stepNs do
    g ← physicsStep g
    acc := acc - stepNs
  g := updateParticles g dtSec
  g := updateCamera g dtSec
  match g.shots with
  | t :: rest =>
    if g.steps ≥ t * 16 then
      Gfx.screenshot s!"/tmp/vc_shot_{t}.bmp"
      g := { g with shots := rest }
  | [] => pure ()
  render g (acc.toFloat / stepNs.toFloat)
  if let some t := g.exitAt then
    if g.steps ≥ t * 16 then return
  loop g now acc

def run : IO Unit := do
  let ok ← Gfx.init 1280 720 "Vibecheck TSA: verified flight safety"
  if !ok then
    IO.eprintln "Could not open an SDL window."
    return
  let t ← Gfx.ticks
  let scripted := (← IO.getEnv "VC_SCRIPT").isSome
  let shots := ((← IO.getEnv "VC_SHOTS").getD "").splitOn "," |>.filterMap String.toNat?
  let exitAt := (← IO.getEnv "VC_EXIT").bind String.toNat?
  let filterOn := (← IO.getEnv "VC_NOFILTER").isNone
  let autoAt := (← IO.getEnv "VC_AUTOPILOT").bind String.toNat?
  let g := { Game.new with scripted, shots, exitAt, filterOn, autoAt, help := !scripted }
  loop (refreshGhost g) t 0
  Gfx.quit

end App
