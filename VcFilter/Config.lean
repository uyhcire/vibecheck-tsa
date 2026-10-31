import VcFilter.Json
import Envelope.Checks

/-! Filter configuration: `Envelope.Checks.P0`, with any field overridden from a JSON object. -/

namespace VcFilter
open Envelope Envelope.Checks

/-- Envelope parameters the adapter runs with; `WellFormed` is checked when loading. -/
structure Cfg where
  P : Params Stick
  wf : P.WellFormed
  /-- elevator (+ nose down) at or below this is `hold`, else `dive`; default 0, JSON `null`: all `dive` -/
  holdElevMax : Option Rat

/-- A JSON number (exact decimal) or a string `"p/q"` / `"p"`, as a rational. -/
def ratOfJson (j : Json) : Except String Rat :=
  match j with
  | .num q => pure q
  | .str s =>
    match s.splitOn "/" with
    | [p] => match p.trimAscii.toString.toInt? with
      | some a => pure a
      | none => throw s!"bad rational {s}"
    | [p, q] => match p.trimAscii.toString.toInt?, q.trimAscii.toString.toNat? with
      | some a, some b => if b == 0 then throw s!"zero denominator {s}" else pure (mkRat a b)
      | _, _ => throw s!"bad rational {s}"
    | _ => throw s!"bad rational {s}"
  | _ => throw "expected a number"

def arrOfJson (j : Json) : Except String (Array Json) :=
  match j with
  | .arr xs => pure xs
  | _ => throw "expected an array"

def natOfJson (j : Json) : Except String Nat := do
  let q ← ratOfJson j
  if q.den == 1 && 0 ≤ q.num then pure q.num.toNat else throw s!"expected a natural number"

/-- Field `k` of `j` through `f`, or `d` when absent. -/
def field {α : Type} (j : Json) (k : String) (f : Json → Except String α) (d : α) : Except String α :=
  match j.get? k with
  | some v => (f v).mapError (s!"{k}: " ++ ·)
  | none => pure d

def perfOfJson (d : Perf) (j : Json) : Except String Perf :=
  return ⟨← field j "pull" ratOfJson d.pull, ← field j "climb" ratOfJson d.climb⟩

def bandOfJson (j : Json) : Except String Band := do
  let vLo ← match j.get? "vLo" with | some v => ratOfJson v | none => throw "band without vLo"
  return ⟨vLo, ← perfOfJson ⟨0, 0⟩ j⟩

def freeOfJson (d : FreeBound) (j : Json) : Except String FreeBound :=
  return ⟨← field j "vzDrop" ratOfJson d.vzDrop, ← field j "vDrop" ratOfJson d.vDrop⟩

def terrainOfJson (d : Terrain) (j : Json) : Except String Terrain := do
  let cells ← field j "cells" (fun c => do (← arrOfJson c).mapM ratOfJson) d.cells
  return ⟨← field j "x0" ratOfJson d.x0, ← field j "w" ratOfJson d.w, cells,
    ← field j "beyond" ratOfJson d.beyond⟩

/-- Parameters from a JSON object; absent keys keep `P0`'s values. -/
def paramsOfJson (j : Json) : Except String (Params Stick × Option Rat) := do
  let d := P0
  let hold ← field j "free" (fun f => field f "hold" (freeOfJson (d.free .hold)) (d.free .hold)) (d.free .hold)
  let dive ← field j "free" (fun f => field f "dive" (freeOfJson (d.free .dive)) (d.free .dive)) (d.free .dive)
  let P : Params Stick :=
    { dt := ← field j "dt" ratOfJson d.dt
      delayTicks := ← field j "delayTicks" natOfJson d.delayTicks
      delayVzDrop := ← field j "delayVzDrop" ratOfJson d.delayVzDrop
      vMin := ← field j "vMin" ratOfJson d.vMin
      escVDrop := ← field j "escVDrop" ratOfJson d.escVDrop
      base := ← field j "base" (perfOfJson d.base) d.base
      bands := ← field j "bands" (fun b => do return (← (← arrOfJson b).mapM bandOfJson).toList) d.bands
      free := fun | .hold => hold | .dive => dive
      vxMin := ← field j "vxMin" ratOfJson d.vxMin
      vxMax := ← field j "vxMax" ratOfJson d.vxMax
      hSlack := ← field j "hSlack" ratOfJson d.hSlack
      sag := ← field j "sag" ratOfJson d.sag
      margin := ← field j "margin" ratOfJson d.margin
      terrain := ← field j "terrain" (terrainOfJson d.terrain) d.terrain
      horizon := ← field j "horizon" natOfJson d.horizon }
  let holdMax ← field j "holdElevatorMax" (fun | .null => pure none | v => some <$> ratOfJson v) (some 0)
  return (P, holdMax)

/-- Configuration from JSON text (empty or blank: `P0`); rejects parameters that are not `WellFormed`. -/
def Cfg.ofString (s : String) : Except String Cfg := do
  let j ← if s.trimAscii.isEmpty then pure (Json.obj []) else Json.parse s
  let (P, holdElevMax) ← paramsOfJson j
  if h : P.WellFormed then pure ⟨P, h, holdElevMax⟩
  else throw "parameters are not WellFormed (need 0 ≤ dt, 0 < terrain.w, 0 ≤ sag, 0 ≤ base.pull, hSlack ≤ dt·base.climb)"

/-- Pilot class of a surface command with elevator `elev`. -/
def Cfg.classify (c : Cfg) (elev : Rat) : Stick :=
  match c.holdElevMax with
  | some t => if elev ≤ t then .hold else .dive
  | none => .dive

#guard match Cfg.ofString "" with | .ok c => c.P.horizon == 400 && c.P.dt == 1/8 | .error _ => false
#guard match Cfg.ofString "{\"dt\": 0.0625, \"margin\": \"21/2\", \"terrain\": {\"cells\": [0, 5]}}" with
  | .ok c => c.P.dt == 1/16 && c.P.margin == 21/2 && c.P.terrain.cells == #[0, 5] && c.P.terrain.w == 50
  | .error _ => false
#guard match Cfg.ofString "{\"sag\": -1}" with | .ok _ => false | .error _ => true
#guard match Cfg.ofString "{\"dt\": [1]}" with | .ok _ => false | .error _ => true

end VcFilter
