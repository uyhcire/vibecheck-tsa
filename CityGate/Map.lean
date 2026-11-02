/-! A city map as the gate sees it (`GateMap`: building boxes and a terrain grid), and the default city (seed 1337)
exactly as `Tools/city-export` writes it (`CityGate/data/`, format in `map.json`). San Francisco is
`CityGate.SanFrancisco`. Every value is a shortest round-trip decimal, so `Dec.toRat` is the exact
value and `Dec.toFloat` the same double Rust uses. Trusted surface (with `data/`). -/

namespace CityGate

/-- A decimal as written in the map files: `(-1)^neg · m · 10^(-e)`. -/
structure Dec where
  m : Nat
  neg : Bool
  e : Nat
  deriving Repr, Inhabited

def Dec.toRat (d : Dec) : Rat := (if d.neg then -1 else 1) * ((d.m : Rat) / ((10 ^ d.e : Nat) : Rat))

/-- Correctly rounded (`Float.ofScientific`), so a shortest round-trip decimal gives back its double. -/
def Dec.toFloat (d : Dec) : Float := let f := Float.ofScientific d.m true d.e; if d.neg then -f else f

/-- Parse `[-]digits[.digits]` (whitespace ignored). -/
def parseDec (s : String) : Option Dec :=
  let cs := s.toList.filter fun c => !c.isWhitespace
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let ip := cs.takeWhile (· != '.')
  let fp := match cs.dropWhile (· != '.') with
    | _ :: r => r
    | [] => []
  if ip.isEmpty || !(ip ++ fp).all Char.isDigit then none
  else some { m := (ip ++ fp).foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0, neg, e := fp.length }

/-- An axis-aligned box `[xmin, xmax] × [ymin, ymax] × [zmin, zmax]`. -/
structure Box (α : Type) where
  xmin : α
  ymin : α
  xmax : α
  ymax : α
  zmin : α
  zmax : α
  deriving Repr, Inhabited

def Box.map {α β : Type} (f : α → β) (b : Box α) : Box β :=
  ⟨f b.xmin, f b.ymin, f b.xmax, f b.ymax, f b.zmin, f b.zmax⟩

/-- Rows of `id,lot,x_min,y_min,x_max,y_max,z_min,z_max` after the header; unparsable rows are dropped
(`#guard`s check none are). -/
def parseBoxes (csv : String) : Array (Box Dec) :=
  ((csv.splitOn "\n").drop 1).toArray.filterMap fun line =>
    match (line.splitOn ",").map parseDec with
    | [_, _, some a, some b, some c, some d, some e, some f] => some ⟨a, b, c, d, e, f⟩
    | _ => none

/-- Terrain heights, row-major, one row per line. -/
def parseTerrain (csv : String) : Array Dec :=
  (csv.splitOn "\n").toArray.flatMap fun line =>
    if line.toList.all Char.isWhitespace then #[] else ((line.splitOn ",").filterMap parseDec).toArray

/-- Terrain vertex spacing (m), on every map. -/
def gridStep : Nat := 20

/-- A map as the gate sees it: terrain heights on an `nx × ny` grid of spacing `gridStep` whose vertex `(0, 0)` is
at `(x0, y0)` (m), row-major (`terrain[j * nx + i]` is the vertex `(x0 + i · gridStep, y0 + j · gridStep)`), and
`nb` closed building boxes `box 0, …, box (nb - 1)`. Trusted surface: `Crash` (`CityGate.Geometry`) reads only
these fields. -/
structure GateMap where
  x0 : Int
  y0 : Int
  nx : Nat
  ny : Nat
  nb : Nat
  box : Nat → Box Rat
  terrain : Array Rat

/-! ### The default city (seed 1337) -/

def buildingsCsv : String := include_str "data/buildings.csv"
def terrainCsv : String := include_str "data/terrain.csv"

def boxesDec : Array (Box Dec) := parseBoxes buildingsCsv

/-- Terrain heights, row-major: row `j` is `y = gridY0 + j · gridStep` (south to north), column `i` is
`x = gridX0 + i · gridStep`. -/
def terrainDec : Array Dec := parseTerrain terrainCsv

def boxes : Array (Box Rat) := boxesDec.map (·.map Dec.toRat)
def boxesF : Array (Box Float) := boxesDec.map (·.map Dec.toFloat)
def terrain : Array Rat := terrainDec.map Dec.toRat
def terrainF : Array Float := terrainDec.map Dec.toFloat

def gridX0 : Int := -3000
def gridY0 : Int := -3000
def gridN : Nat := 301
/-- The map extent: `|x|, |y| < mapHalf`. -/
def mapHalf : Nat := 3000

/-- The default city as a `GateMap`. -/
def gridMap : GateMap := ⟨gridX0, gridY0, gridN, gridN, boxes.size, fun k => boxes.getD k default, terrain⟩

#guard boxesDec.size = 2145
#guard terrainDec.size = gridN * gridN

end CityGate
