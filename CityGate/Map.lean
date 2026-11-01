/-! The city map (seed 1337) exactly as `Tools/city-export` writes it (`CityGate/data/`, format in `map.json`):
building boxes and the terrain grid. Every value is a shortest round-trip decimal, so `Dec.toRat` is the exact
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

def buildingsCsv : String := include_str "data/buildings.csv"
def terrainCsv : String := include_str "data/terrain.csv"

/-- Rows of `id,lot,x_min,y_min,x_max,y_max,z_min,z_max` after the header; unparsable rows are dropped
(`#guard` below checks none are). -/
def boxesDec : Array (Box Dec) :=
  ((buildingsCsv.splitOn "\n").drop 1).toArray.filterMap fun line =>
    match (line.splitOn ",").map parseDec with
    | [_, _, some a, some b, some c, some d, some e, some f] => some ⟨a, b, c, d, e, f⟩
    | _ => none

/-- Terrain heights, row-major: row `j` is `y = gridY0 + j · gridStep` (south to north), column `i` is
`x = gridX0 + i · gridStep`. -/
def terrainDec : Array Dec :=
  ((terrainCsv.splitOn "\n").toArray.flatMap fun line =>
    if line.toList.all Char.isWhitespace then #[] else ((line.splitOn ",").filterMap parseDec).toArray)

def boxes : Array (Box Rat) := boxesDec.map (·.map Dec.toRat)
def boxesF : Array (Box Float) := boxesDec.map (·.map Dec.toFloat)
def terrain : Array Rat := terrainDec.map Dec.toRat
def terrainF : Array Float := terrainDec.map Dec.toFloat

def gridX0 : Int := -3000
def gridY0 : Int := -3000
def gridStep : Nat := 20
def gridN : Nat := 301
/-- The map extent: `|x|, |y| < mapHalf`. -/
def mapHalf : Nat := 3000

#guard boxesDec.size = 2145
#guard terrainDec.size = gridN * gridN

end CityGate
