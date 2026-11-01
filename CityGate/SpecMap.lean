import Spec.CitySafety
import CityGate.Geometry
import CityGate.Landing

/-! The demo city as a spec map (`CitySafety.CityMap`): the exported heights and boxes, exact, with the runway, the
world floor and the datum of `CityGate.Landing`. Shared by the clearance proof and the spec bridge. -/

namespace CityGate

/-- An exported building box as a spec box (same six numbers, reordered). -/
def toBox (b : Box Rat) : CitySafety.Box := ⟨b.xmin, b.xmax, b.ymin, b.ymax, b.zmin, b.zmax⟩

/-- The exported city map as a spec map: exact rational heights and boxes, runway and floor at `rwyZ`, map altitude
= reported altitude + 9 m (`Landing.mapDatum`). -/
def cityMap : CitySafety.CityMap where
  half := 3000
  spacing := 20
  n := gridN
  height := node
  boxes := boxes.toList.map toBox
  rwyX0 := Landing.rwyX0
  rwyX1 := Landing.rwyX1
  rwyY0 := Landing.rwyY0
  rwyY1 := Landing.rwyY1
  rwyZ := Landing.rwyZ
  floor := Landing.rwyZ
  datum := 9

end CityGate
