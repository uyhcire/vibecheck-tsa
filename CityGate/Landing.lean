/-! The runway, the landing funnel and the low-fuel start (the same numbers as `flight/src/runway.rs`). Map metres:
x east, y north, z altitude. The world floor is the runway surface: terrain below `rwyZ` is raised to it, and map
altitude is JSBSim's altitude above sea level plus `mapDatum`, so JSBSim's ground plane (0 ft) is that floor. -/

namespace CityGate.Landing

/-- Runway `[rwyX0, rwyX1] × [rwyY0, rwyY1]`, surface at `rwyZ`; landing eastbound, threshold at `rwyX0`. -/
def rwyX0 : Rat := -100
def rwyX1 : Rat := 1100
def rwyY0 : Rat := -1360
def rwyY1 : Rat := -1320
def rwyYC : Rat := -1340
def rwyZ : Rat := 9
/-- Map altitude = JSBSim altitude above sea level + `mapDatum`. -/
def mapDatum : Float := 9.0
/-- Threshold crossing height above the runway (m). -/
def tch : Float := 15.0

/-- Funnel bounds (see `flight/src/runway.rs` for the definition they enter). -/
def funD0 : Float := 400.0
def funD1 : Float := 2000.0
def funLatDeg : Float := 3.0
def funLatFloor : Float := 5.0
def funGsLoDeg : Float := 2.0
def funGsHiDeg : Float := 4.0
def funVLo : Float := 36.0
def funVHi : Float := 46.0
def funTrackDeg : Float := 10.0
def funBankDeg : Float := 10.0
def funVzLo : Float := -4.0
def funVzHi : Float := 0.5
def funFuelLb : Float := 2.0

/-- Landing contact rule and landed (see `flight/src/runway.rs`). -/
def tdSinkMax : Rat := 3
def gearPenMax : Rat := 1 / 2
def landedV : Rat := 1 / 2

/-- Fuel per tank (lb) for low-fuel starts. -/
def lowFuelLb : Float := 8.0

end CityGate.Landing
