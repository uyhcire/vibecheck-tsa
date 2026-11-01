import CityGate.Map
import CityGate.Plant

/-! PLACEHOLDER (agent G replaces this file): what a crash is, the clearance test the gate checks every frame, and
its soundness. Keep these three names and types. -/

namespace CityGate

/-- The airframe touches a building or the terrain. -/
def Crash (_p : Plane) : Prop := False

/-- Clearance test at one frame, with `extra` metres of margin on top of the base margin. -/
def clearAt (_extra : Float) (_p : Plane) : Bool := false

theorem clear_sound (e : Float) (p : Plane) : clearAt e p = true → ¬ Crash p := by
  simp [clearAt]

end CityGate
