import CityGate.SpecBridge

/-! Numeric check of the bridge's start obligations, as `SpecBridgeNative` decides them. From each of the spec's 4
starts, after the first frame, the gate's initial escape must check out (`InitChecked`), and the start must be
crash-free (`startClearB`). Run: `lake build specbridgeinit && .lake/build/bin/specbridgeinit`. -/

open CityGate CityGate.SpecBridge

def main : IO Unit := do
  let mut allOk := true
  let mut allClear := true
  for c in CitySafety.startConds do
    let pl := firstPlane c.state
    let ctl := cityGate.start pl
    let ok := cityGate.rolloutOK cityGate.horizon (ctl, pl)
    let clr := startClearB c.state
    allOk := allOk && ok
    allClear := allClear && clr
    IO.println s!"start ({c.x}, {c.y}, {c.z}) psi {c.psi}: start escape {ctl.law.esc}, initial check {ok}, crash-free {clr}"
  IO.println s!"InitChecked on all 4 starts: {allOk}; all starts crash-free: {allClear}"
