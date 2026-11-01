import CityGate.SpecBridgeNear

/-! Numeric check of `InitChecked cityGate GInit`, the bridge's start assumption: from each of the spec's 4 starts,
after the first frame, the gate's initial escape checks out. Also flies `specFilter` from each start under a few
pilot commands and reports the margins of `AirframeNear`, `PoseBounded` and `ReportMatchesObs` along the way.
`lake build specbridgeinit && .lake/build/bin/specbridgeinit [frames]`. -/

open CityGate CityGate.SpecBridge

def maxDev (c : Rat × Rat × Rat) (ps : List CitySafety.Pt) : Rat :=
  ps.foldl (fun m q => max m (max (max (absR (q.x - c.1)) (absR (q.y - c.2.1))) (absR (q.z - c.2.2)))) 0

def ratD (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

def main (args : List String) : IO Unit := do
  let frames := (args.head? >>= String.toNat?).getD 0
  let names := ["north", "east", "south", "west"]
  let mut allOk := true
  for (c, nm) in CitySafety.startConds.zip names do
    let pl := firstPlane c.state
    let ctl := cityGate.start pl
    let ok := cityGate.rolloutOK cityGate.horizon (ctl, pl)
    allOk := allOk && ok
    IO.println s!"{nm}: start escape {ctl.law.esc}, initial check {ok}, position {pl.pos.1} {pl.pos.2.1} {pl.pos.2.2}"
  IO.println s!"InitChecked on all 4 starts: {allOk}"
  if frames == 0 then return
  let pilots : List (String × CitySafety.Surfaces) :=
    [("idle", ⟨0, 0, 0, 0⟩), ("dive", ⟨1, 0, 0, 1⟩), ("bank", ⟨-0.3, 1, 0, 1⟩)]
  for (c, nm) in CitySafety.startConds.zip names do
    for (pn, u) in pilots do
      let mut p : JsbExact.State Float × Mem' := (c.state, none)
      let mut worst : Rat := 0
      let mut inRange := true
      let mut defined := true
      let mut tbMax : Rat := 0
      let mut gap : Rat := 0
      let mut cgIn := true
      for _ in [0:frames] do
        let a := (specFilter.act p.2 p.1 u).1
        inRange := inRange && a.clamp.elev.toBits == a.elev.toBits && a.clamp.ail.toBits == a.ail.toBits &&
          a.clamp.rud.toBits == a.rud.toBits && a.clamp.thr.toBits == a.thr.toBits
        let p' := specFilter.frame p u
        match exactPos (refPlane p'), CitySafety.airframe p'.1 with
        | some e, some ps => worst := max worst (maxDev e ps)
        | _, _ => defined := false
        match (tb2lEntries p'.1).mapM CitySafety.ratOf with
        | some T => tbMax := T.foldl (fun m t => max m (absR t)) tbMax
        | none => defined := false
        match CitySafety.ratOf p'.1.cg.x, CitySafety.ratOf p'.1.cg.y, CitySafety.ratOf p'.1.cg.z with
        | some x, some y, some z => cgIn := cgIn && decide (cgLo.1 ≤ x ∧ x ≤ cgHi.1 ∧ cgLo.2.1 ≤ y ∧ y ≤ cgHi.2.1 ∧
            cgLo.2.2 ≤ z ∧ z ≤ cgHi.2.2)
        | _, _, _ => defined := false
        let rep := CitySafety.report p'.1
        match exactPos (refPlane p'), CitySafety.ratOf rep.loc.y, CitySafety.ratOf rep.loc.z, CitySafety.ratOf rep.hsl with
        | some e, some ly, some lz, some hs =>
          gap := max gap (max (max (absR (ly * CitySafety.ft - e.1)) (absR (lz * CitySafety.ft - e.2.1)))
            (absR (hs * CitySafety.ft - e.2.2)))
        | _, _, _, _ => defined := false
        p := p'
      IO.println s!"{nm} {pn}: {frames} frames, airframe within {ratD worst} m of the reported position (all defined: {defined}), controls in range: {inRange}; max |Tb2l| {ratD tbMax}, CG in box {cgIn}, report-obs gap {ratD gap} m"
