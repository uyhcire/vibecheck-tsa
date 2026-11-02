import CityGate.SpecBridge

/-! `sweepcheck [steady]`: `AirframeNear` margins and escape-law outputs on extreme raw-surface flights; `steady`: escapes' settled climb. -/

open CityGate CityGate.Esc CityGate.SpecBridge

def absR (r : Rat) : Rat := if r < 0 then -r else r

def ratD (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

def maxDev (c : Rat × Rat × Rat) (ps : List CitySafety.Pt) : Rat :=
  ps.foldl (fun m q => max m (max (max (absR (q.x - c.1)) (absR (q.y - c.2.1))) (absR (q.z - c.2.2)))) 0

def inRange (u : Surf) : Bool :=
  let ok := fun (x lo hi : Float) => !x.isNaN && lo ≤ x && x ≤ hi
  ok u.elev (-1.0) 1.0 && ok u.ail (-1.0) 1.0 && ok u.rud (-1.0) 1.0 && ok u.thr 0.0 1.0

def probe (name : String) (p0 : Plane) (prog : List (Nat × Surf)) : IO Unit := do
  let mut p := p0
  let mut worst : Rat := 0
  let mut near : Rat := 0
  let mut vmax := 0.0
  let mut undefined := 0
  let mut frames := 0
  let mut states : Array Plane := #[]
  for (n, u) in prog do
    for k in [0:n] do
      let p' := p.step u
      match exactPos p', CitySafety.airframe p.st, CitySafety.airframe p'.st with
      | some c, some ps, some ps' =>
        worst := max worst (maxDev c (ps ++ ps'))
        near := max near (maxDev c ps')
      | _, _, _ => undefined := undefined + 1
      vmax := fmax vmax p'.ob[6]!
      p := p'
      frames := frames + 1
      if k % 384 == 0 then states := states.push p
  let mut bad := 0
  let mut lawWorst : Rat := 0
  let mut nanObs := 0
  for s in states do
    for e in [0:N_ESC] do
      let mut q := s
      let mut l := Law.new e
      for _ in [0:768] do
        let (u, l') := l.step q
        if !inRange u then bad := bad + 1
        let q' := q.step u
        match exactPos q', CitySafety.airframe q.st, CitySafety.airframe q'.st with
        | some c, some ps, some ps' =>
          lawWorst := max lawWorst (maxDev c (ps ++ ps'))
          near := max near (maxDev c ps')
        | _, _, _ => nanObs := nanObs + 1
        vmax := fmax vmax q'.ob[6]!
        q := q'
        l := l'
  (← IO.getStdout).flush
  IO.println s!"{name}: {frames} pilot frames, max airspeed {vmax} m/s; AirframeNear needs h ≥ {ratD near} m; both frame ends within {ratD worst} m (pilot), {ratD lawWorst} m (escapes from {states.size} states x 6); undefined frames {undefined}+{nanObs}; escape outputs out of range {bad}"

def steady : IO Unit := do
  for e in [0:N_ESC - 1] do
    for h in [100.0, 300.0, 500.0, 700.0, 900.0, 1100.0] do
      for v in [26.0, 45.0] do
        let mut p := startPlane 0.0 0.0 h v 0.0 0.0 0.0 1.0 1.0
        let mut l := Law.new e
        let mut z60 := 0.0
        for k in [0:128 * 180] do
          let (u, l') := l.step p
          p := p.step u
          l := l'
          if k == 128 * 60 then z60 := p.pos.2.2
        let o := p.ob
        IO.println s!"esc {e} from {h} m at {v} m/s: after 180 s z {p.pos.2.2} (vz over 60-180 s {(p.pos.2.2 - z60) / 120.0} m/s) vt {o[6]!} alpha {o[13]!} phi {o[7]!}"
        (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args == ["steady"] then steady; return
  let hi := fun (v gam : Float) => planeOf (startPlane 0.0 0.0 2500.0 v gam 0.0 0.0 1.0 1.0).st (startPlane 0.0 0.0 2500.0 v gam 0.0 0.0 1.0 1.0).ob
  probe "vertical dive, full throttle" (hi 60.0 (-0.5)) [(128 * 25, ⟨1.0, 0.0, 0.0, 1.0⟩)]
  probe "dive then full aileron roll" (hi 60.0 (-0.5)) [(128 * 12, ⟨1.0, 0.0, 0.0, 1.0⟩), (128 * 4, ⟨0.0, 1.0, 0.0, 1.0⟩)]
  probe "dive then full pull (max g)" (hi 60.0 (-0.5)) [(128 * 12, ⟨1.0, 0.0, 0.0, 1.0⟩), (128 * 4, ⟨-1.0, 0.0, 0.0, 1.0⟩)]
  probe "dive then pull, roll, rudder" (hi 60.0 (-0.5)) [(128 * 12, ⟨1.0, 0.0, 0.0, 1.0⟩), (128 * 4, ⟨-1.0, 1.0, 1.0, 1.0⟩)]
  probe "spin entry at idle" (hi 30.0 0.0) [(128 * 3, ⟨-1.0, 0.0, 0.0, 0.0⟩), (128 * 15, ⟨-1.0, -1.0, 1.0, 0.0⟩)]
  probe "zoom to a tail slide" (hi 70.0 0.0) [(128 * 4, ⟨-1.0, 0.0, 0.0, 1.0⟩), (128 * 10, ⟨0.0, 0.0, 0.0, 0.0⟩)]
  probe "hammerhead with rudder" (hi 70.0 0.0) [(128 * 3, ⟨-1.0, 0.0, 0.0, 1.0⟩), (128 * 4, ⟨0.0, 0.0, 0.0, 1.0⟩), (128 * 8, ⟨0.0, 0.0, -1.0, 0.0⟩)]
