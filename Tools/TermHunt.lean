import CityGate.SpecBridge

/-! `termhunt`: search for end-test passes of `cityGate` followed by contact (`TermSoundR`); exits 1 if any. -/

open CityGate CityGate.Esc GateSafety

/-- Float stand-in for `Crash` (6 m cube): contact iff ≤ 0; terrain sampled every 0.5 m. -/
def cubeMargin (p : Plane) : Float := Id.run do
  let (x, y, z) := p.pos
  let mut m := 1.0e9
  for i in [0:25] do
    for j in [0:25] do
      let t := Esc.terrainAt (x - 6.0 + 0.5 * i.toFloat) (y - 6.0 + 0.5 * j.toFloat)
      m := fmin m (z - 6.0 - t)
  for b in boxesF do
    let dx := fmax (fmax (b.xmin - x) (x - b.xmax)) 0.0
    let dy := fmax (fmax (b.ymin - y) (y - b.ymax)) 0.0
    let dz := fmax (fmax (b.zmin - z) (z - b.zmax)) 0.0
    m := fmin m (fmax (fmax dx dy) dz - 6.0)
  return m

/-- xorshift64*. -/
structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, ⟨x⟩)

def Rng.unif (r : Rng) (a b : Float) : Float × Rng :=
  let (u, r) := r.next
  (a + (b - a) * ((u >>> 11).toFloat / 9007199254740992.0), r)

structure Case where
  x : Float
  y : Float
  z : Float
  v : Float
  gam : Float
  psi : Float
  phi : Float
  thr : Float
  up : Surf
  pre : Nat
  uc : Surf
  esc : Nat

def showSurf (u : Surf) : String := s!"{u.elev} {u.ail} {u.rud} {u.thr}"

def Case.show (c : Case) : String :=
  s!"case {c.x} {c.y} {c.z} {c.v} {c.gam} {c.psi} {c.phi} {c.thr} {showSurf c.up} {c.pre} {showSurf c.uc} {c.esc}"

def tall : Array (Box Float) := boxesF.filter fun b => b.zmax - b.zmin ≥ 100.0

def sample (r : Rng) (only : Option Nat := none) : Case × Rng := Id.run do
  let mut r := r
  let u := fun (r : Rng) (a b : Float) => r.unif a b
  let (kind, r1) := u r 0.0 3.0; r := r1
  let kind := match only with | some k => k.toFloat + 0.5 | none => kind
  let (psi, r1) := u r (-PI) PI; r := r1
  let mut x := 0.0
  let mut y := 0.0
  let mut z := 0.0
  let mut psi := psi
  if kind < 1.0 then
    let (bi, r1) := u r 0.0 tall.size.toFloat; r := r1
    let b := tall[bi.toUInt64.toNat]!
    let (d, r1) := u r 15.0 150.0; r := r1
    let (a, r1) := u r (-PI) PI; r := r1
    let (cx, cy) := ((b.xmin + b.xmax) / 2.0, (b.ymin + b.ymax) / 2.0)
    let half := fmax (b.xmax - b.xmin) (b.ymax - b.ymin) / 2.0
    x := cx + (half + d) * a.cos
    y := cy + (half + d) * a.sin
    let (h, r1) := u r 0.4 1.15; r := r1
    z := b.zmin + h * (b.zmax - b.zmin)
    let (dpsi, r1) := u r (-1.2) 1.2; r := r1
    psi := Float.atan2 (cy - y) (cx - x) + dpsi
  else if kind < 2.0 then
    let (side, r1) := u r 0.0 4.0; r := r1
    let (along, r1) := u r (-3000.0) 3000.0; r := r1
    let (m, r1) := u r 2450.0 3060.0; r := r1
    let s := side.toUInt64.toNat
    (x, y) := if s == 0 then (m, along) else if s == 1 then (-m, along) else if s == 2 then (along, m) else (along, -m)
    let (agl, r1) := u r 10.0 220.0; r := r1
    z := Esc.terrainAt x y + agl
  else
    let (x1, r1) := u r (-2800.0) 2800.0; r := r1
    let (y1, r1) := u r (-2800.0) 2800.0; r := r1
    let (agl, r1) := u r 20.0 400.0; r := r1
    x := x1; y := y1
    z := surface x y + agl
  let (slow, r1) := u r 0.0 1.0; r := r1
  let (v, r1) := if slow < 0.3 then u r 22.0 30.0 else u r 30.0 70.0; r := r1
  let (gam, r1) := u r (-0.4) 0.3; r := r1
  let (phi, r1) := u r (-1.2) 1.2; r := r1
  let (thr, r1) := u r 0.0 1.0; r := r1
  let (pre, r1) := u r 0.0 192.0; r := r1
  let mut sv : Array Float := #[]
  for _ in [0:8] do
    let (a, r1) := u r (-1.0) 1.0; r := r1
    sv := sv.push a
  let (t1, r1) := u r 0.0 1.0; r := r1
  let (t2, r1) := u r 0.0 1.0; r := r1
  let (e, r1) := u r 0.0 6.0; r := r1
  return ({ x, y, z, v, gam, psi, phi, thr, up := ⟨sv[0]!, sv[1]!, sv[2]!, t1⟩, pre := pre.toUInt64.toNat,
            uc := ⟨sv[4]!, sv[5]!, sv[6]!, t2⟩, esc := e.toUInt64.toNat % N_ESC }, r)

def Case.plane (c : Case) : Plane := Id.run do
  let mut p := startPlane c.x c.y c.z c.v c.gam c.psi c.phi (c.gam.cos / c.phi.cos) c.thr
  for _ in [0:c.pre] do
    p := p.step c.up
  return p

def rollout (x0 : Ctl × Plane) : Option (Nat × (Ctl × Plane)) := Id.run do
  let mut x := x0
  for k in [0:cityGate.horizon + 1] do
    if !cityGate.clear x then return none
    if cityGate.term x then return some (k, x)
    x := cityGate.fly x
  return none

/-- Climb rate from thrust over each settling half: mean climb plus the kinetic-energy change as height (m/s). -/
def energyRates (x : Ctl × Plane) : Float × Float :=
  let h := (x.1.record x.2).hist
  let rate := fun (lo hi : Nat) =>
    let a := h[lo]!
    let b := h[hi]!
    let v2 := fun (q : Hist) => q.vh * q.vh + q.vz * q.vz
    (seg (h.extract lo (hi + 1))).vzMean + (v2 b - v2 a) / (2.0 * G0 * (b.t - a.t))
  (rate 0 32, rate 32 64)

structure Res where
  energy : Float × Float := (0, 0)
  passK : Nat
  minAfter : Float
  tMin : Float
  posMin : Float × Float × Float
  firstHit : Option Nat
  ending : String

def continueFrom (x0 : Ctl × Plane) (maxF : Nat) : Res := Id.run do
  let mut x := x0
  let mut r : Res := { passK := 0, minAfter := 1.0e9, tMin := 0.0, posMin := (0, 0, 0), firstHit := none, ending := "timeout" }
  let mut skip := 0
  for k in [0:maxF] do
    let (_, _, z) := x.2.pos
    if z - 6.0 > top + 20.0 then
      r := { r with ending := "above-top" }
      break
    if skip == 0 then
      let m := cubeMargin x.2
      if m < r.minAfter then r := { r with minAfter := m, tMin := k.toFloat * DT_JSB, posMin := x.2.pos }
      if m ≤ 0.0 && r.firstHit.isNone then r := { r with firstHit := some k }
      if m < -20.0 then
        r := { r with ending := "deep-contact" }
        break
      -- at most 1.2 m of travel per frame, so the margin cannot reach 0 sooner
      skip := Nat.min 64 (fmax 0.0 ((m - 2.0) / 1.2)).floor.toUInt64.toNat
    else skip := skip - 1
    x := cityGate.fly x
  return r

def runCase (c : Case) (maxF : Nat) : Option Res :=
  let p := c.plane
  let ctl := Ctl.fresh c.uc CHECK_EVERY (Law.new c.esc) 0.0 HORIZON_FRAMES
  match rollout (ctl, p) with
  | none => none
  | some (k, x) => some { continueFrom x maxF with passK := k, energy := energyRates x }

def fmtP (p : Float × Float × Float) : String := s!"[{p.1}, {p.2.1}, {p.2.2}]"

def hunt (seed : Nat) (n : Nat) (maxF : Nat) (esc kind : Option Nat := none) : IO Nat := do
  let mut r : Rng := ⟨(seed.toUInt64 + 1) * 0x9E3779B97F4A7C15⟩
  let mut passed := 0
  let mut best := 1.0e9
  let mut eOK := 0
  let mut hits := 0
  let mut hitsEOK := 0
  let t0 ← IO.monoMsNow
  for i in [0:n] do
    let (c, r1) := sample r kind
    r := r1
    let c := match esc with | some e => { c with esc := e } | none => c
    match runCase c maxF with
    | none => pure ()
    | some res =>
      passed := passed + 1
      let hit := res.firstHit.isSome
      let ok := fmin res.energy.1 res.energy.2 ≥ VZ_MIN
      if ok then eOK := eOK + 1
      if hit then hits := hits + 1
      if hit && ok then hitsEOK := hitsEOK + 1
      if hit || res.minAfter < best || res.minAfter < 2.0 then
        best := fmin best res.minAfter
        (← IO.getStdout).flush
        IO.println s!"{if hit then "HIT" else "near"} i={i} esc={c.esc} pass@{res.passK} energy={res.energy.1},{res.energy.2} minAfter={res.minAfter} at t={res.tMin} pos={fmtP res.posMin} end={res.ending} firstHit={res.firstHit}\n  {c.show}"
    if (i + 1) % 50 == 0 then
      IO.eprintln s!"seed {seed}: {i + 1} cases, {passed} passed, best {best}, {(← IO.monoMsNow) - t0} ms"
  IO.println s!"seed {seed}: {n} cases, {passed} rollouts passed the end test ({eOK} also pass an energy-rate check), {hits} hit ({hitsEOK} of them pass it), closest continuation {best}"
  return hits

/-- A made-up controller (a settled 2 m helix history) that passes `term` beside a tower 17 m ahead. -/
def unres : IO Unit := do
  for b in tall do
    for face in [0:4] do
      let (cx, cy) := ((b.xmin + b.xmax) / 2.0, (b.ymin + b.ymax) / 2.0)
      let (x, y, psiE) :=
        if face == 0 then (b.xmin - 17.0, cy, 0.0) else if face == 1 then (b.xmax + 17.0, cy, PI)
        else if face == 2 then (cx, b.ymin - 17.0, FRAC_PI_2) else (cx, b.ymax + 17.0, -FRAC_PI_2)
      let mut hi := 0.0
      for i in [0:13] do
        for j in [0:13] do
          hi := fmax hi (surface (x - 15.0 + 2.5 * i.toFloat) (y - 15.0 + 2.5 * j.toFloat))
      let z := fmax (hi + 10.0) (Esc.terrainAt x y + 30.0)
      if z > b.zmax - 30.0 then continue
      let p := startPlane x y z 40.0 0.04 psiE 0.0 1.0 1.0
      let o := p.ob
      let psi0 := Float.atan2 (obN o) (obE o)
      let vh := (obN o * obN o + obE o * obE o).sqrt
      if -(obD o) < 1.0 then continue
      let (px, py, _) := p.pos
      let lk := 768
      let omega := -20.0
      let rr := vh / omega
      let cbx := px - rr * psi0.sin
      let cby := py + rr * psi0.cos
      let psiAt := fun (i : Nat) => psi0 + omega * ((i.toFloat - 64.0) * 8.0 * DT_JSB)
      let hist : Array Hist := (List.range 64).toArray.map fun i =>
        let ps := psiAt i
        { t := (lk.toFloat - 8.0 * (64.0 - i.toFloat)) * DT_JSB, x := cbx + rr * ps.sin, y := cby - rr * ps.cos,
          z := z - 0.1 * (64.0 - i.toFloat), psi := ps, vh, vz := 2.0, v := vh }
      let law := { Law.new 2 with t := 6.0, psiRef := psi0 }
      let c : Ctl := { pilot := ⟨0, 0, 0, 0⟩, pf := 0, law, lk, hist, psiPrev := psi0, extra := 0.0, cap := HORIZON_FRAMES }
      if !cityGate.term (c, p) then continue
      let mut x := (c, p)
      for k in [0:400] do
        let m := cubeMargin x.2
        if m ≤ 0.0 then
          IO.println s!"term (c, p) = true; contact after {k} frames at {fmtP x.2.pos}, cube margin {m}"
          IO.println s!"tower x [{b.xmin}, {b.xmax}] y [{b.ymin}, {b.ymax}] z [{b.zmin}, {b.zmax}]; start {fmtP p.pos}, heading {psiE}"
          let mut y := x
          for _ in [0:40] do y := cityGate.fly y
          IO.println s!"40 frames later: {fmtP y.2.pos}, cube margin {cubeMargin y.2}"
          return
        x := cityGate.fly x
  IO.println "no unrestricted witness found"

def traceCase (c : Case) (secs : Nat) : IO Unit := do
  let ctl := Ctl.fresh c.uc CHECK_EVERY (Law.new c.esc) 0.0 HORIZON_FRAMES
  match rollout (ctl, c.plane) with
  | none => IO.println "end test never passed"
  | some (k, x0) =>
    IO.println s!"end test passed at frame {k}; energy rates {energyRates x0}; hist settled window:"
    let h := (x0.1.record x0.2).hist
    let a := seg (h.extract 0 33)
    let b := seg (h.extract 32 65)
    IO.println s!"  half a: omega {a.omega} vh {a.vh} vzMin {a.vzMin} vzMean {a.vzMean}; half b: omega {b.omega} vh {b.vh} vzMin {b.vzMin} vzMean {b.vzMean}"
    let mut x := x0
    for f in [0:128 * secs + 1] do
      if f % 128 == 0 then
        let o := x.2.ob
        IO.println s!"t {f / 128} pos {fmtP x.2.pos} vt {o[6]!} vz {-(obD o)} phi {o[7]!} theta {o[8]!} alpha {o[13]!} rpm {o[18]!} ia {x.1.law.ia} ib {x.1.law.ib} iphi {x.1.law.iphi} elev {(x.1.law.step x.2).1.elev} margin {cubeMargin x.2}"
      x := cityGate.fly x

def apSurf (o : FloatArray) (thetaC phiC thr : Float) : Surf :=
  ⟨clamp (-2.0 * (thetaC - o[8]!) + 0.6 * o[11]!) (-1.0) 1.0, clamp (2.0 * (phiC - o[7]!) - 0.4 * o[10]!) (-1.0) 1.0,
   clamp (1.5 * o[14]!) (-1.0) 1.0, thr⟩

/-- Closed loop through `cityGate.frame` from spec start `si`: fly at `(tx, ty)` descending to `ha`, then hold `uf`. -/
def closed (si : Nat) (tx ty ha dB : Float) (uf : Option Surf) (secs : Nat) : IO Unit := do
  let some c := CitySafety.startConds[si]? | return
  let pl := SpecBridge.firstPlane c.state
  let mut g : Plane × (Mem × Ctl) := (pl, (cityGate.m₀, cityGate.start pl))
  IO.println s!"start {si}: init check {cityGate.rolloutOK cityGate.horizon (g.2.2, g.1)}"
  let mut best := 1.0e9
  let mut final := false
  let mut commits := 0
  for f in [0:128 * secs] do
    let o := g.1.ob
    let (x, y, z) := g.1.pos
    if !final && ((tx - x) * (tx - x) + (ty - y) * (ty - y)).sqrt < dB then
      final := true
      IO.println s!"t {f.toFloat / 128.0}: final phase at {fmtP g.1.pos}, vt {o[6]!}"
    let brg := Float.atan2 (tx - x) (ty - y)
    let track := Float.atan2 (obE o) (obN o)
    let u := match final, uf with
      | true, some w => w
      | _, _ => apSurf o (clamp (0.01 * (ha - z)) (-0.3) 0.12) (clamp (wrap (brg - track)) (-0.5) 0.5) (if z > ha + 20.0 then 0.0 else 0.6)
    let wasC := g.2.1.committed
    g := cityGate.frame g u
    if g.2.1.committed && !wasC then commits := commits + 1
    if f % 4 == 0 then
      let m := cubeMargin g.1
      best := fmin best m
      if f % 1280 == 0 then
        IO.println s!"t {f.toFloat / 128.0} pos {fmtP g.1.pos} vt {g.1.ob[6]!} vz {-(obD g.1.ob)} committed {g.2.1.committed} esc {g.2.2.law.esc} margin {m}"
        (← IO.getStdout).flush
      if m ≤ 0.0 then
        IO.println s!"CONTACT t {f.toFloat / 128.0} pos {fmtP g.1.pos} margin {m}; {if g.2.1.committed then "gate escape" else "pilot"} in control (escape {g.2.2.law.esc}, law t {g.2.2.law.t}); commits {commits}"
        return
  IO.println s!"no contact in {secs} s; closest cube margin {best}; commits {commits}"

/-- Closed loop from a spec start: fly to a random city point and height, then random raw-surface holds (slow flight,
stalls, rolls) for `secs` s. -/
def closedRand (seed : Nat) (secs : Nat) (edge : Bool := false) : IO Unit := do
  let mut r : Rng := ⟨(seed.toUInt64 + 7) * 0x9E3779B97F4A7C15⟩
  let (si, r1) := r.unif 0.0 4.0; r := r1
  let (bi, r1) := r.unif 0.0 tall.size.toFloat; r := r1
  let b := tall[bi.toUInt64.toNat]!
  let (a, r1) := r.unif (-PI) PI; r := r1
  let (d, r1) := r.unif 60.0 400.0; r := r1
  let (m, r1) := r.unif 2450.0 2950.0; r := r1
  let (along, r1) := r.unif (-2500.0) 2500.0; r := r1
  let (agl, r1) := r.unif 40.0 250.0; r := r1
  let side := (a + PI) * 2.0 / PI
  let (ex, ey) := if side < 1.0 then (m, along) else if side < 2.0 then (-m, along) else if side < 3.0 then (along, m) else (along, -m)
  let tx := if edge then ex else (b.xmin + b.xmax) / 2.0 + d * a.cos
  let ty := if edge then ey else (b.ymin + b.ymax) / 2.0 + d * a.sin
  let (hf, r1) := r.unif 0.6 1.2; r := r1
  let ha := if edge then Esc.terrainAt ex ey + agl else fmax (b.zmax * hf) 150.0
  let mut segs : Array (Nat × Surf) := #[]
  for _ in [0:20] do
    let (dur, r1) := r.unif 0.2 4.0; r := r1
    let (kind, r1) := r.unif 0.0 4.0; r := r1
    let (q1, r1) := r.unif (-1.0) 1.0; r := r1
    let (q2, r1) := r.unif (-1.0) 1.0; r := r1
    let (q3, r1) := r.unif 0.0 1.0; r := r1
    let u : Surf := if kind < 1.0 then ⟨-1.0, q1 * 0.3, 0.0, 0.0⟩ else if kind < 2.0 then ⟨q1, (if q2 < 0.0 then -1.0 else 1.0), q2, q3⟩
      else if kind < 3.0 then ⟨-0.3 + 0.2 * q1, 0.0, 0.0, 0.0⟩ else ⟨q1, q2, (q3 - 0.5) * 2.0, q3⟩
    segs := segs.push ((dur * 128.0).toUInt64.toNat, u)
  let some c := CitySafety.startConds[si.toUInt64.toNat]? | return
  let pl := SpecBridge.firstPlane c.state
  let mut g : Plane × (Mem × Ctl) := (pl, (cityGate.m₀, cityGate.start pl))
  let mut fArrive : Option Nat := none
  let mut best := 1.0e9
  let mut commits := 0
  IO.println s!"seed {seed}: start {si.toUInt64}, target ({tx}, {ty}) at {ha} m beside tower top {b.zmax}"
  (← IO.getStdout).flush
  for f in [0:128 * (secs + 240)] do
    let o := g.1.ob
    let (x, y, z) := g.1.pos
    if fArrive.isNone && ((tx - x) * (tx - x) + (ty - y) * (ty - y)).sqrt < 150.0 && (z - ha).abs < 40.0 then
      fArrive := some f
      IO.println s!"arrived t {f.toFloat / 128.0} at {fmtP g.1.pos} vt {o[6]!}"
      (← IO.getStdout).flush
    let u := match fArrive with
      | none =>
        let brg := Float.atan2 (tx - x) (ty - y)
        let track := Float.atan2 (obE o) (obN o)
        let dist := ((tx - x) * (tx - x) + (ty - y) * (ty - y)).sqrt
        let phiC := if dist < 150.0 then 0.5 else clamp (wrap (brg - track)) (-0.5) 0.5
        apSurf o (clamp (0.01 * (ha - z)) (-0.3) 0.12) phiC (if z > ha + 20.0 then 0.0 else 0.5)
      | some f0 => Id.run do
        let mut acc := f0
        let mut w : Surf := ⟨-1.0, 0.0, 0.0, 0.0⟩
        for (n, s) in segs do
          if f < acc + n then
            w := s
            break
          acc := acc + n
        return w
    if let some f0 := fArrive then
      if f > f0 + 128 * secs then break
    let wasC := g.2.1.committed
    g := cityGate.frame g u
    if g.2.1.committed && !wasC then commits := commits + 1
    if f % 4 == 0 then
      let m := cubeMargin g.1
      best := fmin best m
      if m ≤ 0.0 then
        IO.println s!"CONTACT t {f.toFloat / 128.0} pos {fmtP g.1.pos} margin {m}; {if g.2.1.committed then "gate escape" else "pilot"} in control (escape {g.2.2.law.esc}, law t {g.2.2.law.t}); commits {commits}"
        (← IO.getStdout).flush
        return
  IO.println s!"seed {seed}: no contact; arrived {fArrive.isSome}; closest cube margin {best}; commits {commits}"
  (← IO.getStdout).flush

/-- Exit status 1 if any end-test pass was followed by contact. -/
def caseAt (seed i : Nat) : Case := Id.run do
  let mut r : Rng := ⟨(seed.toUInt64 + 1) * 0x9E3779B97F4A7C15⟩
  let mut c : Case := (sample r).1
  for _ in [0:i + 1] do
    let (c1, r1) := sample r
    c := c1
    r := r1
  return c

/-- Replays a witness list (lines `SEED I …`): whether each case still passes the end test, and if so whether its
continuation makes contact. -/
def witnesses (path : String) (maxF : Nat) : IO Unit := do
  let mut (n, pass, hit) := (0, 0, 0)
  for l in ← IO.FS.lines path do
    let w := (l.splitOn " ").filter (· ≠ "")
    let some seed := w[0]? >>= String.toNat? | continue
    let some i := w[1]? >>= String.toNat? | continue
    n := n + 1
    match runCase (caseAt seed i) maxF with
    | none => IO.println s!"{seed} {i}: end test never passes"
    | some res =>
      pass := pass + 1
      if res.firstHit.isSome then hit := hit + 1
      IO.println s!"{seed} {i}: passes at frame {res.passK}, continuation {if res.firstHit.isSome then "CONTACT" else "clear"}, min {res.minAfter} at t {res.tMin}, end {res.ending}"
    (← IO.getStdout).flush
  IO.println s!"{n} witnesses: {pass} still pass the end test, {hit} of them make contact"

/-- How many of the first `n` cases of `seed` pass the end test (no continuation). -/
def passCount (seed n : Nat) : IO Unit := do
  let mut r : Rng := ⟨(seed.toUInt64 + 1) * 0x9E3779B97F4A7C15⟩
  let mut pass := 0
  for _ in [0:n] do
    let (c, r1) := sample r
    r := r1
    if (rollout (Ctl.fresh c.uc CHECK_EVERY (Law.new c.esc) 0.0 HORIZON_FRAMES, c.plane)).isSome then pass := pass + 1
  IO.println s!"seed {seed}: {pass} of {n} rollouts pass the end test"

/-- Each escape's rollout from the spec's 4 starts (`InitChecked` needs one to pass from each). -/
def specStarts : IO Unit := do
  for c in CitySafety.startConds do
    let p := SpecBridge.firstPlane c.state
    IO.println s!"start {fmtP p.pos} v {p.ob[6]!}"
    for e in List.range N_ESC do
      let mut x := (Ctl.fresh ⟨0, 0, 0, 0⟩ 0 (Law.new e) 0.0 HORIZON_FRAMES, p)
      let mut out := "horizon"
      for k in [0:cityGate.horizon + 1] do
        if !cityGate.clear x then
          out := s!"clearance fails at frame {k}, {fmtP x.2.pos}"
          break
        if cityGate.term x then
          out := s!"end test passes at frame {k}"
          break
        x := cityGate.fly x
      IO.println s!"  escape {e}: {out}; at the end v {x.2.ob[6]!}, law t {x.1.law.t}"

def huntExit (h : Nat) : IO UInt32 := do
  if h > 0 then IO.eprintln s!"termhunt: {h} end-test passes followed by contact"
  return if h > 0 then 1 else 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => huntExit (← hunt 12 3000 (128 * 400))
  | ["unres"] => unres; return 0
  | ["witnesses", path] => witnesses path (128 * 400); return 0
  | ["witnesses", path, secs] => witnesses path (128 * secs.toNat!); return 0
  | ["pass", seed, n] => passCount seed.toNat! n.toNat!; return 0
  | ["starts"] => specStarts; return 0
  | ["hunt", seed, n] => huntExit (← hunt seed.toNat! n.toNat! (128 * 400))
  | ["hunt", seed, n, secs] => huntExit (← hunt seed.toNat! n.toNat! (128 * secs.toNat!))
  | ["hunt", seed, n, secs, esc, kind] =>
    huntExit (← hunt seed.toNat! n.toNat! (128 * secs.toNat!) esc.toNat? kind.toNat?)
  | ["trace", seed, i] | ["trace", seed, i, _] =>
    let mut r : Rng := ⟨(seed.toNat!.toUInt64 + 1) * 0x9E3779B97F4A7C15⟩
    let mut c : Case := (sample r).1
    for _ in [0:i.toNat! + 1] do
      let (c1, r1) := sample r
      c := c1
      r := r1
    IO.println c.show
    traceCase c ((args[3]? >>= String.toNat?).getD 200)
    return 0
  | ["closed", si, tx, ty, ha, dB, fin, secs] =>
    let pf := fun (s : String) => (s.toInt?.map Float.ofInt).getD 0.0
    let uf : Option Surf := match fin with
      | "dive" => some ⟨1.0, 0.0, 0.0, 0.0⟩
      | "spiral" => some ⟨0.3, 1.0, 0.0, 0.0⟩
      | "stall" => some ⟨-1.0, 0.0, 0.0, 0.0⟩
      | "stallturn" => some ⟨-1.0, 1.0, 1.0, 0.0⟩
      | _ => none
    closed si.toNat! (pf tx) (pf ty) (pf ha) (pf dB) uf secs.toNat!
    return 0
  | ["closedrand", seed0, n, secs] => do
    for k in [0:n.toNat!] do closedRand (seed0.toNat! + k) secs.toNat!
    return 0
  | ["closedrand", seed0, n, secs, "edge"] => do
    for k in [0:n.toNat!] do closedRand (seed0.toNat! + k) secs.toNat! true
    return 0
  | _ =>
    IO.println "usage: termhunt [hunt SEED N [SECS [ESC KIND]] | trace SEED I [SECS] | unres | closed ... | closedrand SEED N SECS [edge]]"
    return 2
