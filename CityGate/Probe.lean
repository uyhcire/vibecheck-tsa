import CityGate.Gate

/-! Tooling only (diagnosing slow ticks): the one-after-another candidate check, instrumented with timers and
work counters. Not part of any theorem; the end-of-escape scans are mirrored with counters, and checked against the
real ones on every call. -/

namespace CityGate.Esc

/-- `rayClear`, also returning the steps along the ray and the surface lookups made. -/
def rayWork (E : EMap) (px py pz psi grad : Float) : Bool × Nat × Nat := Id.run do
  if grad < 0.02 then return (false, 0, 0)
  let c := psi.cos
  let s := psi.sin
  let mut d := 0.0
  let mut k := 0
  let mut n := 0
  for _ in [0:10000] do
    let x := px + d * c
    let y := py + d * s
    let z := pz + d * grad
    let floor := z - R_BODY - MARGIN
    if floor > E.top then return (true, k, n)
    k := k + 1
    let w := R_BODY + 5.0 + 0.02 * d
    let mut l := -w
    while l ≤ w do
      n := n + 1
      if E.surface (x - l * s) (y + l * c) > floor then return (false, k, n)
      l := l + 0.5 * CELL
    d := d + 0.5 * CELL
  return (false, k, n)

/-- `helixClear`, also returning the raster cells visited. -/
def helixWork (E : EMap) (cx cy r m z : Float) : Bool × Nat := Id.run do
  let floor := z - R_BODY - MARGIN
  if floor > E.top then return (true, 0)
  let r0 := fmax (r - m - R_BODY) 0.0
  let r1 := r + m + R_BODY
  if !E.onMap (cx - r1) (cy - r1) || !E.onMap (cx + r1) (cy + r1) then return (false, 0)
  let pad := CELL * FRAC_1_SQRT_2
  let lo2 := let d := fmax (r0 - pad) 0.0; d * d
  let hi2 := let d := r1 + pad; d * d
  let floor := toF32 floor
  let mut n := 0
  for j in [E.cellY (cy - r1 - pad):E.cellY (cy + r1 + pad) + 1] do
    let dy := E.y0 + (j.toFloat + 0.5) * CELL - cy
    for i in [E.cellX (cx - r1 - pad):E.cellX (cx + r1 + pad) + 1] do
      n := n + 1
      if E.raster[j * E.nx + i]! ≤ floor then continue
      let dx := E.x0 + (i.toFloat + 0.5) * CELL - cx
      let d2 := dx * dx + dy * dy
      if d2 ≥ lo2 && d2 ≤ hi2 then return (false, n)
  return (true, n)

/-- `terminalOK` with its scan's work: the verdict, the kind of scan (0 none, 1 ray, 2 helix), ray steps, and
lookups or cells. -/
def terminalWork (E : EMap) (dir : Float) (hist : Array Hist) : Bool × Nat × Nat × Nat := Id.run do
  if hist.size < 2 * HALF + 1 then return (false, 0, 0, 0)
  let n := hist.size
  let a := seg (hist.extract (n - 2 * HALF - 1) (n - HALF))
  let b := seg (hist.extract (n - HALF - 1) n)
  if fmin a.vzMin b.vzMin < VZ_MIN then return (false, 0, 0, 0)
  let e := b.e
  if dir == 0.0 then
    if fmax a.omega.abs b.omega.abs > 0.01 then return (false, 0, 0, 0)
    if !((a.vzMean - b.vzMean).abs ≤ VZ_SETTLED) then return (false, 0, 0, 0)
    let grad := fmin (0.8 * fmin (a.vzMean / fmax a.vh 1.0) (b.vzMean / fmax b.vh 1.0)) GRAD_MAX
    let (ok, k, w) := rayWork E e.x e.y e.z e.psi grad
    return (ok, 1, k, w)
  else
    let want := -dir
    if a.omega * want ≤ 0.02 || b.omega * want ≤ 0.02 then return (false, 0, 0, 0)
    let circ := fun (s : Seg) =>
      let rr := s.vh / s.omega
      (rr.abs, s.e.x - rr * s.e.psi.sin, s.e.y + rr * s.e.psi.cos)
    let (ra, cax, cay) := circ a
    let (rb, cbx, cby) := circ b
    let dR := (ra - rb).abs
    let dC := ((cax - cbx) * (cax - cbx) + (cay - cby) * (cay - cby)).sqrt
    if dR > 0.1 * rb || dC > 0.1 * rb then return (false, 0, 0, 0)
    let m := 5.0 + 3.0 * (dR + dC)
    let (ok, w) := helixWork E cbx cby rb m e.z
    return (ok, 2, 0, w)

end CityGate.Esc

namespace CityGate
open GateSafety Esc

def nowMs : IO Float := do return (← IO.monoNanosNow).toFloat / 1e6

/-- Fields per candidate in `probeE`'s output. -/
def PROBE_FIELDS : Nat := 14

/-- Tooling only: the one-after-another check of this gate frame, instrumented. Per candidate tried (in order, up to
the first that verifies): frames flown, end (0 clear failed on clearAt, 1 the cap, 2 the street test, 3 end test
passed, 4 horizon), CPU ms in `fly`, `clear`, `term`, `term` calls that ran `terminalOK`, ray scans, ray steps, ray
lookups, helix scans, helix cells, the largest single scan's work, and mismatches between the mirrored and real end
test (should be 0). -/
def probeOn (S : Site) (g : Plane × (Mem × Ctl)) (elev ail rud thr : Float) : IO FloatArray := do
  let cityGate := gateOn S
  let cs := cityGate.propose g.2.1 g.1 g.2.2 ⟨elev, ail, rud, thr⟩
  let mut out : Array Float := #[]
  for c in cs do
    let mut x := (c, g.1)
    let mut frames := 0
    let mut reason := 4
    let mut tf := 0.0
    let mut tc := 0.0
    let mut tt := 0.0
    let mut calls := 0
    let mut rays := 0
    let mut raySteps := 0
    let mut rayLook := 0
    let mut helices := 0
    let mut cells := 0
    let mut maxWork := 0
    let mut bad := 0
    let mut ok := false
    for k in [0:cityGate.horizon + 1] do
      let t0 ← nowMs
      let cl := cityGate.clear x
      let t1 ← if cl then nowMs else nowMs
      tc := tc + (t1 - t0)
      if !cl then
        reason := if !decide (x.1.lk ≤ x.1.cap) then 1 else if !x.1.streetOK x.2 then 2 else 0
        break
      let tm := cityGate.term x
      let t2 ← if tm then nowMs else nowMs
      tt := tt + (t2 - t1)
      let cc := x.1
      if cc.pf == 0 && cc.lk % SAMPLE == 0 && cc.lk ≥ 768 && cc.lk % TERM_EVERY == 0 && cc.law.turning then
        calls := calls + 1
        let (okW, kind, steps, work) := terminalWork S.esc cc.law.dir (cc.record x.2).hist
        if okW != tm then bad := bad + 1
        maxWork := max maxWork work
        if kind == 1 then
          rays := rays + 1; raySteps := raySteps + steps; rayLook := rayLook + work
        else if kind == 2 then
          helices := helices + 1; cells := cells + work
      if tm then
        reason := 3; ok := true; break
      if k == cityGate.horizon then break
      let t3 ← nowMs
      x := cityGate.fly x
      let t4 ← if x.2.ob.size == 0 then nowMs else nowMs
      tf := tf + (t4 - t3)
      frames := frames + 1
    out := out ++ #[frames.toFloat, reason.toFloat, tf, tc, tt, calls.toFloat, rays.toFloat, raySteps.toFloat,
      rayLook.toFloat, helices.toFloat, cells.toFloat, maxWork.toFloat, bad.toFloat, if ok then 1 else 0]
    if ok then break
  return ⟨out⟩

@[export citygate_probe_lean]
def probeE (S : Site) (g : Plane × (Mem × Ctl)) (elev ail rud thr : Float) : IO FloatArray := probeOn S g elev ail rud thr

end CityGate
