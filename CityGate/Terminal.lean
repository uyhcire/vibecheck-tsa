import CityGate.Map
import CityGate.Plant

/-! The end-of-escape test of `flight/src/envfilter.rs` (`terminal`, `helix_clear`, `ray_clear`) and the 2.5 m
max-height raster it reads (`World::rasterize`, `World::surface`), ported over `Float` with Rust's operation
order. Not trusted: the gate's theorem assumes the end-of-escape test is sound (`TermSound`). -/

namespace CityGate.Esc

/-! ### Float helpers with Rust's `f64` semantics -/

def PI : Float := 3.141592653589793
def FRAC_PI_2 : Float := 1.5707963267948966
def FRAC_1_SQRT_2 : Float := 0.7071067811865476
def NAN : Float := 0.0 / 0.0

/-- `f64::min` (a NaN argument is ignored). -/
def fmin (a b : Float) : Float := if a.isNaN then b else if b.isNaN then a else if b < a then b else a
/-- `f64::max` (a NaN argument is ignored). -/
def fmax (a b : Float) : Float := if a.isNaN then b else if b.isNaN then a else if a < b then b else a
/-- `f64::clamp`. -/
def clamp (x lo hi : Float) : Float := if x < lo then lo else if x > hi then hi else x
/-- `f64::signum`. -/
def signum (x : Float) : Float := if x.isNaN then x else if x.toBits >>> 63 == 1 then -1.0 else 1.0

/-- C `fmod` for finite `x` and `y ≠ 0`: the remainder is representable, so `fma` gives it exactly once the
quotient is right. -/
def fmod (x y : Float) : Float :=
  let ax := x.abs
  let ay := y.abs
  if ax < ay then x
  else
    let q := (ax / ay).floor
    let r0 := Float.fma (-q) ay ax
    let r := if r0 < 0.0 then Float.fma (-(q - 1.0)) ay ax
      else if r0 ≥ ay then Float.fma (-(q + 1.0)) ay ax else r0
    if x < 0.0 then -r else r

/-- `f64::rem_euclid`. -/
def remEuclid (x y : Float) : Float := let r := fmod x y; if r < 0.0 then r + y.abs else r

/-- Angle to `[-π, π)` (`wrap`). -/
def wrap (a : Float) : Float := remEuclid (a + PI) (2.0 * PI) - PI

/-- `x as f32 as f64`. -/
def toF32 (x : Float) : Float := x.toFloat32.toFloat

/-! ### The map in Rust's representation -/

def MAP_HALF : Float := 3000.0
def CELL : Float := 2.5
def NC : Nat := 2400
def R_BODY : Float := 4.5
def MARGIN : Float := 4.0
def TSP : Float := 20.0
def TN : Nat := 301

/-- Terrain vertex heights as Rust holds them (`f32`, from the shortest round-trip decimals). -/
def terr : FloatArray :=
  ⟨terrainDec.map fun d => let f := Float32.ofScientific d.m true d.e; (if d.neg then -f else f).toFloat⟩

/-- `World::terrain`: barycentric on the render triangulation, clamped to the grid. -/
def terrainAt (x y : Float) : Float :=
  let fx := clamp ((x + MAP_HALF) / TSP) 0.0 ((TN - 1).toFloat - 1e-9)
  let fy := clamp ((y + MAP_HALF) / TSP) 0.0 ((TN - 1).toFloat - 1e-9)
  let i := fx.toUInt64.toNat
  let j := fy.toUInt64.toNat
  let u := fx - i.toFloat
  let v := fy - j.toFloat
  let h00 := terr[j * TN + i]!
  let h10 := terr[j * TN + i + 1]!
  let h01 := terr[(j + 1) * TN + i]!
  let h11 := terr[(j + 1) * TN + i + 1]!
  if u ≥ v then h00 + u * (h10 - h00) + v * (h11 - h10) else h00 + v * (h01 - h00) + u * (h11 - h01)

/-- Cell index of a coordinate (`ci` in `rasterize` and `helix_clear`). -/
def cellIdx (v : Float) : Nat := Nat.min (fmax ((v + MAP_HALF) / CELL).floor 0.0).toUInt64.toNat (NC - 1)

/-- `World::rasterize`: per 2.5 m cell, the max of the terrain at its corners and of every overlapping box top,
in `f32`. -/
def buildRaster : FloatArray := Id.run do
  let np := NC + 1
  let mut corner : FloatArray := FloatArray.emptyWithCapacity (np * np)
  for j in [0:np] do
    for i in [0:np] do
      corner := corner.push (toF32 (terrainAt (-MAP_HALF + i.toFloat * CELL) (-MAP_HALF + j.toFloat * CELL)))
  let mut raw : FloatArray := FloatArray.emptyWithCapacity (NC * NC)
  for j in [0:NC] do
    for i in [0:NC] do
      raw := raw.push (fmax (fmax (fmax corner[j * np + i]! corner[j * np + i + 1]!) corner[(j + 1) * np + i]!)
        corner[(j + 1) * np + i + 1]!)
  for b in boxesF do
    let z := toF32 b.zmax
    for j in [cellIdx b.ymin:cellIdx b.ymax + 1] do
      for i in [cellIdx b.xmin:cellIdx b.xmax + 1] do
        raw := raw.set! (j * NC + i) (fmax raw[j * NC + i]! z)
  return raw

def raster : FloatArray := buildRaster

/-- Highest raw cell on the map (`World::raw_top`). -/
def top : Float := raster.foldl (fun m h => fmax m h) (-1.7976931348623157e308)

/-- `World::surface`: ground or roof height below `(x, y)`. -/
def surface (x y : Float) : Float := raster[cellIdx y * NC + cellIdx x]!

def onMap (x y : Float) : Bool := x.abs < MAP_HALF && y.abs < MAP_HALF

/-! ### The end-of-escape test -/

/-- Path sample spacing (frames), terminal-test start (s) and spacing (frames), required climb (m/s), and the
settling window (samples per half). -/
def SAMPLE : Nat := 8
def T_TERM : Float := 6.0
def TERM_EVERY : Nat := 64
def VZ_MIN : Float := 1.0
def HALF : Nat := 32
/-- Settled climb: the two windows' mean climb rates (m/s) differ by at most this. -/
def VZ_SETTLED : Float := 1.0
/-- Cap on the straight escape's ray gradient: 0.8 of its settled climb gradient (about 0.14). -/
def GRAD_MAX : Float := 0.11
/-- Helix ending (`V_HELIX_MIN` … `E_AIR` in Rust): lowest settled airspeed per end-set kind, airspeed agreement of
the halves, radius and centre agreement as fractions of the radius, and the airframe half-size widening the annulus. -/
def V_HELIX_MIN : Array Float := #[0.0, 37.5, 39.5]
def V_SETTLED : Float := 1.0
def R_SETTLED : Float := 0.03
def C_SETTLED : Float := 0.05
def E_AIR : Float := 7.0
def G0T : Float := 9.80665
/-- Level-off ending: the whole window at least `Z_LEVEL` (m) high at a mean airspeed of at least `V_LEVEL` (m/s). -/
def Z_LEVEL : Float := 980.0
def V_LEVEL : Float := 30.0

/-- `rho_of`: the law's density model. -/
def rhoT (h : Float) : Float := 1.225 * (fmax (1.0 - 2.2558e-5 * h) 0.5).pow 4.256

structure Hist where
  t : Float
  x : Float
  y : Float
  z : Float
  psi : Float
  vh : Float
  vz : Float
  v : Float
  deriving Inhabited

structure Seg where
  omega : Float
  vh : Float
  vzMin : Float
  vzMean : Float
  vMean : Float
  zMin : Float
  de : Float
  e : Hist

/-- Specific energy `z + v²/2g` (m). -/
def energy (h : Hist) : Float := h.z + h.v * h.v / (2.0 * G0T)

def seg (h : Array Hist) : Seg :=
  let a := h[0]!
  let b := h[h.size - 1]!
  let n := h.size.toFloat
  { omega := (b.psi - a.psi) / (b.t - a.t)
    vh := (h.foldl (fun s x => s + x.vh) (-0.0)) / n
    vzMin := h.foldl (fun m x => fmin m x.vz) (1.0 / 0.0)
    vzMean := (h.foldl (fun s x => s + x.vz) (-0.0)) / n
    vMean := (h.foldl (fun s x => s + x.v) (-0.0)) / n
    zMin := h.foldl (fun m x => fmin m x.z) (1.0 / 0.0)
    de := energy b - energy a
    e := b }

/-- `helix_check_annulus`: every raw cell within the annulus `[r0, r1]` around `c` is at least `R_BODY + MARGIN`
below `z`; an annulus reaching past the map's edge fails. -/
def helixClearAnn (cx cy r0 r1 z : Float) : Bool := Id.run do
  let floor := z - R_BODY - MARGIN
  if floor > top then return true
  if !onMap (cx - r1) (cy - r1) || !onMap (cx + r1) (cy + r1) then return false
  let pad := CELL * FRAC_1_SQRT_2
  let lo2 := let d := fmax (r0 - pad) 0.0; d * d
  let hi2 := let d := r1 + pad; d * d
  let floor := toF32 floor
  for j in [cellIdx (cy - r1 - pad):cellIdx (cy + r1 + pad) + 1] do
    let dy := -MAP_HALF + (j.toFloat + 0.5) * CELL - cy
    for i in [cellIdx (cx - r1 - pad):cellIdx (cx + r1 + pad) + 1] do
      if raster[j * NC + i]! ≤ floor then continue
      let dx := -MAP_HALF + (i.toFloat + 0.5) * CELL - cx
      let d2 := dx * dx + dy * dy
      if d2 ≥ lo2 && d2 ≤ hi2 then return false
  return true

/-- `helix_clear`: every raw cell within the annulus `r ± (m + R_BODY)` around `c` is at least `R_BODY + MARGIN`
below `z` (or `z` is that far above the map's top). -/
def helixClear (cx cy r m z : Float) : Bool := helixClearAnn cx cy (fmax (r - m - R_BODY) 0.0) (r + m + R_BODY) z

/-- `ray_clear`: a climbing ray from `p` along track `psi` at gradient `grad`, in a corridor widening 2% of the
distance, stays `R_BODY + MARGIN` above every raw cell until it is that far above the map's top. Off the map the
lookups clamp to the edge cells, as the terrain continues the edge; a ray still low after 10,000 steps fails. -/
def rayClear (px py pz psi grad : Float) : Bool := Id.run do
  if grad < 0.02 then return false
  let c := psi.cos
  let s := psi.sin
  let mut d := 0.0
  for _ in [0:10000] do
    let x := px + d * c
    let y := py + d * s
    let z := pz + d * grad
    let floor := z - R_BODY - MARGIN
    if floor > top then return true
    let w := R_BODY + 5.0 + 0.02 * d
    let mut l := -w
    while l ≤ w do
      if surface (x - l * s) (y + l * c) > floor then return false
      l := l + 0.5 * CELL
    d := d + 0.5 * CELL
  return false

/-- `terminal`: the escape has settled into its terminal set (climbing ray or helix, by `dir`) and that set is
clear, judged on the last `2·HALF + 1` samples. -/
def terminalOK (dir : Float) (kind : Nat) (hist : Array Hist) : Bool := Id.run do
  if hist.size < 2 * HALF + 1 then return false
  let n := hist.size
  let a := seg (hist.extract (n - 2 * HALF - 1) (n - HALF))
  let b := seg (hist.extract (n - HALF - 1) n)
  -- level-off: above `Z_LEVEL` the terminal law holds or descends to `H_LEVEL`, never below the map's top
  if fmin a.zMin b.zMin ≥ Z_LEVEL && b.vMean ≥ V_LEVEL then return true
  if fmin a.vzMin b.vzMin < VZ_MIN then return false
  let e := b.e
  if dir == 0.0 then
    if fmax a.omega.abs b.omega.abs > 0.01 then return false
    -- during the zoom climb vz is still falling and its gradient overstates the settled climb
    if !((a.vzMean - b.vzMean).abs ≤ VZ_SETTLED) then return false
    let grad := fmin (0.8 * fmin (a.vzMean / fmax a.vh 1.0) (b.vzMean / fmax b.vh 1.0)) GRAD_MAX
    return rayClear e.x e.y e.z e.psi grad
  else
    let want := -dir
    if a.omega * want ≤ 0.02 || b.omega * want ≤ 0.02 then return false
    -- speed first: settled above the post-stall branch, and not climbing on airspeed
    if b.vMean < V_HELIX_MIN[kind]! || (a.vMean - b.vMean).abs > V_SETTLED || a.de < 0.0 || b.de < 0.0 then
      return false
    let circ := fun (s : Seg) =>
      let rr := s.vh / s.omega
      (rr.abs, s.e.x - rr * s.e.psi.sin, s.e.y + rr * s.e.psi.cos)
    let (ra, cax, cay) := circ a
    let (rb, cbx, cby) := circ b
    let dR := (ra - rb).abs
    let dC := ((cax - cbx) * (cax - cbx) + (cay - cby) * (cay - cby)).sqrt
    if dR > R_SETTLED * rb || dC > C_SETTLED * rb then return false
    let m := 5.0 + 3.0 * (dR + dC)
    let grow := if e.z < top then rb * (rhoT e.z / rhoT top - 1.0) else 0.0
    return helixClearAnn cbx cby (fmax (rb - m - E_AIR) 0.0) (rb + m + grow + E_AIR) e.z

end CityGate.Esc
