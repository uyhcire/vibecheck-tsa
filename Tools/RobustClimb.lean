import Jsb.Model

/-! `robustclimb`: untrusted (Float) robust-tube generator for C172 climb-out escapes on `Jsb.tickAB`. -/

open Vibecheck Jsb

namespace RC

/-! ## Small dense linear algebra -/

structure Mat where
  r : Nat
  c : Nat
  d : FloatArray
  deriving Inhabited

def fzeros (n : Nat) : FloatArray := FloatArray.mk (Array.replicate n 0.0)

namespace Mat
def zeros (r c : Nat) : Mat := ⟨r, c, fzeros (r * c)⟩
@[inline] def get (m : Mat) (i j : Nat) : Float := m.d[i * m.c + j]!
def ident (n : Nat) : Mat := Id.run do
  let mut d := fzeros (n * n)
  for i in [0:n] do d := d.set! (i * n + i) 1.0
  return ⟨n, n, d⟩
def mul (a b : Mat) : Mat := Id.run do
  let mut out := fzeros (a.r * b.c)
  for i in [0:a.r] do
    for k in [0:a.c] do
      let aik := a.d[i * a.c + k]!
      if aik != 0.0 then
        for j in [0:b.c] do
          out := out.set! (i * b.c + j) (out[i * b.c + j]! + aik * b.d[k * b.c + j]!)
  return ⟨a.r, b.c, out⟩
def tr (a : Mat) : Mat := Id.run do
  let mut out := fzeros (a.r * a.c)
  for i in [0:a.r] do
    for j in [0:a.c] do out := out.set! (j * a.r + i) (a.d[i * a.c + j]!)
  return ⟨a.c, a.r, out⟩
def zip (f : Float → Float → Float) (a b : Mat) : Mat := Id.run do
  let mut out := a.d
  for i in [0:a.d.size] do out := out.set! i (f a.d[i]! b.d[i]!)
  return ⟨a.r, a.c, out⟩
def add (a b : Mat) : Mat := zip (· + ·) a b
def sub (a b : Mat) : Mat := zip (· - ·) a b
def mulVec (a : Mat) (v : FloatArray) : FloatArray := Id.run do
  let mut out := fzeros a.r
  for i in [0:a.r] do
    let mut s := 0.0
    for j in [0:a.c] do s := s + a.d[i * a.c + j]! * v[j]!
    out := out.set! i s
  return out
/-- Columns side by side. -/
def hcat (a b : Mat) : Mat := Id.run do
  let c := a.c + b.c
  let mut out := fzeros (a.r * c)
  for i in [0:a.r] do
    for j in [0:a.c] do out := out.set! (i * c + j) (a.d[i * a.c + j]!)
    for j in [0:b.c] do out := out.set! (i * c + a.c + j) (b.d[i * b.c + j]!)
  return ⟨a.r, c, out⟩
/-- Row sums of absolute values (zonotope interval radius). -/
def absRowSum (a : Mat) : FloatArray := Id.run do
  let mut out := fzeros a.r
  for i in [0:a.r] do
    let mut s := 0.0
    for j in [0:a.c] do s := s + (a.d[i * a.c + j]!).abs
    out := out.set! i s
  return out
def diag (v : FloatArray) : Mat := Id.run do
  let n := v.size
  let mut d := fzeros (n * n)
  for i in [0:n] do d := d.set! (i * n + i) v[i]!
  return ⟨n, n, d⟩
/-- Drop all-zero columns. -/
def pruneZero (a : Mat) : Mat := Id.run do
  let keep := (List.range a.c).filter fun j => (List.range a.r).any fun i => a.get i j != 0.0
  let mut out := fzeros (a.r * keep.length)
  let mut jj := 0
  for j in keep do
    for i in [0:a.r] do out := out.set! (i * keep.length + jj) (a.get i j)
    jj := jj + 1
  return ⟨a.r, keep.length, out⟩
end Mat

/-- Inverse of a 2x2 (row-major) matrix. -/
def inv2 (m : Mat) : Mat :=
  let a := m.get 0 0; let b := m.get 0 1; let c := m.get 1 0; let d := m.get 1 1
  let det := a * d - b * c
  ⟨2, 2, FloatArray.mk #[d / det, -b / det, -c / det, a / det]⟩

/-- Girard order reduction: keep the `m - n` generators with the largest `|g|_1 - |g|_inf` (coordinates scaled to unit radius), box the rest. -/
def reduce (g : Mat) (m : Nat) : Mat := Id.run do
  if g.c ≤ m then return g
  let n := g.r
  let rad := g.absRowSum
  let sc := FloatArray.mk (rad.toList.map fun r => if r > 1e-12 then 1.0 / r else 0.0).toArray
  let score (j : Nat) : Float := Id.run do
    let mut s := 0.0; let mut mx := 0.0
    for i in [0:n] do
      let v := (g.get i j).abs * sc[i]!
      s := s + v; mx := if v > mx then v else mx
    return s - mx
  let idx := ((Array.range g.c).map fun j => (score j, j)).qsort (fun a b => a.1 > b.1)
  let nkeep := m - n
  let mut out := fzeros (n * m)
  for jj in [0:nkeep] do
    let j := idx[jj]!.2
    for i in [0:n] do out := out.set! (i * m + jj) (g.get i j)
  for jj in [nkeep:g.c] do
    let j := idx[jj]!.2
    for i in [0:n] do
      out := out.set! (i * m + nkeep + i) (out[i * m + nkeep + i]! + (g.get i j).abs)
  return ⟨n, m, out⟩

/-- Lower Cholesky factor of `G Gᵀ` (ridge-regularised), the frame the reduction boxes in. -/
def cholFrame (g : Mat) : Mat := Id.run do
  let n := g.r
  let mut c := fzeros (n * n)
  for i in [0:n] do
    for j in [0:i + 1] do
      let mut acc := 0.0
      for k in [0:g.c] do acc := acc + g.d[i * g.c + k]! * g.d[j * g.c + k]!
      c := c.set! (i * n + j) acc
  for i in [0:n] do c := c.set! (i * n + i) (c[i * n + i]! * (1.0 + 1e-9) + 1e-24)
  let mut l := fzeros (n * n)
  for j in [0:n] do
    let mut s := c[j * n + j]!
    for k in [0:j] do s := s - l[j * n + k]! * l[j * n + k]!
    let d := Float.sqrt (if s > 1e-24 then s else 1e-24)
    l := l.set! (j * n + j) d
    for i in [j + 1:n] do
      let mut t := c[i * n + j]!
      for k in [0:j] do t := t - l[i * n + k]! * l[j * n + k]!
      l := l.set! (i * n + j) (t / d)
  return ⟨n, n, l⟩

/-- Solve `L W = G` for lower-triangular `L` by forward substitution. -/
def lowerSolve (l g : Mat) : Mat := Id.run do
  let n := g.r
  let mut w := g.d
  for j in [0:g.c] do
    for i in [0:n] do
      let mut t := w[i * g.c + j]!
      for k in [0:i] do t := t - l.d[i * n + k]! * w[k * g.c + j]!
      w := w.set! (i * g.c + j) (t / l.d[i * n + i]!)
  return ⟨n, g.c, w⟩

/-- Girard reduction in the decorrelated frame `L⁻¹`: keep `m - n` generators, box the rest along columns of `L`. -/
def reduceT (g : Mat) (m : Nat) : Mat := Id.run do
  if g.c ≤ m then return g
  let n := g.r
  let l := cholFrame g
  let w := lowerSolve l g
  let score (j : Nat) : Float := Id.run do
    let mut s := 0.0; let mut mx := 0.0
    for i in [0:n] do
      let v := (w.get i j).abs
      s := s + v; mx := if v > mx then v else mx
    return s - mx
  let idx := ((Array.range g.c).map fun j => (score j, j)).qsort (fun a b => a.1 > b.1)
  let nkeep := m - n
  let mut out := fzeros (n * m)
  for jj in [0:nkeep] do
    let j := idx[jj]!.2
    for i in [0:n] do out := out.set! (i * m + jj) (g.get i j)
  let mut box := fzeros n
  for jj in [nkeep:g.c] do
    let j := idx[jj]!.2
    for i in [0:n] do box := box.set! i (box[i]! + (w.get i j).abs)
  for c in [0:n] do
    for i in [0:n] do out := out.set! (i * m + nkeep + c) (l.get i c * box[c]!)
  return ⟨n, m, out⟩

/-! ## Coordinates on the port's state -/

def toFx (f : Float) : Fx := ⟨(f * 65536.0).round.toInt64.toInt⟩
def fl (a : Fx) : Float := a.toFloat
def addF (a : Fx) (d : Float) : Fx := ⟨a.raw + (d * 65536.0).round.toInt64.toInt⟩
def clampF (lo hi v : Float) : Float := if v < lo then lo else if v > hi then hi else v

/-- Tube coordinates: x h vx vz theta q rpm map elev; the history fields are slaved to these. -/
def nz : Nat := 9
def iX := 0
def iH := 1
def iVX := 2
def iVZ := 3
def iTH := 4
def iQ := 5
def iEL := 8

def theta (s : State) : Float := Float.atan2 (fl s.dz) (fl s.dx)

def toVec (s : State) (el : Float) : FloatArray :=
  FloatArray.mk #[fl s.x, fl s.h, fl s.vx, fl s.vz, theta s, fl s.q, fl s.rpm, fl s.tmap, el]

/-- Displaced state; history fields move by the change of `evaluate` (one-substep-lag approximation). -/
def perturb (s : State) (el thr : Float) (d : FloatArray) : State :=
  let c := Float.cos d[4]!
  let sn := Float.sin d[4]!
  let dx := fl s.dx
  let dz := fl s.dz
  let s1 := { s with x := addF s.x d[0]!, h := addF s.h d[1]!, vx := addF s.vx d[2]!, vz := addF s.vz d[3]!,
                     dx := if d[4]! == 0.0 then s.dx else toFx (dx * c - dz * sn),
                     dz := if d[4]! == 0.0 then s.dz else toFx (dz * c + dx * sn),
                     q := addF s.q d[5]!, rpm := addF s.rpm d[6]!, tmap := addF s.tmap d[7]! }
  let inp : Input := { elev := toFx el, thr := toFx (clampF 0 1 thr) }
  let e0 := (evaluate 7 inp s).1
  let e1 := (evaluate 7 { inp with elev := toFx (el + d[iEL]!) } s1).1
  let dah := e1.ah - e0.ah
  let dau := e1.au - e0.au
  let dvz := s1.vz - s.vz
  { s1 with ah := s.ah + dah, au := s.au + dau, qd := s.qd + (e1.qd - e0.qd), udot := s.udot + (e1.udot - e0.udot),
            wdot := s.wdot + (e1.wdot - e0.wdot), ah1 := s.ah1 + dah, au1 := s.au1 + dau, pvz := s.pvz + dvz,
            pvz2 := s.pvz2 + dvz }

def vsub (a b : FloatArray) : FloatArray := Id.run do
  let mut o := a
  for i in [0:a.size] do o := o.set! i (a[i]! - b[i]!)
  return o

def plant (s : State) (el de thr : Float) : State × Float :=
  let el' := fl (toFx (el + de))
  (tickAB { elev := toFx el', thr := toFx (clampF 0 1 thr) } s, el')

/-! ## Terrain (2D profile of `sysid/tube.py`, stretched along x) -/

def terrainPts : Array (Float × Float) :=
  #[(-400, 50), (0, 50), (700, 50), (1100, 60), (1400, 110), (1700, 180), (1850, 215), (2000, 195), (2200, 250),
    (2300, 240), (2550, 170), (2850, 125), (3100, 120), (3300, 120), (4100, 120), (4400, 165), (4750, 250),
    (5000, 310), (5150, 290), (5300, 360), (5450, 300), (5750, 200), (6100, 110), (6500, 50), (6900, 30),
    (8000, 30), (8200, 60), (8500, 200), (8800, 420), (9200, 560)]

structure Terrain where
  sx : Float
  pts : Array (Float × Float)

def mkTerrain (sx : Float) : Terrain := ⟨sx, terrainPts.map fun (x, z) => (x * sx, z)⟩

def Terrain.at (t : Terrain) (x : Float) : Float := Id.run do
  let p := t.pts
  if x ≤ p[0]!.1 then return p[0]!.2
  for i in [0:p.size - 1] do
    let (x0, z0) := p[i]!
    let (x1, z1) := p[i + 1]!
    if x ≤ x1 then return z0 + (z1 - z0) * (x - x0) / (x1 - x0)
  return p[p.size - 1]!.2

/-- Highest terrain over [a, b]. -/
def Terrain.maxOn (t : Terrain) (a b : Float) : Float := Id.run do
  let mut m := max (t.at a) (t.at b)
  for (x, z) in t.pts do
    if a < x && x < b && z > m then m := z
  return m

/-- Lowest margin of the ray from (x0, h0) with slope `sl` above terrain + clearance ahead (terrain flat past its end). -/
def Terrain.rayMargin (t : Terrain) (x0 h0 sl clr : Float) : Float := Id.run do
  let mut m := 1.0e9
  for (x, z) in t.pts do
    if x > x0 then m := min m (h0 + sl * (x - x0) - z - clr)
  let zEnd := t.pts[t.pts.size - 1]!.2
  if sl ≤ 0.0 then m := min m (h0 - zEnd - clr)
  return m

/-! ## Trim and start states -/

/-- Iterate the evaluation with kinematics held: engine reaches equilibrium, derivative fields become consistent. -/
def settle (inp : Input) (s : State) (n : Nat) : State :=
  let e := iter n (fun s => (evaluate 7 inp s).1) s
  { e with ah1 := e.ah, au1 := e.au, pvz := e.vz, pvz2 := e.vz }

def mkState (x h V gam alpha : Float) (rpm tmap : Fx) : State :=
  let th := gam + alpha
  let vz := toFx (V * Float.sin gam)
  { x := toFx x, h := toFx h, vx := toFx (V * Float.cos gam), vz := vz, dx := toFx (Float.cos th),
    dz := toFx (Float.sin th), q := 0, rpm := rpm, tmap := tmap, udot := 0, wdot := 0, stall := 0,
    ah := 0, au := 0, qd := 0, ah1 := 0, au1 := 0, pvz := vz, pvz2 := vz }

/-- Along-path acceleration, normal acceleration, pitch acceleration. -/
def accels (s : State) : Float × Float × Float :=
  let vx := fl s.vx; let vz := fl s.vz; let v := Float.sqrt (vx * vx + vz * vz)
  ((fl s.ah * vx + fl s.au * vz) / v, (fl s.au * vx - fl s.ah * vz) / v, fl s.qd)

/-- Newton on three unknowns `p` with residual `f`; returns the last iterate. -/
def newton3 (f : Array Float → Array Float) (p0 : Array Float) (eps : Array Float) (iters : Nat) : Array Float := Id.run do
  let mut p := p0
  for _ in [0:iters] do
    let r := f p
    let mut J := Mat.zeros 3 3
    for j in [0:3] do
      let rp := f (p.set! j (p[j]! + eps[j]!))
      for i in [0:3] do J := { J with d := J.d.set! (i * 3 + j) ((rp[i]! - r[i]!) / eps[j]!) }
    let g (i j : Nat) := J.get i j
    let det := g 0 0 * (g 1 1 * g 2 2 - g 1 2 * g 2 1) - g 0 1 * (g 1 0 * g 2 2 - g 1 2 * g 2 0) + g 0 2 * (g 1 0 * g 2 1 - g 1 1 * g 2 0)
    if det.abs < 1e-12 then return p
    let col (k : Nat) : Float := Id.run do
      let m (i j : Nat) := if j == k then -r[i]! else g i j
      return (m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) + m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)) / det
    p := #[p[0]! + col 0, p[1]! + col 1, p[2]! + col 2]
  return p

def rpm0 : Fx := toFx 2300
def map0 : Fx := toFx 80

structure Trim where
  gam : Float
  alpha : Float
  el : Float
  thr : Float
  s : State

/-- Steady flight at speed `V` with throttle `thr`: unknowns flight-path angle, alpha, elevator. -/
def trimClimb (h V thr : Float) : Trim :=
  let mk (p : Array Float) : State :=
    settle { elev := toFx p[2]!, thr := toFx thr } (mkState 0 h V p[0]! p[1]! rpm0 map0) 1500
  let f (p : Array Float) : Array Float := let (a, b, c) := accels (mk p); #[a, b, c]
  let p := newton3 f #[0.05, 0.05, 0.0] #[0.002, 0.002, 0.01] 8
  ⟨p[0]!, p[1]!, p[2]!, thr, mk p⟩

/-- Steady flight along `gam` at speed `V`: unknowns alpha, elevator, throttle (clamped to [0, 1]). -/
def trimStart (x h V gam : Float) : Trim :=
  let mk (p : Array Float) : State :=
    settle { elev := toFx p[1]!, thr := toFx (clampF 0 1 p[2]!) } (mkState x h V gam p[0]! rpm0 map0) 1500
  let f (p : Array Float) : Array Float := let (a, b, c) := accels (mk p); #[a, b, c]
  let p := newton3 f #[0.05, 0.0, 0.5] #[0.002, 0.01, 0.01] 8
  let p := p.set! 2 (clampF 0 1 p[2]!)
  ⟨gam, p[0]!, p[1]!, p[2]!, mk p⟩

/-! ## Nominal climb-out controller -/

structure Ctl where
  /-- climb speed held through pitch, m/s -/
  vc : Float
  /-- nominal throttle -/
  thr : Float
  /-- nominal elevator change per tick allowed (rate limit 2/s = 0.125/tick, times the nominal share) -/
  deNom : Float
  deMax : Float
  tab : Array (Float × Float × Float × Float)

def Ctl.lookup (c : Ctl) (v : Float) : Float × Float × Float := Id.run do
  let t := c.tab
  let lerp (w : Float) (a b : Float × Float × Float) : Float × Float × Float :=
    (a.1 + w * (b.1 - a.1), a.2.1 + w * (b.2.1 - a.2.1), a.2.2 + w * (b.2.2 - a.2.2))
  if v ≤ t[0]!.1 then return t[0]!.2
  for i in [0:t.size - 1] do
    let (v0, a) := t[i]!
    let (v1, b) := t[i + 1]!
    if v ≤ v1 then return lerp ((v - v0) / (v1 - v0)) a b
  return t[t.size - 1]!.2

def mkCtl (vc thr deNom deMax : Float) : Ctl :=
  let tab := (List.range 11).toArray.map fun i =>
    let v := 26.0 + 4.0 * i.toFloat
    let t := trimClimb 100 v thr
    (v, t.gam, t.alpha, t.el)
  ⟨vc, thr, deNom, deMax, tab⟩

/-- Speed error integrator of the nominal controller (not part of the plant). -/
structure CtlMem where
  ithr : Float := 0

def airspeed (s : State) : Float := Float.sqrt (fl s.vx * fl s.vx + fl s.vz * fl s.vz)

/-- Elevator step and throttle for the nominal escape. -/
def Ctl.act (c : Ctl) (m : CtlMem) (s : State) (el : Float) : Float × Float × CtlMem :=
  let v := airspeed s
  let gam := Float.atan2 (fl s.vz) (fl s.vx)
  let th := theta s
  let q := fl s.q
  let (gamC, _, _) := c.lookup c.vc
  let (_, alphaV, elTrimV) := c.lookup v
  let err := v - c.vc
  let ig := clampF (-0.1) 0.1 (m.ithr + 0.0625 * 0.003 * err)
  -- flight-path command from speed error, never below level so slow starts do not dive
  let gamCmd := clampF 0.0 0.25 (gamC + 0.025 * err + ig)
  let thCmd := gamCmd + alphaV + 0.5 * (gamCmd - gam)
  let elCmd := clampF (-1) 1 (elTrimV + 2.0 * (thCmd - th) - 0.6 * q)
  let de := clampF (-c.deNom) c.deNom (0.5 * (elCmd - el))
  let ith := ig
  (de, c.thr, { ithr := ith })


/-! ## Escape plans and robust tubes -/

def lsb : Float := 1.0 / 65536.0

structure Cfg where
  ctl : Ctl
  terrain : Terrain
  /-- residual box D per coordinate -/
  dbox : FloatArray
  qdiag : FloatArray
  rEl : Float
  rThr : Float
  /-- false when the nominal throttle is at its stop, so the feedback is elevator only -/
  thrFb : Bool
  samples : Nat := 8
  order : Nat := 100
  /-- steady-climb trim in coordinates and the radius of its LTI closed-loop tube under D -/
  trimZ : FloatArray := fzeros 9
  rpi : FloatArray := fzeros 9
  /-- DARE cost at the trim, the terminal cost of the TV-LQR -/
  pTrim : Mat := Mat.zeros 0 0
  maxTicks : Nat := 1200
  clear : Float := 8.0
  /-- ticks of horizon beyond the nominal's terminal tick, so the tube can settle -/
  extra : Nat := 160
  /-- zero the gains on rpm and manifold pressure, so engine-state spread does not consume headroom -/
  noEngineFb : Bool := false
  /-- drop the sampled remainder on rpm and manifold pressure (attribution experiment only) -/
  noEngineRem : Bool := false
  /-- coordinates whose sampled remainder is dropped (attribution experiment only) -/
  remSkip : List Nat := []
  /-- remainder inflation over the sampled maximum -/
  remGain : Float := 1.5

structure Nominal where
  ss : Array State
  els : Array Float
  des : Array Float
  thrs : Array Float

/-- Interval of a coordinate set: centre `z`, radius `rad`. -/
structure Box where
  lo : FloatArray
  hi : FloatArray

def mkBox (z rad : FloatArray) : Box := Id.run do
  let mut lo := z
  let mut hi := z
  for i in [0:z.size] do
    lo := lo.set! i (z[i]! - rad[i]!)
    hi := hi.set! i (z[i]! + rad[i]!)
  return ⟨lo, hi⟩

/-- Row vector of the alpha = theta - atan(vz/vx) linearisation at `z`. -/
def alphaRow (z : FloatArray) : FloatArray :=
  let vx := z[iVX]!; let vz := z[iVZ]!; let v2 := vx * vx + vz * vz
  (fzeros nz).set! iTH 1.0 |>.set! iVZ (-vx / v2) |>.set! iVX (vz / v2)

def alphaOf (z : FloatArray) : Float := z[iTH]! - Float.atan2 z[iVZ]! z[iVX]!

def Cfg.clearance (cfg : Cfg) (b : Box) : Float := b.lo[iH]! - cfg.terrain.maxOn b.lo[iX]! b.hi[iX]!

/-- All members climb at 1 m/s or more, the set sits in the steady climb's own tube, and the worst climb ray of that tube clears terrain. -/
def Cfg.terminal (cfg : Cfg) (b : Box) (_z : FloatArray) : Bool :=
  let tol := FloatArray.mk #[0, 0, 1.0, 0.25, 0.03, 0.02, 0, 0, 0]
  let lim (i : Nat) : Float := 1.25 * cfg.rpi[i]! + tol[i]!
  let settled := [iVX, iVZ, iTH, iQ].all fun i =>
    b.hi[i]! ≤ cfg.trimZ[i]! + lim i && b.lo[i]! ≥ cfg.trimZ[i]! - lim i
  let vzMin := min b.lo[iVZ]! (cfg.trimZ[iVZ]! - lim iVZ)
  let vxMax := max b.hi[iVX]! (cfg.trimZ[iVX]! + lim iVX)
  b.lo[iVZ]! ≥ 1.0 && vzMin ≥ 1.0 && settled &&
  cfg.terrain.rayMargin b.hi[iX]! (b.lo[iH]! - 1.25 * cfg.rpi[iH]!) (vzMin / vxMax) cfg.clear ≥ 0.0

/-- stall bit stays clear while alpha < `alphaHystHi` (0.36 rad); 0.3 keeps a margin -/
def alphaMax : Float := 0.3

inductive Verdict where
  | ok (k : Nat)
  | fail (why : String) (k : Nat)
  deriving Inhabited

def Verdict.isOk : Verdict → Bool
  | .ok _ => true
  | _ => false

def Verdict.why : Verdict → String
  | .ok _ => "ok"
  | .fail w _ => w

/-- Fly the nominal escape; `ok kt` gives the first tick in the terminal set. -/
def Cfg.nominal (cfg : Cfg) (s0 : State) (el0 : Float) : Nominal × Verdict := Id.run do
  let mut s := s0
  let mut el := el0
  let mut m : CtlMem := {}
  let mut nom : Nominal := ⟨#[s0], #[el0], #[], #[]⟩
  let mut term : Option Nat := none
  for k in [0:cfg.maxTicks] do
    let z := toVec s el
    let b := mkBox z (fzeros nz)
    if k > 0 then
      if cfg.clearance b < cfg.clear then return (nom, .fail "nominal clearance" k)
      if alphaOf z > alphaMax then return (nom, .fail "nominal stall" k)
      if term.isNone && cfg.terminal b z then term := some k
    match term with
    | some kt => if k ≥ kt + cfg.extra then return (nom, .ok kt)
    | none => pure ()
    let (de, thr, m') := cfg.ctl.act m s el
    let (s', el') := plant s el de thr
    nom := ⟨nom.ss.push s', nom.els.push el', nom.des.push de, nom.thrs.push thr⟩
    s := s'; el := el'; m := m'
  return (nom, match term with | some kt => .ok kt | none => .fail "nominal no terminal" cfg.maxTicks)

/-- Finite-difference step per coordinate, far above the 2^-16 grid. -/
def epsVec : FloatArray := FloatArray.mk #[1.0, 0.5, 0.1, 0.1, 0.01, 0.01, 5.0, 0.2, 0.01]

/-- Jacobians of one tick in coordinates: A (nz x nz) and B (nz x 2) for (elevator step, throttle). -/
def jacobian (s : State) (el de thr : Float) (z1 : FloatArray) : Mat × Mat := Id.run do
  let z0 := toVec s el
  let mut a := Mat.zeros nz nz
  a := { a with d := a.d.set! 0 1.0 }
  for j in [1:nz] do
    let e := epsVec[j]!
    let dz := (fzeros nz).set! j e
    let s1 := perturb s el thr dz
    let el1 := el + dz[iEL]!
    let actual := (toVec s1 el1)[j]! - z0[j]!
    let (sn, eln) := plant s1 el1 de thr
    let zn := toVec sn eln
    for i in [0:nz] do a := { a with d := a.d.set! (i * nz + j) ((zn[i]! - z1[i]!) / actual) }
  let mut b := Mat.zeros nz 2
  let ee := epsVec[iEL]!
  let (sn, eln) := plant s el (de + ee) thr
  let zn := toVec sn eln
  for i in [0:nz] do b := { b with d := b.d.set! (i * 2) ((zn[i]! - z1[i]!) / ee) }
  let et := if thr + 0.01 ≤ 1.0 then 0.01 else -0.01
  let (sn, eln) := plant s el de (thr + et)
  let zn := toVec sn eln
  for i in [0:nz] do b := { b with d := b.d.set! (i * 2 + 1) ((zn[i]! - z1[i]!) / et) }
  return (a, b)

/-- One Riccati step: gain K (2 x nz) and the previous-stage cost P. -/
def riccati (q : Mat) (r : Mat) (a b p : Mat) : Mat × Mat :=
  let pa := p.mul a
  let pb := p.mul b
  let bt := b.tr
  let k := (inv2 (r.add (bt.mul pb))).mul (bt.mul pa)
  let atr := a.tr
  (k, q.add ((atr.mul pa).sub ((atr.mul pb).mul k)))

structure XorShift where
  s : UInt64

def XorShift.next (g : XorShift) : UInt64 × XorShift :=
  let x := g.s ^^^ (g.s <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

/-- Stored per tick for the online one-step check. -/
structure Step where
  acl : Mat
  rem : FloatArray
  /-- generator set after the tick, after order reduction -/
  g : Mat
  deriving Inhabited

structure Tube where
  verdict : Verdict
  steps : Array Step
  tJac : Nat
  tLqr : Nat
  tProp : Nat
  maxRem : FloatArray

def Cfg.fixK (cfg : Cfg) (k : Mat) : Mat := if !cfg.noEngineFb then k else Id.run do
  let mut d := k.d
  for r in [0:2] do
    for c in [6, 7] do d := d.set! (r * nz + c) 0.0
  return { k with d := d }

/-- Robust tube around a nominal escape; checks headroom, clearance, stall margin and the terminal set per tick. -/
def Cfg.tube (cfg : Cfg) (nom : Nominal) (horizon : Nat) (seed : UInt64) (keep : Bool := false) (trace : Bool := false) : IO Tube := do
  let n := min horizon nom.des.size
  let t0 ← IO.monoNanosNow
  let mut abs : Array (Mat × Mat) := #[]
  for k in [0:n] do
    abs := abs.push (jacobian nom.ss[k]! nom.els[k]! nom.des[k]! nom.thrs[k]! (toVec nom.ss[k+1]! nom.els[k+1]!))
  let t1 ← IO.monoNanosNow
  let qm := Mat.diag cfg.qdiag
  let rm := Mat.diag (FloatArray.mk #[cfg.rEl, if cfg.thrFb then cfg.rThr else 1.0])
  let fixB (b : Mat) : Mat := if cfg.thrFb then b else Id.run do
    let mut d := b.d
    for i in [0:nz] do d := d.set! (i * 2 + 1) 0.0
    return { b with d := d }
  let mut p := cfg.pTrim
  let mut ks : Array Mat := Array.replicate n (Mat.zeros 2 nz)
  for i in [0:n] do
    let k := n - 1 - i
    let (a, b) := abs[k]!
    let (kk, p') := riccati qm rm a (fixB b) p
    ks := ks.set! k (cfg.fixK kk)
    p := p'
  let t2 ← IO.monoNanosNow
  let dgen := (Mat.diag cfg.dbox).pruneZero
  let mut g := Mat.zeros nz 0
  let mut rng : XorShift := ⟨seed * 2654435761 + 88172645463325252⟩
  let mut steps : Array Step := #[]
  let mut maxRem := fzeros nz
  let mut verdict : Verdict := .fail "no terminal" n
  for k in [0:n] do
    let z := toVec nom.ss[k]! nom.els[k]!
    let kk := ks[k]!
    if k > 0 then
      let rad := g.absRowSum
      let b := mkBox z rad
      let fb := kk.mul g |>.absRowSum
      let cap := cfg.ctl.deMax
      if trace && k % 16 == 0 then
        IO.println s!"  k {k} rad h {rad[iH]!} vx {rad[iVX]!} vz {rad[iVZ]!} th {rad[iTH]!} q {rad[iQ]!} el {rad[iEL]!} | fb de {fb[0]!} thr {fb[1]!} | nom de {nom.des[k]!} vz {z[iVZ]!} clr {cfg.clearance b}"
      if nom.des[k]!.abs + fb[0]! > cap then verdict := .fail "elevator rate headroom" k; break
      if nom.thrs[k]! + fb[1]! > 1.0 + 1e-9 || nom.thrs[k]! - fb[1]! < 0.0 then verdict := .fail "throttle headroom" k; break
      if b.hi[iEL]! > 1.0 || b.lo[iEL]! < -1.0 then verdict := .fail "elevator travel" k; break
      if cfg.clearance b < cfg.clear then verdict := .fail "clearance" k; break
      let ar := (Mat.mul ⟨1, nz, alphaRow z⟩ g).absRowSum
      if alphaOf z + ar[0]! > alphaMax then verdict := .fail "stall margin" k; break
      if cfg.terminal b z then verdict := .ok k; break
    let (a, bm) := abs[k]!
    let acl := a.sub ((fixB bm).mul kk)
    let lin := acl.mul g
    -- sampled linearisation remainder of the closed-loop tick over vertices of the current set
    let z1 := toVec nom.ss[k+1]! nom.els[k+1]!
    let mut rem := fzeros nz
    if g.c > 0 then
      for _ in [0:cfg.samples] do
        let mut xi := fzeros g.c
        for j in [0:g.c] do
          let (r, rng') := rng.next
          rng := rng'
          xi := xi.set! j (if r &&& 1 == 0 then 1.0 else -1.0)
        let dz := g.mulVec xi
        let u := kk.mulVec dz
        let (sn, eln) := plant (perturb nom.ss[k]! nom.els[k]! nom.thrs[k]! dz) (nom.els[k]! + dz[iEL]!) (nom.des[k]! - u[0]!)
          (nom.thrs[k]! - (if cfg.thrFb then u[1]! else 0.0))
        let pred := acl.mulVec dz
        let zn := toVec sn eln
        for i in [0:nz] do
          let e := (zn[i]! - z1[i]! - pred[i]!).abs
          if e > rem[i]! then rem := rem.set! i e
    for i in [0:nz] do
      let r := (if (cfg.noEngineRem && (i == 6 || i == 7)) || cfg.remSkip.contains i then 0.0 else cfg.remGain * rem[i]!) + 2.0 * lsb
      rem := rem.set! i r
      if r > maxRem[i]! then maxRem := maxRem.set! i r
    if trace && k % 16 == 0 then IO.println s!"    rem {rem}"
    let full := (lin.hcat (Mat.diag rem)).hcat dgen
    g := reduceT full cfg.order
    if keep then steps := steps.push ⟨acl, rem, g⟩
  let t3 ← IO.monoNanosNow
  return ⟨verdict, steps, t1 - t0, t2 - t1, t3 - t2, maxRem⟩

end RC


namespace RC

def Cfg.fixB (cfg : Cfg) (b : Mat) : Mat := if cfg.thrFb then b else Id.run do
  let mut d := b.d
  for i in [0:nz] do d := d.set! (i * 2 + 1) 0.0
  return { b with d := d }

/-- LTI LQR at the steady-climb trim and the radius of its tube under D after `ticks`. -/
def Cfg.withRpi (cfg : Cfg) (ticks : Nat := 800) : Cfg := Id.run do
  let t := trimClimb 200 cfg.ctl.vc cfg.ctl.thr
  let z := toVec t.s t.el
  let (s1, el1) := plant t.s t.el 0 cfg.ctl.thr
  let (a, b0) := jacobian t.s t.el 0 cfg.ctl.thr (toVec s1 el1)
  let b := cfg.fixB b0
  let qm := Mat.diag cfg.qdiag
  let rm := Mat.diag (FloatArray.mk #[cfg.rEl, if cfg.thrFb then cfg.rThr else 1.0])
  let mut p := qm
  let mut kk := Mat.zeros 2 nz
  for _ in [0:1000] do
    let (k', p') := riccati qm rm a b p
    kk := k'; p := p'
  let acl := a.sub (b.mul (cfg.fixK kk))
  let dgen := (Mat.diag cfg.dbox).pruneZero
  let mut g := dgen
  for _ in [0:ticks] do g := reduceT ((acl.mul g).hcat dgen) cfg.order
  return { cfg with trimZ := z, rpi := g.absRowSum, pTrim := p }

end RC

namespace RC

def dFull : FloatArray := FloatArray.mk #[0.0006, 0.0006, 0.0192, 0.0166, 0.0021, 0.0104, 0.3, 0.0005, 0]

/-- D when the filter is given measured bank and sideslip. -/
def dLat : FloatArray := FloatArray.mk #[0.0006, 0.0006, 0.0158, 0.0037, 0.0021, 0.0047, 0.3, 0.0005, 0]

def scaleVec (c : Float) (v : FloatArray) : FloatArray := FloatArray.mk (v.toList.map (c * ·)).toArray

def qDefault : FloatArray := FloatArray.mk #[0, 1, 10, 10, 100, 10, 0, 0, 1]

/-- `reserve`: nominal throttle 0.8 and 60% of the elevator rate; otherwise full throttle and full rate. -/
def mkCfg (reserve : Bool) (dscale : Float) (terrain : Terrain) (lat : Bool := false) : Cfg :=
  let ctl := if reserve then mkCtl 38 0.8 (0.6 * 0.125) 0.125 else mkCtl 38 1.0 0.125 0.125
  Cfg.withRpi { ctl := ctl, terrain := terrain, dbox := scaleVec dscale (if lat then dLat else dFull), qdiag := qDefault,
                rEl := 400, rThr := 25, thrFb := reserve }

end RC

/-- Decimal like `-0.05` or `1e-3`. -/
def parseF (str : String) : Option Float := do
  let neg := str.startsWith "-"
  let body := if neg then (str.drop 1).toString else str
  let (mant, ex) ← match body.splitOn "e" with
    | [m, e] => (fun x => (m, x)) <$> (if e.startsWith "-" then (fun n => -(n : Int)) <$> (e.drop 1).toString.toNat? else (fun n => (n : Int)) <$> e.toNat?)
    | _ => some (body, 0)
  let (ip, fp) := match mant.splitOn "." with
    | [a, b] => (a, b)
    | _ => (mant, "")
  let digits ← (ip ++ fp).toNat?
  let e : Int := ex - fp.length
  let v := Float.ofScientific digits (decide (e < 0)) e.natAbs
  return if neg then -v else v

def optF (args : List String) (name : String) (d : Float) : Float :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => (parseF v).getD d
  | _ => d

open RC in
def main (args : List String) : IO UInt32 := do
  if args.head? == some "trim" then
    for thr in [0.6, 0.8, 1.0] do
      for v in [30.0, 35.0, 38.0, 42.0, 50.0, 60.0] do
        let t := trimClimb 100 v thr
        let (a, b, c) := accels t.s
        IO.println s!"thr {thr} V {v}: gam {t.gam} alpha {t.alpha} el {t.el} vz {v * Float.sin t.gam} rpm {fl t.s.rpm} res {a} {b} {c}"
  if args.head? == some "nom" then
    let thr := 0.8
    let c := mkCtl 38 thr (0.6 * 0.125) 0.125
    IO.println s!"tab {c.tab}"
    for (v, g) in [(30.0, -0.1), (60.0, -0.1), (45.0, 0.1), (60.0, 0.1), (30.0, 0.1)] do
      let t := trimStart 0 100 v g
      let mut s := t.s
      let mut el := t.el
      let mut m : CtlMem := {}
      IO.println s!"start V {v} gam {g}: alpha {t.alpha} el {t.el} thr {t.thr}"
      for k in [0:1201] do
        let (de, th, m') := c.act m s el
        if k % 48 == 0 then
          IO.println s!"  t {k.toFloat / 16} h {fl s.h} V {airspeed s} vz {fl s.vz} th {theta s} q {fl s.q} el {el} de {de} alpha {theta s - Float.atan2 (fl s.vz) (fl s.vx)}"
        let (s', el') := plant s el de th
        s := s'; el := el'; m := m'
  if args.head? == some "bench" then
    let terr := mkTerrain 3.0
    let lat := args.contains "--lat"
    let cfg := { mkCfg true (optF args "--d" 1) terr lat with remGain := optF args "--rg" 1.5 }
    let mut gen : Array Nat := #[]
    let mut perTick : Array Float := #[]
    let mut ticks : Array Nat := #[]
    let mut chk : Array Float := #[]
    let mut chkMul : Array Float := #[]
    for x in [1800.0, 9000.0, 14400.0] do
      for v in [30.0, 45.0, 60.0] do
        for g in [-0.1, 0.1] do
          let t := trimStart x (terr.at x + 60) v g
          let t0 ← IO.monoNanosNow
          let (nom, nv) := cfg.nominal t.s t.el
          let some kt := (match nv with | .ok k => some k | _ => none) | continue
          let tb ← cfg.tube nom (kt + cfg.extra) 3 (keep := true)
          let t1 ← IO.monoNanosNow
          gen := gen.push (t1 - t0)
          let n := tb.steps.size
          let hz := min (kt + cfg.extra) nom.des.size
          ticks := ticks.push hz
          perTick := perTick.push ((t1 - t0).toFloat / hz.toFloat)
          -- per-tick committed-plan check: model tick at the centre, push the set, reduce, compare with the stored next set
          let dgen := (Mat.diag cfg.dbox).pruneZero
          let reps := 20
          let c0 ← IO.monoNanosNow
          let mut sink := 0.0
          for _ in [0:reps] do
            for k in [1:n] do
              let st := tb.steps[k]!
              let (sn, _) := plant nom.ss[k]! nom.els[k]! nom.des[k]! nom.thrs[k]!
              let pushed := ((st.acl.mul tb.steps[k - 1]!.g).hcat (Mat.diag st.rem)).hcat dgen
              let red := reduceT pushed cfg.order
              let mut worst := 0.0
              for i in [0:red.d.size] do worst := max worst (red.d[i]! - st.g.d[i]!).abs
              sink := sink + worst + fl sn.h
          let c1 ← IO.monoNanosNow
          let mut sink2 := 0.0
          for _ in [0:reps] do
            for k in [1:n] do
              let st := tb.steps[k]!
              let pushed := st.acl.mul tb.steps[k - 1]!.g
              sink2 := sink2 + pushed.d[0]!
          let c2 ← IO.monoNanosNow
          if n > 1 then
            chk := chk.push ((c1 - c0).toFloat / (reps * (n - 1)).toFloat / 1000.0)
            chkMul := chkMul.push ((c2 - c1).toFloat / (reps * (n - 1)).toFloat / 1000.0)
          IO.println s!"x {x} v {v} g {g}: {tb.verdict.why} at {n}, horizon {min (kt + cfg.extra) nom.des.size} ticks, generation {(t1 - t0) / 1000000} ms (jac {tb.tJac / 1000000} lqr {tb.tLqr / 1000000} prop {tb.tProp / 1000000}) sink {decide (sink + sink2 > 0)}"
    let med (a : Array Float) : Float := if a.isEmpty then 0 else (a.qsort (· < ·))[a.size / 2]!
    IO.println s!"median generation {med (gen.map (·.toFloat / 1e6))} ms, median per horizon tick {med perTick / 1000} us, median horizon {med (ticks.map (·.toFloat))} ticks"
    IO.println s!"per-tick check (centre tick + push + reduce + compare) median {med chk} us; push product alone {med chkMul} us"
    let t := trimStart 3000 200 40 0
    let (nom, _) := cfg.nominal t.s t.el
    let tk0 ← IO.monoNanosNow
    let mut sinkh := 0.0
    for _ in [0:20] do
      for k in [0:nom.des.size] do sinkh := sinkh + fl (plant nom.ss[k]! nom.els[k]! nom.des[k]! nom.thrs[k]!).1.h
    let tk1 ← IO.monoNanosNow
    IO.println s!"tickAB along a nominal {(tk1 - tk0).toFloat / (20 * nom.des.size).toFloat / 1000} us (sink {decide (sinkh > 0)})"
  if args.head? == some "rpi" then
    let opt := optF args
    let terr := mkTerrain 3.0
    let cfg := mkCfg true (opt "--d" 1) terr (args.contains "--lat")
    let t := trimStart 3000 200 38 0.08
    let (nom, _) := cfg.nominal t.s t.el
    let k := nom.des.size - 1
    let (a, b) := jacobian nom.ss[k]! nom.els[k]! nom.des[k]! nom.thrs[k]! (toVec nom.ss[k+1]! nom.els[k+1]!)
    IO.println s!"B col el {(List.range nz).map (b.get · 0)}"
    IO.println s!"B col thr {(List.range nz).map (b.get · 1)}"
    let qd := cfg.qdiag |>.set! iTH (opt "--qth" 100) |>.set! iVZ (opt "--qvz" 10) |>.set! iVX (opt "--qvx" 10) |>.set! iQ (opt "--qq" 10) |>.set! iH (opt "--qh" 1)
    let qm := Mat.diag qd
    let rm := Mat.diag (FloatArray.mk #[1 / (opt "--sel" 0.05) ^ 2, 1 / (opt "--sthr" 0.2) ^ 2])
    let mut p := qm
    let mut kk := Mat.zeros 2 nz
    for _ in [0:2000] do
      let (k', p') := riccati qm rm a b p
      kk := k'; p := p'
    IO.println s!"K el {(List.range nz).map (kk.get 0 ·)}"
    let acl := a.sub (b.mul kk)
    let mut v := FloatArray.mk ((List.range nz).map (fun i => 1.0 + i.toFloat * 0.1)).toArray
    let mut gr := 0.0
    for _ in [0:3000] do
      let w := acl.mulVec v
      let nrm := Float.sqrt (w.toList.foldl (fun acc x => acc + x * x) 0)
      gr := nrm
      v := FloatArray.mk (w.toList.map (· / nrm)).toArray
    IO.println s!"acl dominant growth/tick {gr} vec {v}"
    let ord := (opt "--ord" 54).toUInt64.toNat
    let dgen := (Mat.diag cfg.dbox).pruneZero
    let mut g := dgen
    for i in [1:1601] do
      let full := (acl.mul g).hcat dgen
      g := if args.contains "--girard" then reduce full ord else reduceT full ord
      if i % 320 == 0 then
        let r := g.absRowSum
        let fb := (kk.mul g).absRowSum
        IO.println s!"t {i / 16}s rad h {r[iH]!} vx {r[iVX]!} vz {r[iVZ]!} th {r[iTH]!} q {r[iQ]!} el {r[iEL]!} fb de {fb[0]!} thr {fb[1]!}"
  if args.head? == some "cover" then
    let opt := optF args
    let terr := mkTerrain 3.0
    let xs := if args.contains "--small" then [1200.0, 3000.0, 4800.0] else (List.range 10).map fun i => 600.0 * (i.toFloat + 1)
    let mut starts : Array (Float × Float × Float × Float) := #[]
    for x in xs do
      for v in [30.0, 40.0, 50.0, 60.0] do
        for agl in [25.0, 60.0, 100.0, 150.0] do
          for g in [-0.1, 0.0, 0.1] do starts := starts.push (3.0 * x, agl, v, g)
    let skipList : List Nat := match args.dropWhile (· != "--remskip") with
      | _ :: v :: _ => (v.splitOn ",").filterMap String.toNat?
      | _ => []
    let tune (c : Cfg) : Cfg :=
      let qd := (((((c.qdiag.set! iTH (opt "--qth" 100)).set! iVZ (opt "--qvz" 10)).set! iVX (opt "--qvx" 10)).set! iQ (opt "--qq" 10)).set! iH (opt "--qh" 1)).set! 6 (opt "--qrpm" 0)
      let ctl := if c.thrFb && args.contains "--thr" then mkCtl (opt "--vc" 38) (opt "--thr" 0.8) c.ctl.deNom c.ctl.deMax else c.ctl
      let c := { c with rEl := 1 / (opt "--sel" 0.05) ^ 2, rThr := 1 / (opt "--sthr" 0.2) ^ 2, qdiag := qd, ctl := ctl,
                        remGain := opt "--rg" 1.5, samples := (opt "--ns" 8).toUInt64.toNat, extra := (opt "--extra" 160).toUInt64.toNat, noEngineFb := args.contains "--noeng", noEngineRem := args.contains "--noengrem",
                        remSkip := skipList,
                        thrFb := c.thrFb && !args.contains "--nothr" }
      c.withRpi
    let modes := (if args.contains "--nofull" then [true] else [true, false])
    let levels : List (String × Float × Bool) := [("D", 1.0, false), ("0.5D", 0.5, false), ("latD", 1.0, true)]
    let mut lines : Array String := #[]
    for reserve in modes do
      let nomCfg := tune (mkCfg reserve 0 terr)
      let cfgs := levels.map fun (nm, sc, lat) => (nm, tune (mkCfg reserve sc terr lat))
      let work (st : Float × Float × Float × Float) : IO (String × List (String × String × Nat)) := do
        let (x, agl, v, g) := st
        let t := trimStart x (terr.at x + agl) v g
        let (_, nv) := nomCfg.nominal t.s t.el
        let mut res : List (String × String × Nat) := []
        for (nm, cfg) in cfgs do
          if nv.isOk then
            let (nom, v2) := cfg.nominal t.s t.el
            match v2 with
            | .ok kt =>
              let tb ← cfg.tube nom (kt + cfg.extra) 7
              res := res ++ [(nm, tb.verdict.why, tb.tJac + tb.tLqr + tb.tProp)]
            | .fail _ _ => res := res ++ [(nm, "terminal region unreachable", 0)]
          else res := res ++ [(nm, "nominal failed", 0)]
        return (nv.why, res)
      let nth := (opt "--threads" 8).toUInt64.toNat
      let mut out : Array (String × List (String × String × Nat)) := #[]
      let mut i := 0
      while i < starts.size do
        let chunk := starts.extract i (i + nth)
        let tasks ← chunk.mapM fun st => IO.asTask (work st)
        for tk in tasks do
          match ← IO.wait tk with
          | .ok r => out := out.push r
          | .error e => throw e
        i := i + nth
      let nomOk := (out.filter fun r => r.1 == "ok").size
      let tag := if reserve then "reserve (thr 0.8, elev rate 60%)" else "no reserve (thr 1.0, full rate)"
      lines := lines.push s!"{tag}: starts {out.size}, nominal ok {nomOk}"
      let nomWhy := out.foldl (fun (acc : List (String × Nat)) r => if r.1 == "ok" then acc else
        match acc.find? (·.1 == r.1) with
        | some _ => acc.map fun (k, c) => if k == r.1 then (k, c + 1) else (k, c)
        | none => acc ++ [(r.1, 1)]) []
      lines := lines.push s!"  nominal failures {nomWhy}"
      for (nm, _) in cfgs do
        let rs := out.filterMap fun r => r.2.find? (·.1 == nm)
        let ok := (rs.filter fun r => r.2.1 == "ok").size
        let why := rs.foldl (fun (acc : List (String × Nat)) r => if r.2.1 == "ok" || r.2.1 == "nominal failed" then acc else
          match acc.find? (·.1 == r.2.1) with
          | some _ => acc.map fun (k, c) => if k == r.2.1 then (k, c + 1) else (k, c)
          | none => acc ++ [(r.2.1, 1)]) []
        let ts := (rs.filter fun r => r.2.2 > 0).map (·.2.2)
        let tmed := if ts.isEmpty then 0 else (ts.qsort (· < ·))[ts.size / 2]!
        lines := lines.push s!"  {nm}: robust ok {ok} ({if nomOk == 0 then 0.0 else ok.toFloat / nomOk.toFloat * 100}% of nominal) median gen {tmed / 1000000} ms (multithreaded) failures {why}"
      for l in lines do IO.println l
      lines := #[]
  if args.head? == some "one" then
    let opt := optF args
    let terr := mkTerrain 3.0
    let x0 := opt "--x" 3000
    let agl := opt "--agl" 60
    let v := opt "--v" 40
    let g := opt "--gam" 0
    let reserve := !args.contains "--full"
    let cfg := mkCfg reserve (opt "--d" 1) terr (args.contains "--lat")
    let cfg := { cfg with rEl := 1 / (opt "--sel" 0.05) ^ 2, rThr := 1 / (opt "--sthr" 0.2) ^ 2,
                          qdiag := scaleVec 1 cfg.qdiag |>.set! iTH (opt "--qth" 100) |>.set! iVZ (opt "--qvz" 10) |>.set! iVX (opt "--qvx" 10) |>.set! iQ (opt "--qq" 10) |>.set! iH (opt "--qh" 1) |>.set! 6 (opt "--qrpm" 0),
                          remGain := opt "--rg" 1.5, samples := (opt "--ns" 8).toUInt64.toNat, extra := (opt "--extra" 160).toUInt64.toNat,
                          noEngineFb := args.contains "--noeng", order := (opt "--ord" 100).toUInt64.toNat,
                          thrFb := cfg.thrFb && !args.contains "--nothr" : Cfg }.withRpi
    IO.println s!"trim {cfg.trimZ} rpi {cfg.rpi}"
    let t := trimStart x0 (terr.at x0 + agl) v g
    let (nom, nv) := cfg.nominal t.s t.el
    IO.println s!"nominal: {nv.why} ticks {nom.des.size}"
    if let .ok kt := nv then
      let tb ← cfg.tube nom (kt + cfg.extra) 1 (trace := true)
      IO.println s!"tube: {tb.verdict.why} at {match tb.verdict with | .ok k => k | .fail _ k => k} jac {tb.tJac / 1000000} ms lqr {tb.tLqr / 1000000} ms prop {tb.tProp / 1000000} ms"
      IO.println s!"max remainder {tb.maxRem}"
  return 0
