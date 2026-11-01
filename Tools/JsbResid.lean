import Jsb.Model

/-! `jsbresid CSV [--euler] [--skip N] [--phi MAX] [--beta MAX] [--lat|--lat-beta|--lat-phi] [--diag [--diag-curin] [--rows]] [--dump FILE]`: one Lean tick from each logged state versus JSBSim's next logged state. -/

open Vibecheck Jsb

def parseFloat (str : String) : Float :=
  let neg := str.startsWith "-"
  let body := if neg then (str.drop 1).toString else str
  let (mant, ex) := match body.splitOn "e" with
    | [m, e] => (m, (if e.startsWith "+" then (e.drop 1).toString else e).toInt?.getD 0)
    | _ => (body, 0)
  let (ip, fp) := match mant.splitOn "." with
    | [a, b] => (a, b)
    | _ => (mant, "")
  let digits := (ip ++ fp).toNat?.getD 0
  let v := Float.ofScientific digits (decide ((ex - fp.length : Int) < 0)) (ex - fp.length : Int).natAbs
  if neg then -v else v

def toFx (f : Float) : Fx := ⟨(f * 65536.0).round.toInt64.toInt⟩

structure Row where
  ep : Nat
  k : Nat
  v : Array Float

def quantiles (xs : Array Float) : List Float :=
  let s := xs.qsort (· < ·)
  let pick (p : Float) : Float := if s.isEmpty then 0 else s[min (s.size - 1) (p * (s.size.toFloat - 1) + 0.5).toUSize.toNat]!
  [pick 0.5, pick 0.9, pick 0.99, pick 0.999, if s.isEmpty then 0 else s[s.size - 1]!]

def fmt (x : Float) : String :=
  let m := (x * 1000000.0).round / 1000000.0
  toString m

def printRow (name : String) (xs : Array Float) : IO Unit :=
  IO.println s!"{name}: n={xs.size} p50 {fmt (quantiles xs)[0]!} p90 {fmt (quantiles xs)[1]!} p99 {fmt (quantiles xs)[2]!} p99.9 {fmt (quantiles xs)[3]!} max {fmt (quantiles xs)[4]!}"

def main (args : List String) : IO UInt32 := do
  let path := args.head!
  let euler := args.contains "--euler"
  let diag := args.contains "--diag"
  let opt (name : String) (d : Float) : Float :=
    match args.dropWhile (· != name) with
    | _ :: v :: _ => parseFloat v
    | _ => d
  let skip := (opt "--skip" 4).toUInt64.toNat
  let phiMax := opt "--phi" 10
  let betaMax := opt "--beta" 10
  let lines ← IO.FS.lines path
  let hdr := (lines[0]!.splitOn ",").toArray
  let col (n : String) : Nat := (hdr.findIdx? (· == n)).getD 0
  let rows : Array (Array Float) := (lines.extract 1 lines.size).map fun l => (l.splitOn ",").toArray.map parseFloat
  let g (r : Array Float) (n : String) : Float := r[col n]!
  let mkState (r : Array Float) : State :=
    let th := g r "theta"
    { x := toFx (g r "x"), h := toFx (g r "h"), vx := toFx (g r "vx"), vz := toFx (g r "vz"),
      dx := toFx th.cos, dz := toFx th.sin, q := toFx (g r "q"), rpm := toFx (g r "rpm"),
      tmap := toFx (g r "map" / 1000), udot := toFx (g r "udot"), wdot := toFx (g r "wdot"),
      stall := toFx (g r "stallh"), ah := toFx (g r "ah0"), au := toFx (g r "au0"), qd := toFx (g r "qdot"),
      ah1 := toFx (g r "ah1"), au1 := toFx (g r "au1"), pvz := toFx (g r "hvz1"), pvz2 := toFx (g r "hvz2") }
  let lat := args.contains "--lat"
  let mkInput (r : Array Float) : Input :=
    { elev := toFx (g r "elev"), thr := toFx (g r "thr"),
      beta := if lat || args.contains "--lat-beta" then toFx (g r "beta") else 0,
      phi := if lat || args.contains "--lat-phi" then toFx (g r "phi") else 0 }
  -- pairs of consecutive ticks in one episode
  let mut pairs : Array (Array Float × Array Float) := #[]
  for i in [0:rows.size - 1] do
    let a := rows[i]!
    let b := rows[i + 1]!
    if g a "ep" == g b "ep" && g b "k" == g a "k" + 1 && g a "k" ≥ skip.toFloat && (g a "phi").abs ≤ phiMax && (g a "beta").abs ≤ betaMax then
      pairs := pairs.push (a, b)
  IO.println s!"{path}: {pairs.size} tick pairs ({if euler then "4x Euler 1/64 s" else "8x AB 1/128 s"})"
  if diag then
    let names := ["alpha", "adot", "qbar kPa", "fx aero kN", "fz aero kN", "m aero kNm", "fx prop kN", "m prop kNm",
                  "hp", "vind", "CLwbh kN", "CDwbh kN", "tip Mach", "CT", "J"]
    let mut cols : Array (Array Float) := (names.map fun _ => #[]).toArray
    for (a, _) in pairs do
      let dIn := if args.contains "--diag-curin" then mkInput a else { mkInput a with elev := toFx (g a "elevp"), thr := toFx (g a "thrp") }  -- logged properties came from the previous tick's inputs
      let (_, p) := probe dIn { mkState a with udot := toFx (g a "pudot"), wdot := toFx (g a "pwdot") }
      let ref : List Float := [g a "alpha", g a "adot", g a "qbar_s", g a "fxa" / 1000, g a "fza" / 1000,
        g a "ma" / 1000, g a "fxp" / 1000, g a "mp" / 1000, g a "hp", g a "vind", g a "cl" * 4.4482216 / 1000,
        g a "cd" * 4.4482216 / 1000, g a "tmach", g a "ct", g a "jadv"]
      let got : List Float := [p.alpha.toFloat, p.adot.toFloat, p.qbar.toFloat, p.fxA.toFloat, p.fzA.toFloat,
        p.mA.toFloat, p.fxP.toFloat, p.mP.toFloat, p.hp.toFloat, p.vind.toFloat, p.cl.toFloat, p.cd.toFloat,
        p.tipMach.toFloat, p.ct.toFloat, p.adv.toFloat]
      for i in [0:names.length] do
        cols := cols.set! i (cols[i]!.push ((got[i]! - ref[i]!).abs))
      if args.contains "--rows" then
        IO.println s!"ep {g a "ep"} k {g a "k"} alpha {fmt (g a "alpha")} elev {fmt (g a "elev")} fzA lean {fmt got[4]!} jsb {fmt ref[4]!} mA lean {fmt got[5]!} jsb {fmt ref[5]!} hp lean {fmt got[8]!} jsb {fmt ref[8]!} vind {fmt got[9]!} {fmt ref[9]!}"
    IO.println "diagnostics: |Lean probe - JSBSim property| at the tick-start state"
    for i in [0:names.length] do
      printRow names[i]! cols[i]!
    return 0
  let mut res : Array (Array Float) := (List.replicate 8 #[]).toArray
  let inits : Array (State × Input) := pairs.map fun (a, _) => (mkState a, mkInput a)
  let t0 ← IO.monoNanosNow
  let mut sink : Int := 0
  let mut preds : Array State := #[]
  for (s, i) in inits do
    let n := if euler then tickEuler i s else tickAB i s
    sink := sink + n.vz.raw
    preds := preds.push n
  let t1 ← IO.monoNanosNow
  for i in [0:pairs.size] do
    let (_, b) := pairs[i]!
    let n := preds[i]!
    let th := Float.atan2 n.dz.toFloat n.dx.toFloat
    let dth := (th - g b "theta")
    let vals : List Float := [n.x.toFloat - g b "x", n.h.toFloat - g b "h", n.vx.toFloat - g b "vx",
      n.vz.toFloat - g b "vz", dth, n.q.toFloat - g b "q", n.rpm.toFloat - g b "rpm",
      n.tmap.toFloat * 1000 - g b "map"]
    for j in [0:8] do
      res := res.set! j (res[j]!.push vals[j]!.abs)
  match args.dropWhile (· != "--dump") with
  | _ :: file :: _ =>
    let mut out : Array String := #["ep,k,rx,rh,rvx,rvz,rth,rq,rrpm,rmap,rstall"]
    for i in [0:pairs.size] do
      let (a, b) := pairs[i]!
      let n := preds[i]!
      let th := Float.atan2 n.dz.toFloat n.dx.toFloat
      let vals : List Float := [n.x.toFloat - g b "x", n.h.toFloat - g b "h", n.vx.toFloat - g b "vx",
        n.vz.toFloat - g b "vz", th - g b "theta", n.q.toFloat - g b "q", n.rpm.toFloat - g b "rpm",
        n.tmap.toFloat * 1000 - g b "map"]
      out := out.push s!"{g a "ep"},{g a "k"},{",".intercalate (vals.map toString)},{n.stall.toFloat - g b "stallh"}"
    IO.FS.writeFile file ("\n".intercalate out.toList)
  | _ => pure ()
  let names := ["x m", "h m", "vx m/s", "vz m/s", "theta rad", "q rad/s", "rpm", "map Pa"]
  for j in [0:8] do
    printRow names[j]! res[j]!
  IO.println s!"model time: {(t1 - t0).toFloat / pairs.size.toFloat} ns per tick (sink {sink})"
  return 0
