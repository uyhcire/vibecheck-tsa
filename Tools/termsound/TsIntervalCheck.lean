import Lean.Data.Json
import Tools.termsound.TsInterval
import Tools.termsound.TableStop

/-! # `tsintervalcheck [N]`: sampling test of `TsInterval.frameBox` (`make tsinterval-check`, see the README). -/

open TsInterval JsbExact

namespace TsIntervalCheck

def nextU (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

def nextF (s : UInt64) : Float × UInt64 :=
  let (z, s) := nextU s
  ((z >>> 11).toFloat / 9007199254740992.0, s)

/-- h in m, then `trim.py`'s `SCALE`. -/
def scale : Array Float :=
  #[1, 1e-2, 1e-1, 1e-2, 30, 1, 5, 1e-1, 1e-1, 1e-1, 3e-4, 3e-4, 3e-4, 3e-4, 3e-4, 3e-4,
    3e-2, 3e-2, 3e-2, 3e-2, 3e-2, 3e-2, 1e-1, 1e-1, 1e-1, 1, 1, 1, 2600, 9e4, 1e-1, 1e-1, 1e-1]

def names : Array String := #["h"] ++ yNames

def col (n : String) : Nat := (names.findIdx? (· == n)).getD 0

structure Box where
  name : String
  psi : Float := 3.141592653589793 / 2
  centre : List (String × Float) := []
  half : Array Float

def only (ws : List (String × Float)) : Array Float :=
  ws.foldl (fun a (n, w) => a.set! (col n) w) (Array.replicate 33 0)

def boxes : List Box :=
  [ { name := "point", half := only [] } ] ++
  ([("1e-9", 1e-9), ("1e-8", 1e-8), ("1e-7", 1e-7), ("1e-6", 1e-6), ("1e-5", 1e-5), ("1e-4", 1e-4), ("1e-3", 1e-3),
    ("1e-2", 1e-2), ("0.1", 0.1), ("1", 1)].map fun (l, s) =>
    { name := s!"all coordinates x {l}", half := scale.map (s * ·) }) ++
  [ { name := "PANICKED BEFORE: h 1 m, theta 0.1 rad", half := only [("h", 1), ("theta", 0.1)] },
    { name := "PANICKED BEFORE: h 60, v_al 18, v_dn 1, theta 0.05", half := only [("h", 60), ("v_al", 18), ("v_dn", 1), ("theta", 0.05)] },
    { name := "theta 1e-6", half := only [("theta", 1e-6)] },
    { name := "theta 1e-5", half := only [("theta", 1e-5)] },
    { name := "theta 1e-4", half := only [("theta", 1e-4)] },
    { name := "h 1 m", half := only [("h", 1)] },
    { name := "h 10 m", half := only [("h", 10)] },
    { name := "h 30 m", half := only [("h", 30)] },
    { name := "h 60 m", half := only [("h", 60)] },
    { name := "h 150 m (mixEff key 0.08845)", half := only [("h", 150)] },
    { name := "v_al 5 m/s (propeller J key 0.8)", half := only [("v_al", 5)] },
    { name := "rpm 300 (propeller J keys 0.7, 0.8; tip-Mach key 0.85)", half := only [("rpm", 300)] },
    { name := "h 880 +- 30 m (piston mixEff key 0.08845)", centre := [("h", 880)], half := only [("h", 30)] },
    { name := "v_rt 0.5 m/s (beta across 0, beta rule)", half := only [("v_rt", 0.5)] },
    { name := "v_dn 1 m/s (alpha across CDwbh key -0.0175)", half := only [("v_dn", 1)] },
    { name := "v_dn 2 m/s (alpha across 0: CLwbh, CYp, CYr, Clr)", half := only [("v_dn", 2)] },
    { name := "v_dn 0.5, v_rt 0.5, v_al 5, h 30, rpm 300", half := only [("v_dn", 0.5), ("v_rt", 0.5), ("v_al", 5), ("h", 30), ("rpm", 300)] },
    { name := "low: h 10 +- 2 m (ground-effect keys)", centre := [("h", 10)], half := only [("h", 2)] },
    { name := "low: h 3 +- 1 m (ground contact possible)", centre := [("h", 3)], half := only [("h", 1)] },
    { name := "track north: dpsi 0.01 (heading across 0)", psi := 0, half := only [("dpsi", 0.01)] } ]

def outputs (h : α) (y : Array α) (beta alpha : α) : Array α := #[h] ++ y ++ #[beta, alpha]
def outNames : Array String := #["h'"] ++ yNames.map (· ++ "'") ++ #["beta", "alpha"]

structure Tally where
  points : Nat := 0
  outside : Nat := 0

def readTrim (path : String) : IO (Array Float) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let a ← IO.ofExcept (j.getObjValAs? (Array Lean.JsonNumber) "trim")
  return a.map (·.toFloat)

/-! ## Table lookups over key intervals -/

/-- `x` as `m.mmmmmmeE` (Lean prints floats with six decimals). -/
def sci (x : Float) : String :=
  if x == 0 || !x.isFinite then toString x else
  let e := (Float.log10 x.abs).floor
  s!"{x / Float.pow 10 e}e{e.toInt64}"

def keysOf (t : Table) (col : Bool) : Array Float :=
  if col then (List.range t.cols).toArray.map fun c => ix t.data (c + 1)
  else (List.range t.rows).toArray.map fun r => ix t.data ((r + 1) * (t.cols + 1))

/-- A random key interval for `keys`: around one key (mostly straddling it), across several, or near and past the
ends. -/
def keyIv (keys : Array Float) (seed : UInt64) : (Float × Float) × UInt64 := Id.run do
  let (u0, s) := nextF seed; let (u1, s) := nextF s; let (u2, s) := nextF s; let (u3, s) := nextF s
  let k0 := ix keys 0
  let k1 := ix keys (keys.size - 1)
  let span := Max.max (k1 - k0) 1e-3
  let j := (u1 * keys.size.toFloat).toUInt64.toNat
  let gap := Max.max (if j + 1 < keys.size then ix keys (j + 1) - ix keys j else span / 4) 1e-6
  let w := gap * Float.pow 10 (-6 * u2)
  if u0 < 0.5 then
    let c := ix keys j + (u3 - 0.5) * w
    return ((c - w / 2, c + w / 2), s)
  else if u0 < 0.8 then
    let a := k0 - 0.2 * span + u2 * 1.4 * span
    let b := k0 - 0.2 * span + u3 * 1.4 * span
    return ((Min.min a b, Max.max a b), s)
  else
    let e := if u1 < 0.5 then k0 else k1
    let c := e + (u3 - 0.5) * 2 * gap
    return ((c - w, c + w), s)

def keyID (lo hi : Float) (lin : Bool) : ID := { v := Iv.out lo hi, d := #[], lin }

/-- Samples `m` key intervals per table and `p` points per interval (both ends plus uniform interior points); returns
(lookups, points, points outside). With `lin`, the row key is marked as β (`linRule`) and kept strictly between
`betaRuleMin` and `betaRuleMax`, as `frameBox` requires. -/
def tableCheck (name : String) (t : Table) (two lin : Bool) (m p : Nat) (seed : UInt64) :
    IO (Nat × Nat × Nat × UInt64) := do
  let rk := keysOf t false
  let ck := keysOf t true
  let mut seed := seed
  let mut pts := 0
  let mut bad := 0
  let mut first : Option String := none
  for _ in [0:m] do
    let ((rlo, rhi), s) := keyIv rk seed
    let ((clo, chi), s) := keyIv ck s
    seed := s
    let clampB (x : Float) : Float := Min.min (Max.max x (betaRuleMin + 1e-9)) (betaRuleMax - 1e-9)
    let (rlo, rhi) := if lin then (clampB rlo, clampB rhi) else (rlo, rhi)
    let enc : ID :=
      if two then t.get2 (keyID rlo rhi lin) (keyID clo chi false) else t.get1 (keyID rlo rhi lin)
    for k in [0:p] do
      let (u, s) := nextF seed; let (v, s) := nextF s
      seed := s
      let fr := if k == 0 then 0 else if k == 1 then 1 else u
      let x := Min.min (Max.max (rlo + fr * (rhi - rlo)) rlo) rhi
      let y := Min.min (Max.max (clo + v * (chi - clo)) clo) chi
      let val : Float := if two then t.get2 x y else t.get1 x
      pts := pts + 1
      unless enc.v.lo ≤ val && val ≤ enc.v.hi do
        bad := bad + 1
        if first.isNone then
          first := some s!"key {sci x}{if two then s!", {sci y}" else ""} gives {sci val} outside [{sci enc.v.lo}, {sci enc.v.hi}]"
  IO.println s!"  {name}{if lin then " (as beta)" else ""}: {m} key intervals, {pts - bad}/{pts} points inside"
  if let some f := first then IO.println s!"      first point outside: {f}"
  return (m, pts, bad, seed)

def tables1 : List (String × Table) :=
  [("stdTemp", Gen.tab_stdTemp), ("mixEff (piston)", Gen.tab_mixEff), ("cThrust", Gen.tab_cThrust),
   ("cPower", Gen.tab_cPower), ("CtMach", Gen.tab_CtMach), ("CpMach", Gen.tab_CpMach), ("kCDge", Gen.tab_kCDge_0),
   ("kCLge", Gen.tab_kCLge_1), ("CDDf", Gen.tab_CDDf_2), ("CLDf", Gen.tab_CLDf_8), ("Cmdf", Gen.tab_Cmdf_11),
   ("Clb", Gen.tab_Clb_9), ("Cnb", Gen.tab_Cnb_12)]
def tables2 : List (String × Table) :=
  [("CDwbh", Gen.tab_CDwbh_3), ("CYb", Gen.tab_CYb_4), ("CYp", Gen.tab_CYp_5), ("CYr", Gen.tab_CYr_6),
   ("CLwbh", Gen.tab_CLwbh_7), ("Clr", Gen.tab_Clr_10)]
def betaTables : List String := ["Clb", "Cnb", "CYb"]

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 200
  let trim ← readTrim "Tools/termsound/barrier_trim.json"
  if trim.size != 33 then throw (IO.userError s!"barrier_trim.json: {trim.size} entries, need 33")
  let base := mkBase
  let T : Term := {}
  let mut seed : UInt64 := 0x5eed
  let mut valid := 0
  let mut invalid := 0
  let mut vt : Tally := {}
  let mut it : Tally := {}
  IO.println s!"tsintervalcheck: {boxes.length} boxes around the level trim, {n} sampled points each (half vertices)"
  for bx in boxes do
    let c := bx.centre.foldl (fun a (k, v) => a.set! (col k) v) trim
    let r := frameBox T base bx.psi 0 c bx.half
    let enc := outputs r.h r.y r.beta r.alpha
    let mut outside := 0
    let mut firstBad : Option String := none
    for k in [0:n] do
      let mut x : Array Float := #[]
      for i in [0:33] do
        let (u, s) := nextF seed
        seed := s
        let t := if k % 2 == 0 then 2 * u - 1 else (if u < 0.5 then -1 else 1)
        x := x.push (ix c i + t * ix bx.half i)
      let ((h', y'), d, _) := frameG (α := Float) T base bx.psi 0 (ix x 0) (x.extract 1 33)
      let pt := outputs h' y' d.beta d.alpha
      let bad := (List.range pt.size).filter fun j =>
        let e := ix enc j
        !(e.v.lo ≤ ix pt j && ix pt j ≤ e.v.hi)
      if !bad.isEmpty then
        outside := outside + 1
        if firstBad.isNone then
          let j := bad.headD 0
          firstBad := some s!"{outNames.getD j "?"} = {ix pt j} outside [{(ix enc j).v.lo}, {(ix enc j).v.hi}] ({bad.length} outputs)"
    if r.valid then
      valid := valid + 1
      vt := { points := vt.points + n, outside := vt.outside + outside }
    else
      invalid := invalid + 1
      it := { points := it.points + n, outside := it.outside + outside }
    let status := if r.valid then (if outside == 0 then "VALID, sound on samples" else "VALID, UNSOUND") else "INVALID"
    IO.println s!"  {bx.name}: {status}; {n - outside}/{n} points inside; alpha [{r.alpha.v.lo}, {r.alpha.v.hi}], beta [{r.beta.v.lo}, {r.beta.v.hi}]"
    if let some m := firstBad then IO.println s!"      first point outside: {m}"
    unless r.valid do IO.println s!"      reasons: {"; ".intercalate r.reasons.toList}"
  IO.println s!"table lookups (get1/get2 over key intervals, {n} intervals per table, 20 points each):"
  let mut tl := 0
  let mut tp := 0
  let mut tb := 0
  for (two, ts) in [(false, tables1), (true, tables2)] do
    for (nm, t) in ts do
      for lin in (if betaTables.contains nm then [false, true] else [false]) do
        let (l, p, b, s) ← tableCheck nm t two lin n 20 seed
        seed := s
        tl := tl + l; tp := tp + p; tb := tb + b
  IO.println s!"valid boxes {valid}: {vt.points} points, {vt.outside} outside an enclosure"
  IO.println s!"table lookups {tl}: {tp} points, {tb} outside an enclosure"
  IO.println s!"invalid boxes {invalid} (explicit failures): {it.points} points, {it.outside} outside the (unusable) numbers"
  if vt.outside == 0 && tb == 0 then
    IO.println "PASS: every sampled point of every valid box and table lookup is inside its enclosure"
    return 0
  else
    IO.println "FAIL: an enclosure marked valid missed a sampled point"
    return 1

end TsIntervalCheck

def main (args : List String) : IO UInt32 := TsIntervalCheck.main args
