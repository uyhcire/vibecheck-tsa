import JsbExact.Model
import Std.Data.HashMap

/-! `jsbx RUN [step|tick|free]`: lockstep residuals of `JsbExact.step` against `jsbx/harness.cpp` dumps. -/

open JsbExact

structure Run where
  names : Array String
  nf : Nat
  data : FloatArray

def Run.col (r : Run) (n : String) : Nat := (r.names.idxOf? n).getD (panic! s!"no column {n}")

def Run.get (r : Run) (k : Nat) (c : Nat) : Float := r.data[k * r.nf + c]!

def loadRun (pfx : String) : IO Run := do
  let names := ((← IO.FS.readFile (pfx ++ ".names")).splitOn "\n").filter (· ≠ "") |>.toArray
  let bytes ← IO.FS.readBinFile (pfx ++ ".bin")
  let n := bytes.size / 8
  let mut fa : FloatArray := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let mut u : UInt64 := 0
    for j in [0:8] do
      u := u ||| ((bytes[8 * i + j]!).toUInt64 <<< (8 * j).toUInt64)
    fa := fa.push (Float.ofBits u)
  return { names, nf := names.size, data := fa }

def stateOf (r : Run) (k : Nat) : State Float :=
  let g := fun n => r.get k (r.col n)
  let v := fun p => (⟨g (p ++ "1"), g (p ++ "2"), g (p ++ "3")⟩ : V3 Float)
  { q := ⟨g "qi1", g "qi2", g "qi3", g "qi4"⟩, qdot := ⟨g "qdot1", g "qdot2", g "qdot3", g "qdot4"⟩,
    pqri := v "pqri", ri := v "ri", vi := v "vi", vih0 := v "vih0_", vih1 := v "vih1_", aih0 := v "aih0_",
    epa := g "epa", pqridot := v "pqridot", uvwidot := v "uvwidot", uvwdot := v "uvwdot", stall := g "stall",
    cg := v "cg", tank0 := g "tank0", tank1 := g "tank1", tmap := g "tmap", running := g "running" != 0.0,
    fuelflow := g "fuelflow", starved := g "starved" != 0.0, rpm := g "rpm", act := v "actxyz",
    lastcg := v "lastcg", wind := v "d_wind", gears := (List.range Gen.gears.size).toArray.map fun i =>
      let p := s!"g{i}_"
      { wow := g (p ++ "wow") != 0.0, lm0 := g (p ++ "lm0"), lm1 := g (p ++ "lm1"), lm2 := g (p ++ "lm2"),
        slip := g (p ++ "slip"), steer := g (p ++ "steer"), act := v (p ++ "act"),
        mT := M33.mk' (g (p ++ "mT11")) (g (p ++ "mT12")) (g (p ++ "mT13")) (g (p ++ "mT21")) (g (p ++ "mT22"))
                (g (p ++ "mT23")) (g (p ++ "mT31")) (g (p ++ "mT32")) (g (p ++ "mT33")) } }

def inputOf (r : Run) (k : Nat) : Input Float :=
  let g := fun n => r.get k (r.col n)
  { elev := g "u_elev", ail := g "u_ail", rud := g "u_rud", thr := g "u_thr", mix := g "u_mix",
    brkL := g "u_brkL", brkR := g "u_brkR" }

def fields (s : State Float) (d : Diag Float) : List (String × Float) :=
  let v := fun (p : String) (x : V3 Float) => [(p ++ "1", x.x), (p ++ "2", x.y), (p ++ "3", x.z)]
  v "uvw" d.uvw ++ v "pqr" d.pqr ++ v "ecef" d.loc ++
  [("phi", d.euler.x), ("theta", d.euler.y), ("psi", d.euler.z), ("hsl", d.hsl), ("rpm", s.rpm),
   ("qi1", s.q.q0), ("qi2", s.q.q1), ("qi3", s.q.q2), ("qi4", s.q.q3)] ++
  v "vi" s.vi ++ v "ri" s.ri ++ v "pqri" s.pqri ++ v "uvwdot" s.uvwdot ++ v "pqridot" s.pqridot ++ v "uvwidot" s.uvwidot ++
  [("epa", s.epa), ("stall", s.stall), ("tank0", s.tank0), ("tank1", s.tank1), ("tmap", s.tmap),
   ("fuelflow", s.fuelflow), ("running", if s.running then 1.0 else 0.0)] ++ v "cg" s.cg ++ v "actxyz" s.act ++
  v "vned" d.vned ++
  [("d_alpha", d.alpha), ("d_beta", d.beta), ("d_adot", d.adot), ("d_qbar", d.qbar), ("d_vt", d.vt),
   ("d_mach", d.mach), ("d_pt", d.pt), ("d_hmac", d.hmac), ("d_rho", d.rho), ("d_p", d.p), ("d_t", d.t),
   ("d_a", d.a), ("d_thrust", d.thrust), ("d_hp", d.hp), ("d_mass", d.mass), ("d_agl", d.agl),
   ("d_de", d.de), ("d_da", d.da), ("d_dr", d.dr)] ++
  v "d_grav" d.grav ++ v "d_fnat" d.fnat ++ v "d_mmrc" d.mmrc ++ v "d_faero" d.faero ++ v "d_maero" d.maero ++ v "d_fprop" d.fprop ++ v "d_mprop" d.mprop ++
  v "d_ftot" d.ftot ++ v "d_mtot" d.mtot ++ v "d_fgear" d.fgear ++ v "d_mgear" d.mgear ++ v "d_ffric" d.ffric ++
  v "lastcg" s.lastcg ++
  ((List.range s.gears.size).flatMap fun i =>
    let g := s.gears[i]!
    let p := s!"g{i}_"
    [(p ++ "wow", if g.wow then 1.0 else 0.0), (p ++ "lm0", g.lm0), (p ++ "lm1", g.lm1), (p ++ "lm2", g.lm2),
     (p ++ "slip", g.slip), (p ++ "steer", g.steer), (p ++ "d_fz", d.gearFz[i]!)] ++ v (p ++ "act") g.act)

def stepN (r : Run) (k n : Nat) : State Float × Diag Float := Id.run do
  let mut s := stateOf r k
  let mut d : Diag Float := (step s (inputOf r k)).2
  for i in [0:n] do
    let (s', d') := step s (inputOf r (k + i))
    s := s'
    d := d'
  return (s, d)

def quantile (xs : Array Float) (p : Float) : Float :=
  if xs.isEmpty then 0.0 else
  let ys := (xs.filter (· != 0.0)).qsort (· < ·)
  let z := xs.size - ys.size
  let idx := min (xs.size - 1) (p * (xs.size.toFloat - 1)).round.toUInt64.toNat
  if idx < z then 0.0 else ys[idx - z]!

def fmt (x : Float) : String :=
  if x == 0.0 then "0" else
  let e := (Float.log10 (Float.abs x)).floor
  let m := x / Float.pow 10.0 e
  s!"{(m * 100.0).round / 100.0}e{e.toInt64}"

def main (args : List String) : IO Unit := do
  let pfx := args.headD "ext/data/t_on"
  let mode := args.getD 1 "step"
  let verbose := args.getD 2 "" == "verbose"
  let n := if mode == "tick" then 8 else 1
  let r ← loadRun pfx
  let nrec := r.data.size / r.nf
  let cEp := r.col "ep"
  let cK := r.col "k"
  let cStop := r.col "stop"
  let names := (fields (stateOf r 0) (step (stateOf r 0) (inputOf r 0)).2).map (·.1) |>.toArray
  let cols := names.map r.col
  let mut errs : Array FloatArray := names.map fun _ => FloatArray.emptyWithCapacity nrec
  let mut exact : Array Nat := names.map fun _ => 0
  let mut starts : Array Nat := #[]
  for k in [0:nrec] do
    if k + n ≥ nrec then break
    if mode == "tick" && (r.get k cK).toUInt64.toNat % 8 != 0 then continue
    let mut ok := r.get (k + n) cEp == r.get k cEp
    for i in [0:n] do
      if r.get (k + i) cStop != 0.0 then ok := false
    if ok then starts := starts.push k
  if mode == "bench" then
    let mut eps : Array (State Float × Nat × Nat) := #[]
    let mut k := 0
    while k < nrec do
      let ep := r.get k cEp
      let mut j := k
      while j + 1 < nrec && r.get (j + 1) cEp == ep && r.get j cStop == 0.0 do j := j + 1
      eps := eps.push (stateOf r k, k, j)
      k := j + 1
    let inputs := (List.range nrec).toArray.map (inputOf r)
    let t0 ← IO.monoNanosNow
    let mut acc := 0.0
    let mut n := 0
    for (s0, a, b) in eps do
      let mut s := s0
      for j in [a:b] do
        s := (step s inputs[j]!).1
        n := n + 1
      acc := acc + s.vi.x
    let t1 ← IO.monoNanosNow
    IO.println s!"{pfx} mode=bench: {n} open-loop steps, {(t1 - t0).toFloat / n.toFloat / 1000.0} us/step (checksum {acc})"
    return
  if mode == "free" then
    let mut worst : Float := 0.0
    let mut nexact := 0
    let mut ncmp := 0
    let mut k := 0
    while k < nrec do
      let ep := r.get k cEp
      let mut s := stateOf r k
      let mut j := k
      while j + 1 < nrec && r.get (j + 1) cEp == ep && r.get j cStop == 0.0 do
        let (s', d) := step s (inputOf r j)
        s := s'
        let mut i := 0
        let mut allExact := true
        for (_, val) in fields s d do
          let ref := r.get (j + 1) cols[i]!
          if val.toBits != ref.toBits then
            allExact := false
            worst := max worst (Float.abs (val - ref))
          i := i + 1
        if allExact then nexact := nexact + 1
        ncmp := ncmp + 1
        j := j + 1
      k := j + 1
    IO.println s!"{pfx} mode=free (each episode run open-loop from its first record): {nexact}/{ncmp} steps with all {names.size} fields bit-exact; worst abs difference {worst}"
    return
  let t0 ← IO.monoNanosNow
  let mut acc := 0.0
  for k in starts do
    acc := acc + (stepN r k n).1.vi.x
  let t1 ← IO.monoNanosNow
  for k in starts do
    let (s, d) := stepN r k n
    let mut i := 0
    for (name, val) in fields s d do
      let ref := r.get (k + n) cols[i]!
      errs := errs.modify i (·.push (Float.abs (val - ref)))
      if val.toBits == ref.toBits then exact := exact.modify i (· + 1)
      else if verbose then
        IO.println s!"mismatch ep {r.get k cEp} k {r.get k cK} {name}: model {val} ref {ref}"
      i := i + 1
  let nsteps := starts.size * n
  IO.println s!"{pfx} mode={mode}: {starts.size} comparisons, {(t1 - t0).toFloat / nsteps.toFloat / 1000.0} us per model step (checksum {acc})"
  IO.println "field            bit-exact      p50        p99        max"
  for i in [0:names.size] do
    let es := errs[i]!.toList.toArray
    let name := names[i]!
    IO.println s!"{name.pushn ' ' (16 - name.length)} {exact[i]!}/{es.size}  {fmt (quantile es 0.5)}  {fmt (quantile es 0.99)}  {fmt (quantile es 1.0)}"
