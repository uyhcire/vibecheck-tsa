import Ci.proof.T
import Ci.proof.LawIv
import Ci.proof.SafeIv
import PfAff
import PfReal
import PfJac
import Jsb.Enc
import Ci.Bench
open Vibecheck Jsb Ci Ci.Lawfirst

/-! Numerics for the T proof: batch one-tick evaluation of the lawfirst law. Reads lines of 21 ints
(19 raw state fields, eI, ac) on stdin and prints the tick image (21 ints, safe, climb). -/

def L : Law := Ci.Proof.lawT

def toState (a : Array Int) : State :=
  ⟨⟨a[0]!⟩, ⟨a[1]!⟩, ⟨a[2]!⟩, ⟨a[3]!⟩, ⟨a[4]!⟩, ⟨a[5]!⟩, ⟨a[6]!⟩, ⟨a[7]!⟩, ⟨a[8]!⟩, ⟨a[9]!⟩, ⟨a[10]!⟩,
   ⟨a[11]!⟩, ⟨a[12]!⟩, ⟨a[13]!⟩, ⟨a[14]!⟩, ⟨a[15]!⟩, ⟨a[16]!⟩, ⟨a[17]!⟩, ⟨a[18]!⟩⟩

def ofState (s : State) : Array Int :=
  #[s.x.raw, s.h.raw, s.vx.raw, s.vz.raw, s.dx.raw, s.dz.raw, s.q.raw, s.rpm.raw, s.tmap.raw, s.udot.raw,
    s.wdot.raw, s.stall.raw, s.ah.raw, s.au.raw, s.qd.raw, s.ah1.raw, s.au1.raw, s.pvz.raw, s.pvz2.raw]

def showA (a : Array Int) : String := " ".intercalate (a.toList.map toString)

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) (k : Nat) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!
  let a := ws.toArray
  if a.size < 21 then return
  let mut s := toState a
  let mut m : Mem := ⟨a[19]!, a[20]!⟩
  let mut ok := true
  let mut cl := true
  for _ in [0:k] do
    let r := tickT L s m
    s := r.s; m := r.m; ok := ok && r.safe; cl := cl && r.climb
  o.putStrLn s!"{showA (ofState s)} {m.eI} {m.ac} {ok} {cl} {L.inT (toState a, (⟨a[19]!, a[20]!⟩ : Mem))} {L.inT (s, m)}"
  o.flush
  loop h o k

/-- interval product of raw Ints (no rescale) -/
def pI (a b c d : Int) : Int × Int := (min (min (a*c) (a*d)) (min (b*c) (b*d)), max (max (a*c) (a*d)) (max (b*c) (b*d)))
def lo' : Iv → Int | .box a _ => a | .top => -1000000000000
def hi' : Iv → Int | .box _ b => b | .top => 1000000000000
def safeI (S : StateOf Iv) : List Bool :=
  let (vx0, vx1) := (lo' S.vx, hi' S.vx); let (vz0, vz1) := (lo' S.vz, hi' S.vz)
  let (dx0, dx1) := (lo' S.dx, hi' S.dx); let (dz0, dz1) := (lo' S.dz, hi' S.dz)
  let a := pI vx0 vx1 dx0 dx1; let b := pI vz0 vz1 dz0 dz1
  let c := pI vx0 vx1 dz0 dz1; let d := pI vz0 vz1 dx0 dx1
  let u0 := a.1 + b.1; let u1 := a.2 + b.2
  let w1 := c.2 - d.1
  let alpha := decide (0 < u0) && decide (w1 * 65536 ≤ Ci.alphaTanMax * u0)
  let au := (lo' S.au + Ci.gRaw, hi' S.au + Ci.gRaw)
  let l1 := pI au.1 au.2 dx0 dx1; let l2 := pI (lo' S.ah) (hi' S.ah) dz0 dz1
  let load := decide (10 * (l1.2 - l2.1) ≤ Ci.loadMaxX10 * Ci.gRaw * 65536)
  let v2 := (pI vx0 vx1 vx0 vx1).1 + (if vz0 ≤ 0 && 0 ≤ vz1 then 0 else min (vz0*vz0) (vz1*vz1))
  let speed := decide (Ci.vFloor * Ci.vFloor ≤ v2)
  let stall := decide (lo' S.stall = 0 && hi' S.stall = 0)
  let hok := decide (Ci.clearance ≤ lo' S.h && hi' S.h ≤ Ci.hMax)
  [alpha, load, speed, stall, hok]

/-- checkRec with a leaf count: (passes, leaves) -/
partial def countRec (dims : List (Nat × Int)) : Nat → CLOf Iv → Bool × Nat
  | 0, B => (Ci.Proof.SafeIv.ok B, 1)
  | n + 1, B =>
    if Ci.Proof.SafeIv.ok B then (true, 1) else
    let p := halve B (pick dims B)
    let (a, na) := countRec dims n p.1
    if !a then (false, na) else
    let (b, nb) := countRec dims n p.2
    (b, na + nb)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["traj", n] =>
    let line ← (← IO.getStdin).getLine
    let a := ((line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
    let mut s := toState a
    let mut m : Mem := ⟨a[19]!, a[20]!⟩
    for k in [0:n.toNat! + 1] do
      IO.println s!"{k} {showA (ofState s)} {m.eI} {m.ac} {L.inT (s, m)}"
      let r := tickT L s m
      s := r.s; m := r.m
    return 0
  | ["frozen", n] =>
    -- equilibrium at a frozen altitude: h is reset to its initial value before every tick
    let h := (← IO.getStdin)
    let mut out : Array String := #[]
    repeat
      let line ← h.getLine
      if line.isEmpty then break
      let a := ((line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
      if a.size < 21 then break
      let mut s := toState a
      let mut m : Mem := ⟨a[19]!, a[20]!⟩
      for _ in [0:n.toNat!] do
        let r := tickT L { s with h := ⟨a[1]!⟩, x := ⟨0⟩ } m
        s := r.s; m := r.m
      IO.println s!"{showA (ofState { s with h := ⟨a[1]!⟩, x := ⟨0⟩ })} {m.eI} {m.ac}"
    return 0
  | ["ivcheck"] =>
    let h := (← IO.getStdin)
    repeat
      let line ← h.getLine
      if line.isEmpty then break
      let a := ((line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
      if a.size < 42 then break
      let S : StateOf Iv := ⟨.box a[0]! a[19]!, .box a[1]! a[20]!, .box a[2]! a[21]!, .box a[3]! a[22]!, .box a[4]! a[23]!,
        .box a[5]! a[24]!, .box a[6]! a[25]!, .box a[7]! a[26]!, .box a[8]! a[27]!, .box a[9]! a[28]!, .box a[10]! a[29]!,
        .box a[11]! a[30]!, .box a[12]! a[31]!, .box a[13]! a[32]!, .box a[14]! a[33]!, .box a[15]! a[34]!, .box a[16]! a[35]!,
        .box a[17]! a[36]!, .box a[18]! a[37]!⟩
      let mut U : InputOf Iv := ⟨.box a[38]! a[39]!, .box a[40]! a[41]!, .box 0 0, .box 0 0⟩
      if a.size ≥ 48 then
        let r0 := (Jsb.atmLookup Jsb.C172.atmRho ⟨a[20]!⟩).raw
        let r1 := (Jsb.atmLookup Jsb.C172.atmRho ⟨a[1]!⟩).raw
        let b : Ci.Proof.LawIv.Box := ⟨(a[2]!, a[21]!), (a[3]!, a[22]!), (a[4]!, a[23]!), (a[5]!, a[24]!), (a[6]!, a[25]!),
          (a[12]!, a[31]!), (a[13]!, a[32]!), (min r0 r1, max r0 r1), (a[46]!, a[47]!)⟩
        match Ci.Proof.LawIv.elev b with
        | some e => U := { U with elev := .box e.1 e.2 }; IO.print s!"elev[{e.1},{e.2}] "
        | none => IO.print "elev[none] "
      let mut cur := S
      let mut outs : Array String := #[]
      -- D1 ∋ vz − pvz, D2 ∋ pvz − pvz2 (tracked separately to avoid wrapping in ab3)
      let mut d1 : Int × Int := (a[3]! - a[36]!, a[22]! - a[17]!)
      let mut d2 : Int × Int := (a[17]! - a[37]!, a[36]! - a[18]!)
      if a.size ≥ 46 then
        d1 := (a[42]!, a[43]!); d2 := (a[44]!, a[45]!)
      for _ in [0:8] do
        -- ab3 = (12 vz + 11 D1 − 5 D2) / 12
        let n0 := 12 * lo' cur.vz + 11 * d1.1 - 5 * d2.2
        let dh := Iv.shr (.box (n0 / 12) ((12 * hi' cur.vz + 11 * d1.2 - 5 * d2.1) / 12)) 7
        let nd1 := Iv.shr (Iv.sub (Iv.mul (.box 196608 196608) cur.au) cur.au1) 8
        d2 := d1
        d1 := (lo' nd1, hi' nd1)
        let nx := step 7 true U cur
        let fl := safeI nx
        let climb := decide (Ci.climbVz ≤ lo' nx.vz) && decide (1 ≤ lo' dh) || decide (Ci.climbTop ≤ lo' nx.h)
        outs := outs.push s!"{fl.map (fun b => if b then 1 else 0)}{if climb then 1 else 0} vz[{lo' nx.vz},{hi' nx.vz}] q[{lo' nx.q},{hi' nx.q}] au[{lo' nx.au},{hi' nx.au}]"
        cur := nx
      IO.println (" | ".intercalate outs.toList)
    return 0
  | ["safecheck", depth, hw, focus] =>
    let h := (← IO.getStdin)
    repeat
      let line ← h.getLine
      if line.isEmpty then break
      let a := ((line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
      if a.size < 40 then break
      let S : StateOf Iv := ⟨.top, .box a[1]! a[20]!, .box a[2]! a[21]!, .box a[3]! a[22]!, .box a[4]! a[23]!,
        .box a[5]! a[24]!, .box a[6]! a[25]!, .box a[7]! a[26]!, .box a[8]! a[27]!, .box a[9]! a[28]!, .box a[10]! a[29]!,
        .box a[11]! a[30]!, .box a[12]! a[31]!, .box a[13]! a[32]!, .box a[14]! a[33]!, .box a[15]! a[34]!, .box a[16]! a[35]!,
        .box a[17]! a[36]!, .box a[18]! a[37]!⟩
      let B : CLOf Iv := ⟨S, .box a[38]! a[39]!⟩
      let dims : List (Nat × Int) := (List.range 20).filterMap fun i =>
        if i == 0 || i == 11 then none else
        let w := width (B.get i)
        let fs := (focus.splitOn ",").map String.toNat!
        if w ≤ 0 then none else some (i, (if i == 1 then hw.toInt! else if fs.contains i then 10 else 1) * 1000000000000 / w)
      let (okv, n) := countRec dims depth.toNat! B
      IO.println s!"{okv} {n}"
    return 0
  | ["aff"] => PfAff.run; return 0
  | ["realgap"] => PfReal.run; return 0
  | ["jac"] => PfJac.run; return 0
  | ["elevof"] =>
    let h := (← IO.getStdin)
    repeat
      let line ← h.getLine
      if line.isEmpty then break
      let a := ((line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.map String.toInt!).toArray
      if a.size < 21 then break
      let r := Ci.Proof.step ⟨a[19]!, a[20]!⟩ (toState a)
      IO.println s!"{r.1.elev.raw},{r.2.eI}"
    return 0
  | ["tick", k] => loop (← IO.getStdin) (← IO.getStdout) k.toNat!; return 0
  | ["bench", i, n] =>
    let lines := (← IO.FS.lines "../../../Ci/data/bench.csv").toList.drop 1
    let some e := (lines.filterMap Ci.Entry.parse)[i.toNat!]? | return 2
    let mut s := e.c.s
    let mut m := L.init e.c
    for k in [0:n.toNat! + 1] do
      IO.println s!"{k} {showA (ofState s)} {m.eI} {m.ac} {L.inT (s, m)}"
      let r := tickT L s m
      s := r.s; m := r.m
    return 0
  | _ => return 1
