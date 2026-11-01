import Ci.proof.Law
import Ci.Bench
open Vibecheck Jsb Ci Ci.Lawfirst

/-! Numerics for the T proof: batch one-tick evaluation of the lawfirst law. Reads lines of 21 ints
(19 raw state fields, eI, ac) on stdin and prints the tick image (21 ints, safe, climb). -/

def L : Law := { law1 with step := Ci.Proof.step }

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
  o.putStrLn s!"{showA (ofState s)} {m.eI} {m.ac} {ok} {cl}"
  o.flush
  loop h o k

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
