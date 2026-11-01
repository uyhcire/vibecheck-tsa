import Ci.Rules
import Jsb.Enc

/-! Scoreboard-owned. -/

namespace Ci
open Vibecheck Jsb

structure Entry where
  family : String
  id : Nat
  params : String
  c : Commit
  deriving Inhabited

def stateRaw (s : State) : List Int :=
  [s.x, s.h, s.vx, s.vz, s.dx, s.dz, s.q, s.rpm, s.tmap, s.udot, s.wdot, s.stall, s.ah, s.au, s.qd, s.ah1, s.au1,
   s.pvz, s.pvz2].map (·.raw)

def stateOfRaw (xs : Array Int) (o : Nat) : State :=
  let f (i : Nat) : Fx := ⟨xs[o + i]!⟩
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15, f 16, f 17, f 18⟩

def benchHeader : String :=
  "family,id,params,x,h,vx,vz,dx,dz,q,rpm,tmap,udot,wdot,stall,ah,au,qd,ah1,au1,pvz,pvz2,pilot_elev,pilot_thr"

def Entry.toLine (e : Entry) : String :=
  ",".intercalate ([e.family, toString e.id, e.params] ++
    (stateRaw e.c.s ++ [e.c.pilot.elev.raw, e.c.pilot.thr.raw]).map toString)

def Entry.parse (l : String) : Option Entry := do
  let parts := l.splitOn ","
  guard (parts.length == 24)
  let nums ← (parts.drop 3).mapM String.toInt?
  let xs := nums.toArray
  some ⟨parts[0]!, (← parts[1]!.toNat?), parts[2]!, ⟨stateOfRaw xs 0, ⟨⟨xs[19]!⟩, ⟨xs[20]!⟩, ⟨0⟩, ⟨0⟩⟩⟩⟩

def fnv1a (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  return h

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.unif (r : Rng) (lo hi : Float) : Float × Rng :=
  let (x, r) := r.next
  (lo + (hi - lo) * (x >>> 11).toFloat / 9007199254740992.0, r)

def Rng.pick {β : Type} [Inhabited β] (r : Rng) (xs : Array β) : β × Rng :=
  let (x, r) := r.next
  (xs[(x % xs.size.toUInt64).toNat]!, r)

def benchPath : System.FilePath := "Ci/data/bench.csv"

def benchHash : UInt64 := 1107417647163377884

end Ci
