import CityGate

/-! The Lean side of `flight/src/bin/gatefaith.rs`, in its line formats: `laws STARTS OUT` and `reftraj`. -/

open CityGate Esc

def fnv (h : UInt64) (x : Float) : UInt64 := Id.run do
  let b : UInt64 := if x.isNaN then 0x7ff8000000000000 else x.toBits
  let mut h := h
  for i in [0:8] do
    h := (h ^^^ ((b >>> (8 * i).toUInt64) &&& 0xff)) * 0x100000001b3
  return h

def FNV0 : UInt64 := 0xcbf29ce484222325

def hex64 (b : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  "".pushn '0' (16 - s.length) ++ s

def hx (f : Float) : String := hex64 f.toBits

def unhx (s : String) : Float :=
  Float.ofBits (s.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt64) 0)

structure Start where
  id : Nat
  frames : Nat
  ox : Float
  oy : Float
  dump : FloatArray

def readStarts (path : String) : IO (Array Start) := do
  let ls ← IO.FS.lines path
  return ls.filterMap fun l =>
    let w := (l.splitOn " ").toArray
    if w[0]? != some "S" then none else
    let n := w[5]!.toNat!
    some { id := w[1]!.toNat!, frames := w[2]!.toNat!, ox := unhx w[3]!, oy := unhx w[4]!,
           dump := ⟨(w.extract 6 (6 + n)).map unhx⟩ }

def plane (s : Start) : Plane :=
  { st := (CityJsb.fromDump s.dump).get!, ob := (CityJsb.obsFromDump s.dump).get!, ox := s.ox, oy := s.oy }

def lawVals (l : Law) : Array Float :=
  #[l.t, l.ia, l.ib, l.iphi, l.psiRef, l.axis, l.side, l.nextTry, if l.captured then 1.0 else 0.0]

def surfVals (u : Surf) : Array Float := #[u.elev, u.ail, u.rud, u.thr]

/-- End-test verdicts follow `rollout_law`'s schedule but continue past the first pass. -/
def fly (st : Start) (esc : Nat) : Array UInt64 × Array (Nat × Bool) := Id.run do
  let mut p := plane st
  let mut law := Law.new esc
  let mut c := (Ctl.fresh default 0 law 0.0 HORIZON_FRAMES).record p
  let mut hs : Array UInt64 := #[]
  let mut ts : Array (Nat × Bool) := #[]
  for k in [1:st.frames + 1] do
    let (u, l) := law.step p
    law := l
    p := p.step u
    hs := hs.push ((surfVals u ++ p.ob.data ++ lawVals law).foldl fnv FNV0)
    if k % SAMPLE == 0 then
      c := { c with lk := k }.record p
      if k ≥ 768 && k % TERM_EVERY == 0 && law.turning then
        ts := ts.push (k, terminalOK law.dir law.kind c.hist)
  return (hs, ts)

def lawsCmd (sp out : String) : IO Unit := do
  let st ← readStarts sp
  let h ← IO.FS.Handle.mk out .write
  let jobs := st.toList.flatMap fun s => (List.range N_ESC).map fun e => (s, e)
  for (s, e) in jobs do
    let (id, (hs, ts)) := (s.id, fly s e)
    h.putStrLn s!"L {id} {e} {" ".intercalate (hs.map hex64).toList}"
    h.putStrLn (s!"T {id} {e}" ++ String.join (ts.map fun (k, v) => s!" {k}:{if v then 1 else 0}").toList)

/-- The reference-trajectory hashes of `docs/escape-law-terminal.md`. -/
def reftraj : IO Unit := do
  for (name, x, y, z, v, gam, psi, phi, n, thr, frames) in
      [("A", 0.0, 0.0, 150.0, 30.0, -0.1, FRAC_PI_2, 0.4, 1.0, 1.0, 2048),
       ("B", 0.0, 0.0, 950.0, 40.0, 0.1, FRAC_PI_2, 0.0, 1.0, 1.0, 5120),
       ("C", 0.0, 0.0, 950.0, 40.0, 0.1, FRAC_PI_2, 0.3, 1.0, 1.0, 6400)] do
    let mut p := startPlane x y z v gam psi phi n thr
    let mut law := Law.new 0
    let mut h := FNV0
    for _ in [0:frames] do
      let (u, l) := law.step p
      law := l
      p := p.step u
      let (px, py, pz) := p.pos
      h := (surfVals u ++ #[px, py, pz]).foldl fnv h
    IO.println s!"start {name}, {frames} frames: HASH {hex64 h}"

def main (args : List String) : IO Unit := do
  match args with
  | "laws" :: sp :: out :: _ => lawsCmd sp out
  | "reftraj" :: _ => reftraj
  | _ => IO.eprintln "usage: gatefaith laws STARTS OUT | reftraj"
