import Vibecheck
open Vibecheck

/-! Autoland under injected per-tick velocity disturbances (spike tooling, not verified). -/

def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- Disturbance in [-d, d] (raw Fx units); mode 0 random, 1 sustained sink, 2 sustained headwind+sink. -/
def dist (mode : Nat) (seed : Nat) (d : Int) : Int × Int × Int :=
  let r1 := lcg seed; let r2 := lcg r1; let r3 := lcg r2
  let u (r : Nat) : Int := (r : Int) % (2 * d + 1) - d
  match mode with
  | 0 => (u r1, u r2, u r3 / 3)
  | 1 => (0, -d, 0)
  | _ => (-d, -d, 0)

partial def fly (r : Runway) (mode : Nat) (d : Int) (s : State) (seed k : Nat) : State × Nat :=
  if s.crashed || s.parked || k > 16 * 300 then (s, k)
  else
    let s' := step s (Autoland.control r s)
    let (ex, ez, eq) := dist mode seed d
    let s'' := if s'.phase == .air then
      { s' with vx := Fx.mk (s'.vx.raw + ex), vz := Fx.mk (s'.vz.raw + ez), q := Fx.mk (s'.q.raw + eq) } else s'
    fly r mode d s'' (lcg (lcg (lcg seed))) (k + 1)

def main : IO Unit := do
  let starts : List (Nat × Int × Int × Int) :=
    [(1, 1500, 200, 40), (1, 2300, 300, 40), (2, 4300, 250, 40), (2, 5400, 450, 35), (2, 6000, 300, 40)]
  for dmm in [0, 20, 50, 100, 200, 300] do
    let d : Int := dmm * 65536 / 1000
    for mode in [0, 1, 2] do
      let mut ok := 0; let mut total := 0; let mut fails : List String := []
      for (ri, x, h, v) in starts do
        for seed in [1, 2, 3, 4] do
          let r := runways.toArray[ri]!
          let xi : Fx := ⟨x * 65536⟩
          let hi : Fx := ⟨h * 65536⟩
          let vi : Fx := ⟨v * 65536⟩
          let s0 : State := { initState with x := xi, h := hi, vx := vi, phase := Phase.air, elev := (0.2 : Fx) }
          let (e, _) := fly r mode d s0 seed 0
          total := total + 1
          if e.parked then ok := ok + 1
          else fails := s!"{repr e.phase}" :: fails
          if mode != 0 then break
      IO.println s!"D={dmm} mm/s/tick mode={mode}: landed {ok}/{total} {fails.eraseDups.take 3}"
