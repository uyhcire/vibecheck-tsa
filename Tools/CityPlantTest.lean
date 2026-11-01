import CityJsb.Plant

/-! Hands-off flight from `CityJsb.init`: prints the state once a second. -/

open CityJsb

def main : IO Unit := do
  let mut s := init 300 50 0 (Float.ofNat 90 * 3.14159265 / 180) 0 0.03
  for k in [0:128 * 20] do
    let (s', o) := stepE s (-0.05) 0 0 0.7
    s := s'
    if k % 128 == 127 then
      IO.println s!"t={(k + 1) / 128} N={o[0]!} E={o[1]!} h={o[2]!} vt={o[6]!} phi={o[7]!} th={o[8]!} psi={o[9]!} a={o[13]!} nz={o[15]!} rpm={o[18]!}"
