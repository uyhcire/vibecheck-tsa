import Lake
open Lake DSL

package proofharness

require vibecheck from "../../.."

lean_lib PfAffLib where
  roots := #[`PfAff, `PfReal, `PfJac]

lean_exe pfprobe where
  root := `PfProbe
