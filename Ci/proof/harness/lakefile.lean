import Lake
open Lake DSL

package proofharness

require vibecheck from "../../.."

lean_lib PfAffLib where
  roots := #[`PfAff]

lean_exe pfprobe where
  root := `PfProbe
