import Lean
import Envelope3D
open Lean Elab Command

/-! Axiom audit and trusted surface of the 3D envelope theorems. Run: `lake env lean Tools/Envelope3DAudit.lean`. -/

/-- Constants a theorem's statement mentions, followed through definition bodies (not proofs). -/
partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- `#spec_surface thm`: the `Envelope3D` definitions the statement of `thm` depends on. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toList.filter fun c =>
    ((`Envelope3D).isPrefixOf c || (`ExpEnvelope).isPrefixOf c) && !c.isInternal && !Meta.isMatcherCore env c &&
      !(`Envelope3D.Checks).isPrefixOf c
  logInfo m!"{(own.map toString).toArray.qsort (· < ·)}"

#print axioms Envelope3D.never_hit3d
#print axioms Envelope3D.never_hit3d_tick
#print axioms Envelope3D.never_hit3d_substeps
#print axioms Envelope3D.comparison
#print axioms Envelope3D.escLoop_mono
#print axioms Envelope3D.passthrough
#print axioms Envelope3D.substep_clear
#print axioms Envelope3D.monitor_iff
#print axioms Envelope3D.Checks.neverTrigger_unsafe
#print axioms Envelope3D.Checks.climb_allowed
#print axioms Envelope3D.Checks.P0_wf

#spec_surface Envelope3D.never_hit3d
#spec_surface Envelope3D.substep_clear
