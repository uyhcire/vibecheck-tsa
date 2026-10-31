import Lean
import Envelope
open Lean Elab Command

/-! Axiom audit and trusted surface of the envelope theorems. Run: `lake env lean Tools/EnvelopeAudit.lean`. -/

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

/-- `#spec_surface thm`: the `Envelope` definitions the statement of `thm` depends on. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toList.filter fun c =>
    (`Envelope).isPrefixOf c && !c.isInternal && !Meta.isMatcherCore env c &&
      !(`Envelope.Checks).isPrefixOf c
  logInfo m!"{(own.map toString).toArray.qsort (· < ·)}"

#print axioms Envelope.never_hit
#print axioms Envelope.never_hit_tick
#print axioms Envelope.comparison
#print axioms Envelope.comparison_altitude
#print axioms Envelope.passthrough
#print axioms Envelope.monitor_iff
#print axioms Envelope.Checks.neverTrigger_unsafe
#print axioms Envelope.Checks.climb_allowed
#print axioms Envelope.Checks.P0_wf

#spec_surface Envelope.never_hit
