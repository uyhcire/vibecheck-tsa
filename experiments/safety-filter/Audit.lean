import Lean
import Filters
open Lean Elab Command

/-! Axiom audit and trusted surface of the `SafetyFilter` interface and its instances.
Run: `lake env lean Tools/FiltersAudit.lean`. -/

/-- Constants a declaration's type mentions, followed through definition bodies (not proofs). -/
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

/-- Whether `c` is declared in this project (`ExpVibecheck`, `ExpEnvelope` or `Filters` modules). -/
def isOwn (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => [`ExpVibecheck, `ExpEnvelope, `Filters].contains (env.header.moduleNames[i.toNat]!).getRoot
  | none => true

/-- `#spec_surface thm`: the project definitions the statement of `thm` depends on. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toList.filter fun c =>
    isOwn env c && !c.isInternal && !Meta.isMatcherCore env c
  logInfo m!"{(own.map toString).toArray.qsort (· < ·)}"

-- The instances (their `guarantee` fields) and the named guarantees.
#print axioms Filters.rolloutFilter
#print axioms Filters.rollout_guarantee
#print axioms Filters.rollout_recovers_flight_never_crashes
#print axioms Filters.envelopeFilter
#print axioms Filters.envelope_guarantee
#print axioms Filters.envelopeSubsteps
#print axioms Filters.envelope_recovers_never_hit
#print axioms Filters.envelope_recovers_never_hit_substeps
-- Generic theorems.
#print axioms Filters.SafetyFilter.always_safe
#print axioms Filters.SafetyFilter.safe_while_monitored
#print axioms Filters.SafetyFilter.run_safe
#print axioms Filters.SubstepCheck.safe_of_checks
-- Conversion.
#print axioms Filters.fxFloor_le
#print axioms Filters.le_fxCeil

#spec_surface Filters.SafetyFilter.guarantee
#spec_surface Filters.rollout_guarantee
#spec_surface Filters.envelope_guarantee
