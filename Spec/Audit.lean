import Lean

namespace SpecAudit
open Lean Elab Command

partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some (.inductInfo i) => i.type.getUsedConstants.toList ++ i.ctors
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  go [thm] {}

def surfaceIn (env : Environment) (thm : Name) (pre : Name) : List Name :=
  (specSurface env thm).toList.filter fun c =>
    let inPre := match env.getModuleIdxFor? c with
      | some i => pre.isPrefixOf env.header.moduleNames[i.toNat]!
      | none => pre.isPrefixOf env.mainModule
    inPre && !c.isInternal && !Meta.isMatcherCore env c

/-- `#spec_surface thm in Pre`: the definitions from modules `Pre.*` that the statement of `thm` depends on. -/
elab "#spec_surface " id:ident " in " pre:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (surfaceIn env thm pre.getId).toArray.qsort (·.toString < ·.toString)
  logInfo m!"{own.size} names: {own.toList}"

/-- `#audit_axioms thm`: print the axioms `thm` depends on. -/
elab "#audit_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  logInfo m!"{thm}: {axs.toList}"

end SpecAudit
