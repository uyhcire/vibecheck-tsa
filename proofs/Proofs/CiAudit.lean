import Lean
import Proofs.CiClaims

/-! Scoreboard-owned: build-time audit of `Proofs.CiClaims.claimed`, same row format as `Ci.Report.auditRows`. -/

namespace Proofs.CiAudit
open Lean Meta Elab Term

unsafe def claimedUnsafe : MetaM (List Name) := evalConst (List Name) ``Proofs.CiClaims.claimed

@[implemented_by claimedUnsafe] opaque claimedNames : MetaM (List Name)

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def lawExprs : MetaM (Array Expr) := do
  let mut e ← whnf (mkApp (mkConst ``Ci.Submission.laws) (mkConst ``Ci.Agent.submission))
  let mut out := #[]
  for _ in [0:64] do
    match e.getAppFnArgs with
    | (``List.cons, #[_, hd, tl]) => out := out.push hd; e ← whnf tl
    | _ => break
  return out

elab "ci_audit_ext%" : term => do
  let laws ← lawExprs
  let mut rows : Array String := #[]
  for n in (← claimedNames) do
    let some ci := (← getEnv).find? n | rows := rows.push s!"{n}|<missing>|false|none|-1"; continue
    let axs ← collectAxioms n
    let std := axs.all stdAxioms.contains
    let (kind, law) ← match ci.type.getAppFnArgs with
      | (``Ci.Goals.TSafe, #[L]) | (``Ci.Goals.TInvariant, #[L]) => do
        let mut idx : Int := -1
        for i in [0:laws.size] do
          if idx < 0 then
            if ← isDefEq L laws[i]! then idx := i
        pure ((ci.type.getAppFn.constName!.toString), idx)
      | _ => pure ("other", (-1 : Int))
    rows := rows.push s!"{n}|{",".intercalate (axs.toList.map toString)}|{std}|{kind}|{law}"
  return toExpr rows.toList

def rows : List String := ci_audit_ext%

end Proofs.CiAudit
