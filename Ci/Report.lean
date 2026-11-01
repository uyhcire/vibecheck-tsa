import Lean
import Ci.Audit
import Ci.Baseline

/-! Scoreboard-owned: build-time audit of `Ci.Audit.claimed` and the static rule R4. -/

namespace Ci.Report
open Lean Meta Elab Term

def dynamics : List Name :=
  [``Jsb.integrate, ``Jsb.evaluate, ``Jsb.step, ``Jsb.tickAB, ``Jsb.tickEuler, ``Jsb.probe, ``Jsb.Escape.tick]

def isBanned (env : Environment) (n : Name) : Bool :=
  dynamics.contains n || match env.find? n with
    | some ci => ci.type.getUsedConstants.contains ``Jsb.C172.AeroIn && n != ``Jsb.C172.AeroIn
    | none => false

/-- Constants reachable from `todo` through definition bodies and `implemented_by` targets (proofs not followed). -/
partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | c :: rest =>
    if seen.contains c then closure env rest seen else
    let next := match env.find? c with
      | some (.defnInfo d) => d.value.getUsedConstants.toList
      | some (.opaqueInfo d) => d.value.getUsedConstants.toList
      | _ => []
    closure env ((Compiler.getImplementedBy? env c).toList ++ next ++ rest) (seen.insert c)

elab "ci_static% " id:ident : term => do
  let env ← getEnv
  let c ← realizeGlobalConstNoOverloadWithInfo id
  let bad := (closure env [c] {}).toList.filter (isBanned env)
  return toExpr (bad.map toString)

unsafe def claimedUnsafe : MetaM (List Name) := evalConst (List Name) ``Ci.Audit.claimed

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

/-- One `|`-separated row per claim: name, axioms, all-standard flag, goal kind, law index (or -1). -/
elab "ci_audit%" : term => do
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

def auditRows : List String := ci_audit%

def staticAgent : List String := ci_static% Ci.Agent.submission
def staticBox : List String := ci_static% Ci.Baseline.box
def staticInterior : List String := ci_static% Ci.Baseline.interior

end Ci.Report
