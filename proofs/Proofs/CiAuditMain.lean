import Proofs.CiAudit

/-! `ciaudit OUT`: write the Mathlib-side audit rows for `ciscore --external-proofs OUT`. -/

def main (args : List String) : IO Unit :=
  IO.FS.writeFile (args.headD "../ci-out/external-proofs.txt") ("\n".intercalate Proofs.CiAudit.rows ++ "\n")
