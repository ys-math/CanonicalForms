import CanonicalForms

/-!
# Axiom check

Runs `#print axioms` on every declaration of the `CanonicalForms` library: all
theorems, and also all definitions and structures. Compiler-generated auxiliary
declarations are skipped. The declarations are read from the environment, so
new theorems are checked without editing this file.

CI runs this file with `lake env lean scripts/CheckAxioms.lean` and fails if the
output mentions `sorryAx` or any axiom other than `propext`, `Classical.choice`
and `Quot.sound`.
-/

open Lean Elab Command

/-- Runs `#print axioms` on every non-auxiliary declaration of the modules whose
names start with `CanonicalForms`, in source order, and then reports how many
declarations were checked. -/
elab "#print_axioms_of_project" : command => do
  let env ← getEnv
  let mut decls : Array Name := #[]
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless (`CanonicalForms).isPrefixOf modName do continue
    let mut modDecls : Array (Nat × Name) := #[]
    for name in data.constNames, info in data.constants do
      -- Constructors and recursors are covered by `#print axioms` on their inductive type.
      if name.isInternalDetail || isAuxRecursor env name || isNoConfusion env name
          || info.isCtor || info matches .recInfo _ then
        continue
      let line := (← findDeclarationRanges? name).map (·.range.pos.line) |>.getD 0
      modDecls := modDecls.push (line, name)
    decls := decls ++ (modDecls.qsort (·.1 < ·.1)).map (·.2)
  if decls.isEmpty then
    throwError "no declarations found in the CanonicalForms library"
  for name in decls do
    elabCommand (← `(#print axioms $(mkIdent name)))
  logInfo m!"axiom check: {decls.size} declarations checked"

#print_axioms_of_project
