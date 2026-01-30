import Lean

open Lean Meta Elab Tactic


def myAssumptionCore (goal : MVarId) : MetaM Unit :=
  goal.withContext do
    let goalType ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      if ← isDefEq decl.type goalType then
        goal.assign decl.toExpr
        return
    throwError "my_assumption failed: no matching hypothesis found"

syntax (name := my_assumption_syntax) "my_assumption" : tactic

@[tactic my_assumption_syntax]
def elabMyAssumption : Tactic := fun _stx => do
  let goal ← getMainGoal
  myAssumptionCore goal

example (x y : Nat) (h : x = y) : x = y := by
  my_assumption



elab "my_assumption'" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      if ← isDefEq decl.type goalType then
        goal.assign decl.toExpr
        return
    throwError "my_assumption failed: no matching hypothesis found"


example (x y : Nat) (h : x = y) : x = y := by
  my_assumption'
