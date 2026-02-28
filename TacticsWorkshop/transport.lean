import Mathlib
import Lean

/-!
# Transport tactic

A minimal analogue of the Lean 3 `transport` tactic.
Given a goal of the form `S β` (a structure/typeclass applied to `β`),
and a hypothesis providing `S α` together with an equivalence `e : α ≃ β`,
the tactic decomposes the structure and attempts to fill each field
by composing through the equivalence.

## Usage

```
transport using e
```

where `e : α ≃ β` is an equivalence in the local context.
The tactic will search the context for a matching source instance
and try to close all field goals automatically.
-/

open Lean Meta Elab Tactic

namespace Transport

/-- Given an expression `e : α ≃ β`, extract the types `α` and `β`. -/
def getEquivTypes (e : Expr) : MetaM (Expr × Expr) := do
  let eType ← inferType e
  let eType ← whnf eType
  match eType.getAppFnArgs with
  | (``Equiv, #[α, β]) => return (α, β)
  | _ => throwError "transport: expected an Equiv, got {eType}"

/-- Search the local context for a hypothesis whose type is an application
    of the same head constant as the goal, but with `α` in place of `β`. -/
def findSourceInst (goal : MVarId) (α β : Expr) : MetaM (Option FVarId) := do
  goal.withContext do
    let goalType ← goal.getType
    let goalHead := goalType.getAppFn
    let some goalName := goalHead.constName? | return none
    let goalArgs := goalType.getAppArgs
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      let declType ← whnf decl.type
      let declHead := declType.getAppFn
      let some declName := declHead.constName? | continue
      if declName != goalName then continue
      let declArgs := declType.getAppArgs
      if declArgs.size != goalArgs.size then continue
      let mut isMatch := true
      for i in [:goalArgs.size] do
        let gArg := goalArgs[i]!
        let dArg := declArgs[i]!
        if ← isDefEq gArg dArg then continue
        if (← isDefEq gArg β) && (← isDefEq dArg α) then continue
        isMatch := false
        break
      if isMatch then
        return some decl.fvarId
    return none

/-- Recursively build a transport term for a given type.

    For `β → T`, produce a lambda that converts the argument via `e.symm`
    and recurses on the codomain.
    At a base type `β`, apply `e` to convert from `α`.
    At other base types, return the source expression unchanged. -/
partial def buildTransportTerm (goalType : Expr) (equivExpr sourceExpr α β : Expr)
    : MetaM Expr := do
  let goalType ← whnf goalType
  match goalType with
  | .forallE name dom body bi =>
    withLocalDecl name bi dom fun arg => do
      let convertedArg ←
        if ← isDefEq dom β then
          mkAppM ``Equiv.invFun #[equivExpr, arg]
        else
          pure arg
      let sourceApplied := mkApp sourceExpr convertedArg
      let bodyType := body.instantiate1 arg
      let result ← buildTransportTerm bodyType equivExpr sourceApplied α β
      mkLambdaFVars #[arg] result
  | _ =>
    if ← isDefEq goalType β then
      mkAppM ``Equiv.toFun #[equivExpr, sourceExpr]
    else
      pure sourceExpr

/-- The main transport logic: project each field from the source instance,
    transport it through the equivalence, and rebuild the structure. -/
def transportCore (goal : MVarId) (equivExpr sourceInst α β : Expr)
    : TacticM Unit := do
  goal.withContext do
    let goalType ← goal.getType
    let goalHead := goalType.getAppFn
    let some goalName := goalHead.constName? | throwError "transport: goal is not a structure"
    let env ← getEnv
    if !isStructure env goalName then
      throwError "transport: {goalName} is not a structure"
    let fields := getStructureFieldsFlattened env goalName (includeSubobjectFields := false)
    -- Build each transported field
    let mut transportedFields : Array Expr := #[]
    let mut unsolved : List MVarId := []
    for field in fields do
      let sourceField ← mkProjection sourceInst field
      let sourceFieldType ← inferType sourceField
      let fieldGoalType := sourceFieldType.replace fun e =>
        if e == α then some β else none
      -- Try to build the transported term
      try
        let transported ← buildTransportTerm fieldGoalType equivExpr sourceField α β
        -- Type-check the result
        let _ ← inferType transported
        transportedFields := transportedFields.push transported
      catch _ =>
        -- If automatic transport fails, create a metavar for the user to fill
        let mvar ← mkFreshExprMVar fieldGoalType
        transportedFields := transportedFields.push mvar
        unsolved := unsolved ++ [mvar.mvarId!]
    -- Use constructor to decompose, then assign each field
    let subgoals ← goal.constructor
    for (sg, field) in subgoals.zip transportedFields.toList do
      try
        sg.assign field
      catch _ =>
        unsolved := unsolved ++ [sg]
    replaceMainGoal unsolved

end Transport

open Transport in
/-- `transport using e` transports a structure instance along an equivalence `e : α ≃ β`.

It searches the local context for a matching source instance on `α` and decomposes
the goal structure, attempting to fill each field by composing through `e`.

Any fields that cannot be closed automatically are left as subgoals. -/
elab "transport" " using " e:term : tactic => do
  let goal ← getMainGoal
  let equivExpr ← Tactic.elabTerm e none
  let (α, β) ← getEquivTypes equivExpr
  match ← findSourceInst goal α β with
  | some srcFVarId =>
    let sourceInst := .fvar srcFVarId
    transportCore goal equivExpr sourceInst α β
  | none =>
    throwError "transport: could not find a source instance on the type {α}"

-- ============================================================
-- Examples
-- ============================================================

-- Example 1: A simple custom structure with one operation
structure MyMul (α : Type*) where
  mul : α → α → α

example {α β : Type*} (inst : MyMul α) (e : α ≃ β) : MyMul β := by
  transport using e
