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
      let isMatch ← withoutModifyingState do
        let mut ok := true
        for i in [:goalArgs.size] do
          let gArg := goalArgs[i]!
          let dArg := declArgs[i]!
          if ← isDefEq gArg dArg then continue
          if (← isDefEq gArg β) && (← isDefEq dArg α) then continue
          ok := false
          break
        return ok
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

/-- Transport a structure: project each field from the source instance,
    transport it through the equivalence, and rebuild the structure. -/
def transportStructure (goal : MVarId) (equivExpr sourceInst α β : Expr)
    : TacticM Unit := do
  goal.withContext do
    let goalType ← goal.getType
    let goalHead := goalType.getAppFn
    let some goalName := goalHead.constName? | throwError "transport: goal is not a structure"
    let env ← getEnv
    if !isStructure env goalName then
      throwError "transport: {goalName} is not a structure"
    let fields := getStructureFieldsFlattened env goalName (includeSubobjectFields := false)
    let mut transportedFields : Array Expr := #[]
    let mut unsolved : List MVarId := []
    for field in fields do
      let sourceField ← mkProjection sourceInst field
      let sourceFieldType ← inferType sourceField
      let fieldGoalType := sourceFieldType.replace fun e =>
        if e == α then some β else none
      try
        let transported ← buildTransportTerm fieldGoalType equivExpr sourceField α β
        let _ ← inferType transported
        transportedFields := transportedFields.push transported
      catch _ =>
        let mvar ← mkFreshExprMVar fieldGoalType
        transportedFields := transportedFields.push mvar
        unsolved := unsolved ++ [mvar.mvarId!]
    let subgoals ← goal.constructor
    for (sg, field) in subgoals.zip transportedFields.toList do
      try
        sg.assign field
      catch _ =>
        unsolved := unsolved ++ [sg]
    replaceMainGoal unsolved

/-- Search the local context for a hypothesis from which `buildTransportTerm`
    can produce a proof of the goal. -/
def findSourceHyp (goal : MVarId) (equivExpr α β : Expr) : MetaM (Option FVarId) := do
  goal.withContext do
    let goalType ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      try
        let result ← withoutModifyingState do
          let r ← buildTransportTerm goalType equivExpr decl.toExpr α β
          let rType ← inferType r
          if ← isDefEq rType goalType then return some r
          return none
        if result.isSome then return some decl.fvarId
      catch _ => continue
    return none

/-- Transport a Prop by finding a source hypothesis and building the proof
    via `buildTransportTerm`. -/
def transportProp (goal : MVarId) (equivExpr α β : Expr) : TacticM Unit := do
  goal.withContext do
    let goalType ← goal.getType
    match ← findSourceHyp goal equivExpr α β with
    | some srcFVarId =>
      let sourceExpr := Expr.fvar srcFVarId
      let result ← buildTransportTerm goalType equivExpr sourceExpr α β
      goal.assign result
      replaceMainGoal []
    | none =>
      throwError "transport: could not find a source hypothesis to transport"

/-- Transport an inductive type: use `cases` on the source to extract fields,
    then `constructor` on the goal and transport each field. -/
def transportInductive (goal : MVarId) (equivExpr : Expr) (srcFVarId : FVarId)
    (α β : Expr) : TacticM Unit := do
  -- Case-split the source hypothesis to extract its fields
  let casesResult ← goal.cases srcFVarId
  let mut remaining : List MVarId := []
  for alt in casesResult do
    let sg := alt.mvarId
    -- After cases, the subgoal has the constructor fields in context.
    -- Use constructor on the goal, then try to transport each field.
    let subgoals ← sg.constructor
    for fieldGoal in subgoals do
      let closed ← fieldGoal.withContext do
        let fgType ← fieldGoal.getType
        -- Search the local context for a transportable source
        let lctx ← getLCtx
        for decl in lctx do
          if decl.isAuxDecl then continue
          try
            let result ← buildTransportTerm fgType equivExpr decl.toExpr α β
            let rType ← inferType result
            if ← isDefEq rType fgType then
              fieldGoal.assign result
              return true
          catch _ => continue
        return false
      if !closed then
        remaining := remaining ++ [fieldGoal]
  replaceMainGoal remaining

/-- Main entry point: dispatch to structure, inductive, or Prop transport. -/
def transportCore (goal : MVarId) (equivExpr α β : Expr) : TacticM Unit := do
  goal.withContext do
    let goalType ← goal.getType
    let env ← getEnv
    let isStruct := match goalType.getAppFn.constName? with
      | some name => isStructure env name
      | none => false
    -- Try structure transport first
    if isStruct then
      match ← findSourceInst goal α β with
      | some srcFVarId =>
        transportStructure goal equivExpr (.fvar srcFVarId) α β
        return
      | none => pure ()
    -- Try Prop transport (∀-quantified statements)
    if ← isProp goalType then
      -- First try direct buildTransportTerm
      match ← findSourceHyp goal equivExpr α β with
      | some srcFVarId =>
        let sourceExpr := Expr.fvar srcFVarId
        let result ← buildTransportTerm goalType equivExpr sourceExpr α β
        goal.assign result
        replaceMainGoal []
        return
      | none => pure ()
    -- Try direct term building (functions, plain types, etc.)
    match ← findSourceHyp goal equivExpr α β with
    | some srcFVarId =>
      let sourceExpr := Expr.fvar srcFVarId
      let result ← buildTransportTerm goalType equivExpr sourceExpr α β
      goal.assign result
      replaceMainGoal []
      return
    | none => pure ()
    -- Try inductive transport (e.g. Nonempty, Exists)
    match ← findSourceInst goal α β with
    | some srcFVarId =>
      transportInductive goal equivExpr srcFVarId α β
    | none =>
      throwError "transport: could not find a matching source for {goalType}"

end Transport

open Transport in
/-- `transport using e` transports a structure instance or theorem along an
equivalence `e : α ≃ β`.

- **Structure goals** (`S β`): finds a source instance `S α` in the context,
  projects each field, rewrites through `e`, and rebuilds the structure.
- **Prop goals** (`∀ x : β, P x`): finds a source hypothesis about `α` and
  builds a proof by converting `β`-quantified variables via `e.symm`.
- **Inductive goals** (`Nonempty β` etc.): case-splits the source and
  reconstructs via the constructor.

Any fields/goals that cannot be closed automatically are left as subgoals. -/
elab "transport" " using " e:term : tactic => do
  let goal ← getMainGoal
  let equivExpr ← Tactic.elabTerm e none
  let (α, β) ← getEquivTypes equivExpr
  transportCore goal equivExpr α β

-- ============================================================
-- Examples
-- ============================================================

-- Example 1: Transport a structure
structure MyMul (α : Type*) where
  mul : α → α → α

example {α β : Type*} (inst : MyMul α) (e : α ≃ β) : MyMul β := by
  transport using e

-- Example 2: Transport a universally quantified proposition
example {α β : Type*} (e : α ≃ β) (P : α → Prop) (h : ∀ x : α, P x)
    : ∀ x : β, P (e.symm x) := by
  transport using e

-- Example 3: Transport a binary predicate
example {α β : Type*} (e : α ≃ β) (R : α → α → Prop) (h : ∀ x y : α, R x y)
    : ∀ x y : β, R (e.symm x) (e.symm y) := by
  transport using e

-- Example 4: Transport Nonempty
example {α β : Type*} (h : Nonempty α) (e : α ≃ β) : Nonempty β := by
  transport using e

-- Example 5: Transport a proposition about a function
example {α β : Type*} (e : α ≃ β) (f : α → α) (h : ∀ x : α, f x = x)
    : ∀ x : β, f (e.symm x) = e.symm x := by
  transport using e

-- Example 6: Transport a function α → α to β → β
example {α β : Type*} (f : α → α) (e : α ≃ β) : β → β := by
  transport using e

-- Example 7: Transport a binary operation α → α → α to β → β → β
example {α β : Type*} (op : α → α → α) (e : α ≃ β) : β → β → β := by
  transport using e

-- Example 8: Transport an element α to β
example {α β : Type*} (a : α) (e : α ≃ β) : β := by
  transport using e
