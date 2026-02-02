import Mathlib
import Lean

open Lean Meta Elab Tactic

example (x y : Nat) (h : x = y) : x = y := by assumption

#check Expr

syntax (name := my_assumption_syntax) "my_assumption" : tactic

#check Tactic

@[tactic my_assumption_syntax]
def my_assumption_elab : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- logInfo s!"{goalType}"
  goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      -- logInfo s!"{decl.type}"
      if ← isDefEq decl.type goalType then
        goal.assign decl.toExpr
        return
    throwError "Failed to find matching local declaration"
  return

theorem test : True := True.intro

example (x y : Nat) (h : x = y) : x = y := by
  my_assumption

-- import Lean.Elab.Tactic

-- sketch tactic: like sorry but allows a string comment describing the proof idea
elab "sketch" _msg:str : tactic => do
  let goal ← getMainGoal
  goal.admit
  replaceMainGoal []

example (x y : Nat) (_ : x = y) : y = x := by
  symm
  sketch "use the assumption"

set_option warn.sorry false in
/-- A noetherian ring (where by definition every ideal is finitely
generated) satisfies the ascending chain condition
-/
theorem isNoetherianRing_acc [CommRing R] [IsNoetherianRing R]
    (I : ℕ → Ideal R) (_h_chain : ∀ k, I k ≤ I (k + 1)) :
   ∃ n, ∀ m ≥ n, I n = I m := by
  let J : Ideal R := ⨆ n, I n
  have J_fg : J.FG := by sketch "J is Noetherian"
  obtain ⟨G : Finset R, hs : Ideal.span (↑G) = J⟩ := J_fg
  have h : ∃ n, ∀ g ∈ G, g ∈ I n := by
    sketch "∀ g ∈ G, ∃ n_g, g ∈ I n_g. Take n = max {n_g | g ∈ G}"
  obtain ⟨n, hn⟩ := h
  have h2 :  ∀ m ≥ n, I n = I m := by
    sketch "since every generator of J is in I n, J = I n \
      for each m ≥ n, since I n ≤ I m ≤ J, we have I n = I m"
  use n
