import Lean
import Mathlib.Tactic
import Lean.Elab.Tactic
open Lean

/- As we discussed, every proof assistant has the following:
1) A vernacular language used for defining objects and theorems
2) A formal langauge that everything in the vernacular langauge can be translated into.
    This formal language captures the base, unwrapped syntax of the vernacular language.


In lean, The vernacular language is the language of the Calculus of Inductive constructions.
This is the language that Lean uses - it provides support for types and functions and all the
other stuff we discussed. Every object definiable in Lean is a term of some type.

The formal language for Lean is implemented _within_ the vernacular language. The basis for this
is the type Expr
-/

-- Lean code → Syntax → Syntax  → Expr

#check Expr

-- #eval 5^1000
-- #eval 5^10000
-- #eval 5^100000

-- example : 5+10=15 := rfl
-- set_option exponentiation.threshold 1000
-- theorem foo : 5^1000 = 933263618503218878990089544723817169617091446371708024621714339795966910975775634454440327097881102359594989930324242624215487521354032394841520817203930756234410666138325150273995075985901831511100490796265113118240512514795933790805178271125415103810698378854426481119469814228660959222017662910442798456169448887147466528006328368452647429261829862165202793195289493607117850663668741065439805530718136320599844826041954101213229629869502194514609904214608668361244792952034826864617657926916047420065936389041737895822118365078045556628444273925387517127854796781556346403714877681766899855392069265439424008711973674701749862626690747296762535803929376233833981046927874558605253696441650390625 := rfl

-- #print foo

/- Just like many other types we've seen, this is an inductively defined type with a bunch
of constructors. The idea is that an object in the Expr type caputures the "abstract syntax".
Terms in Expr should be thought of as syntactical representations of arbitrary terms in Lean.
Here are some examples:
-/
open Expr

#check Nat.zero

#check Expr.const `Nat.zero []

#eval toExpr Nat.zero

inductive my_nat
| zero
| succ (n : my_nat)

#check my_nat.zero
#check (app (const `my_nat.succ []) (const `my_nat.zero []))


/-
When you write code in a lean file, multiple steps take place. The compiler sees a string
of Lean code, say "let a := 2", and the following process unfolds:

1) apply a relevant syntax rule ("let a := 2" ➤ Syntax)
    During the parsing step, Lean tries to match a string of Lean code to one of the declared
    syntax rules in order to turn that string into a "Syntax object". Syntax Objects are also
    a type defined in Lean, just like Expr above. Syntax rules are basically glorified regular
    expressions - when you write a Lean string that matches a certain syntax rule's regex, that
    rule will be used to handle subsequent steps.

    As a user, you can create new syntax rules whenever you want. In fact, this is how Lean allows
    you to use mathematical symbols and to create new notation. You can also use it to create
    commands, like `#check` and `#eval`. In the following example, we create a new syntax rule that
    establishes that the text `MyTerm` should be interpreted as a term. However, we still haven't
    explained to lean how to convert it into an Expr. As such it should be thought of as a
    meaningless term.
-/

syntax (name := myterm) "MyTerm" : term -- The name is used when defining the laborator later

def f := λ x => x + MyTerm

/-
2) apply all macros in a loop (Syntax ➤ Syntax)
    During the elaboration step, each macro simply turns the existing Syntax object into some
    new Syntax object. Then, the new Syntax is processed similarly (repeating steps 1 and 2),
    until there are no more macros to apply.

3) apply a single elab (Syntax ➤ Expr)
    Finally, it's time to infuse your syntax with meaning - Lean finds an elab that's matched to
    the appropriate syntax rule by the name argument (syntax rules, macros and elabs all have this
    argument, and they must match). The newfound elab returns a particular Expr object. This completes
    the elaboration step.

    As a user, you can write new elaborators whenever you want. Below, we write an elaborator for the
    syntax we defined above. The elaborator tells lean to interpret the term `MyTerm` as being the first
    element of the list mytermValues defined below.
-/
open Meta Elab Term

def mytermValues := ["hi", "there", "Lean", "user"]

@[term_elab myterm] -- This tag tells lean to use THIS elaborator when it encounters the syntax rule with name `myterm`
def myTerm1Impl : TermElab := fun stx type? => do
  mkAppM ``List.getD #[.const ``mytermValues [], mkNatLit 0, mkStrLit "fail"] -- `MetaM` code

def f := λ x => x ++ MyTerm

#eval f "text: "

/-The expression (Expr) is then given to the Lean kernel, whose job it is to "Type Check" the expression.
i.e. by analyzing the types of the smaller pieces the Expr is made of, it figures out what the type of
the whole expression is, and checks that it matches the type that the term was initially declared to have.
-/

def example_function : ℕ → ℕ := λ x => x + 6

/- In the above example, we use the fact that we already know that the plus function always returns
a Nat to verify that the lambda expression we created indeed has type ℕ → ℕ -/

/- The kernel operates only on objects of type Expr. So then what is metaprogramming? Meta programming
in lean can be thought of as the act of writing code that manipulates the above process - allowing you to
create new syntax and macros, new elaborators to convert new syntax in Expr objects, or code that can
directly create new Expr objects from scratch. All these operations work better within some context or
state, and so this code usually lives within one of the following monads: -/

open Tactic

#check MetaM
#check TermElabM
#check CoreM
#check TacticM


/- Each gives access to a different type of state. For example, CoreM gives access to the Environment
consisting of all declerations in the file and in imported files. MetaM gives access to metavariables
which are used while constructing proofs and writing tactics. You can learn more about what a monad is
from the other files in this repository-/

/- Here is an example of creating the syntax and elaborator for a new command that logs the text
`Hello World` to InfoView. You can imagine how useful this feature could be for debugging. -/

open Command

syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1 -- Hello World
