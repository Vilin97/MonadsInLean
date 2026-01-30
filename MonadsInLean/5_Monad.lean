import Mathlib.Tactic
/- This file borrows from "Functional Programming in Lean":
https://lean-lang.org/functional_programming_in_lean/monads.html -/

/- Lean has monads too! Here's an example - the option monad. It has all three things:
1) The wrapper type: Option
2) The wrapper function: Option.some
3) The run function: Option.bind
We can command/ctrl click on the following to see their definitions
-/

#check Option
#check Option.some
#check Option.bind

/- Lean has a type class for monads which we can use to tell lean when a type we crated is a monad-/

#check Monad

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

/- But to truly be a monad, we need more than just a pure and a bind. We need these functions to satisfy
certain properties. For example, if A and B are types and M is a monad, then given f : A → M B, we need
    bind (pure a) f = f a
for any a : A. Or, given f and g : A → M B and x : M A, we need
    bind (bind x f) g = bind x (λ a => bind (f a) g)

These extra properties are wrapped into the type class LawfulMonad
-/

#check LawfulMonad


/- The Option monad abstracts away the possibility of missing values. When running a function,
 it checks whether the value is missing, and only returns something if the value is not missing.
 If the input element was empty, it aborts operations by simply returning none. Here's some
 contrived code to illustrate this. -/

def first (xs : List α) : Option α :=
xs[0]?

/- Because the list may or may not have a first entry (it might be the empty list), we need to
include the '?', which makes it return 'none' in case the list doesn't have a first entry. -/

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)

/- the functions above have all the checks to make sure at every stage we aren't putting 'none'
into a function. However, using the fact that Option is a monad, we can write this much more
efficiently. Take the time to trace through these definitions to make sure you understand this. -/

def firstThirdm (xs : List α) : Option (α × α) :=
  bind xs[0]? (fun fst =>
    bind xs[2]? (fun thrd =>
      some (fst, thrd)))


/- lean actually includes notation for bind: the >>= operator, which makes this even shorter
to write.
'bind x f' is the same thing as 'x >>= f', where 'x : Option α' and 'f : α -> Option β'
This notation reminds us that the bind operator is like feeding a monadic term to a function
-/

def firstThirdM (xs : List α) : Option (α × α) :=
  xs[0]? >>= fun fst =>
  xs[2]? >>= fun thrd =>
  some (fst, thrd)

#eval firstThirdM ["first", "second", "third"]

/- The ultimate goal of monads in a functional language like lean is to simulate imperative
programming. To do that, Lean provides more syntax - so called 'do' notation. Using it, we can
re write the above as: -/

def firstThirdMd (xs : List α) : Option (α × α) := do
  let fst ← xs[0]?
  let thrd ← xs[2]?
  some (fst, thrd)

/- The above is just syntax, it is definitionally equivalent to using bind the regular way. But
the benefit of writing things this way is that it feels like we are assigning the output from
'xs[0]?' to the variable 'fst'. Since each "assignment" might fail due to missing values, this
really is like imperative programming! -/
