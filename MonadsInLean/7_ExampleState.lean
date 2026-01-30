import Lean
/- Here's another example of a monad: the State Monad. It adds a read write memory state
to a type, allowing you to write programs with access to whatever is stored in memory.

`StateM S A` is definitionally equal to `S → S × A`. Functions that can take in a state
of type S and return a new state, along with a value computed in A.
-/

open Lean
#check StateM

def NatWithLogs : Type := StateM (List Format) Nat

#reduce StateM (List Format) Nat

def add_one (n : Nat) : NatWithLogs := do
  let s ← get
  set (s.cons f!"added 1 to {n} to get {n + 1}")
  return n + 1

def square (n : Nat) : NatWithLogs := do
  modify (λ s => s.cons f!"squared {n} to get {n^2}")
  return n * n

def my_program (n : Nat): NatWithLogs := do
  let n ← add_one n
  let n ← square n

  return n

#eval my_program 5 []

/- A similar monad is the Reader Monad, which adds a read only memory.

Sometimes, we want a range of functionalities added. Maybe we wish to be able to talk to
the command line and also store information in memory. We can just compose monads to
achieve this
-/

#check StateM (List Format) (IO Nat)
