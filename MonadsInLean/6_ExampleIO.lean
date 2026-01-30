import Lean
/-The most important monad in Lean is the IO monad. Since Lean is a funtional language,
no pure functions have the ability to interact with anything outside Lean, like with
the console, the state of the computer, etc. If we want lean to be able to do this stuff,
we need to cheat a little by writing special code that calls external c++ code to do
these interactions for us. The IO monad's job is to abstract away the cheating!

If α is a type, then we think of IO α as the type containing "programs" that return an α
but might need to call external programs along the way.

In the example below, since we are just printing, we don't actually need our program to
return anything, so we just return the default element of the type 'Unit'. We can run it
by typing

'lean --run MonadsInLean/ExampleIO.lean'

which looks for an 'IO -' named 'main', and runs the program it corresponds to.
-/


-- def main : IO Unit := do
--   IO.println "hello"

-- def main : IO Unit :=
-- bind (IO.println "hello") (fun _ =>
-- return Unit.unit)

/- The bind function takes an IO unit, "unwraps" it by calling an external program that
does the printing, and then passes the unwrapped form to the function that simply returns
the single element of Unit. Here's a more involved example: -/

def main : IO Unit := do
  IO.println "enter a line of text:"
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let inputAsList := input.toList
  let some fifth := inputAsList[4]? | IO.println "input not long enough"
  IO.println fifth

#eval main

/- here's the same thing but with bind used explicitly. -/

-- def main : IO Unit :=
-- bind (IO.println "enter a line of text") (fun _ =>
-- bind IO.getStdin (fun stdin =>
-- bind stdin.getLine (fun input =>
-- let inputAsList := input.toList
-- let optFifth := inputAsList[4]?
-- match optFifth with
--   | none => IO.println "input not long enough"
--   | some fifth => IO.println fifth)))


/- In this way, bind helps us chain operations together, all the while hiding the execution
through external programs! We simulate imperative programming within a functional setting! -/
