import mathlib.Tactic
/- Lean is a language that falls within the paradigm of functional programming. The first thing
one notices about Lean is that there is no run button! When I do the following:-/

#check Nat
#check Nat → Nat

/- Lean infoview displays the result on the right. Even when we use the command #eval, we don't
need to run anything -/

#eval 1 + 2
#check 5

/- However, consider the following: I will define my own local copy of the natural numbers.
I'll even define addition analogously-/

inductive my_nat
| zero
| succ (n : my_nat)

def my_nat.add : my_nat → my_nat → my_nat
| a, my_nat.zero => a
| a, (my_nat.succ b) => my_nat.succ (my_nat.add a b)

#check Nat.succ (Nat.succ Nat.zero)

#check my_nat.succ (my_nat.succ my_nat.zero)

/- #check still works, just as before. But when I try to use eval... -/

#eval 1 + 2

#reduce my_nat.add (my_nat.succ my_nat.zero) (my_nat.succ (my_nat.succ my_nat.zero))

/- Lean complains that it doesn't know how to represent this object. You might argue: why doesn't
it just print
  my_nat.succ (my_nat.succ (my_nat.succ my_nat.zero))
which is 3? The problem is,
  my_nat.add (my_nat.succ my_nat.zero) (my_nat.succ (my_nat.succ my_nat.zero))
is also 3 - by definition. By definition they are the same exact thing. How is Lean to know which
representation we like? In fact, we could also write 3 = 2 + 1. or 0 + 3. Or 3 + 0.  Or 3 + 0 + 0.
They are all definitionally the same.

For the internally defined naturals, Lean has an algorithm that computes the form we expect to see,
along with a proof that the computed form is the same as the thing we evaluated. This is why eval works
there, but not with our predefined naturals.
-/

example : 1 + 2 = 3 := by simp

/- In the above, that is what simp is doing - it is computing a proof that the LHS and RHS are
definitionally the same thing! This question of different representations of things comes up all
the time - whenever, in math, we want to prove an equality, we are essentially trying to demonstrate
that the left hand side and the right hand side are just two representations of the same thing.
This is why, in a language built for the express purpose of proving things, it is important that
the language respect the different representations of the same thing. -/

#check my_nat.add (my_nat.succ my_nat.zero) (my_nat.succ (my_nat.succ my_nat.zero))

/- When we type the above, lean is under no obligation to "run" something that would compute the
value of this. Instead, if simply checks that our syntax was correct, using the type signatures
to figure out that the types all check out, and leaves it at that.

It's like doing math on a whiteboard! Say I define a function
    f : ℝ → ℝ
        x ↦ x^2

If I then wrote down f(6), the whiteboard is under no obligation to grow a mouth and say "the
answer is 36!" Instead, we recognize f(6) as being definitionally the same thing as 36 - a
different representation. In this way, Lean is like a smart board - it's like doing math on a
whiteboard, but it also catches your mistakes:
-/

#check Nat.add "hi" "Dhruv"


/- This is the sense in which I say that lean is a language that does not fall under the
"imperative programming" paradigm, where we type commands that actually "do" something by
updating the computer state. Instead, if follows a contrasting philosophy - that of
"declarative programming," where all we are really doing is declaring definitions and writing
down statements, a lot like doing math on a whiteboard. The human is still performing all
the doing, and lean's job is simply to make sure we haven't made any mistakes. This is why lean
doesn't have a run button. It isn't really running anything at all - instead, it's just getting
C++, the language on top of which lean is built, to read the code and make sure there are no
syntax errors - a process called compilation. -/

/- To be completely accurate, lean follows the philosophy of functional programming - a kind of
declarative programming where functions are treated with as much value and importance as the
other data structures. The algorithmic steps for getting from the input to the output of a
function aren't really that important. All that matters is the correspondence between each
input and it's output. Functions viewed in this light are called "pure functions", because
they lack the ability to make any changes to the state of the computer. They simply take an
input, and BECOME the output when called. No side effects! The type signature tells you everyhting
the function can and cannot do.
-/

/- But if lean is purely a functional programming language, how does it do the following things? -/

#check Type

#eval 3 + 5

example (x y : ℝ) (h1 : x ^ 2 + y = 0) (h2 : y = 0) : x = 0 := by
  -- linear_combination (exp := 2) h1 - 1 * h2
  linarith

#check Prop


example (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2
