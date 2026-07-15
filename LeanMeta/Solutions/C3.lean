import Lean
import LeanMeta.C3_Syntax
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 3 (`Syntax`)

Compare with `Exercises/C3.lean`.  E4 extends the `arith` DSL declared in the
chapter, so we import it. -/

-- E1.  A macro that expands to an existing tactic.
macro "triv2" : tactic => `(tactic| trivial)
example : True := by triv2

-- E2.  A macro that splits a conjunction goal into its two parts.
macro "split_and" : tactic => `(tactic| refine ⟨?_, ?_⟩)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  split_and <;> assumption

-- E3.  Build a piece of syntax from another via an antiquotation.
#eval show CoreM Unit from do
  let t ← `(True)
  logInfo m!"{(← `($t ∧ $t)).raw}"     -- True ∧ True

-- E4.  Extend the `arith` DSL (Chapter 3) with subtraction, mirroring `+`.
syntax:65 arith:65 " - " arith:66 : arith
macro_rules
  | `([arith| $a:arith - $b:arith]) => `([arith| $a] - [arith| $b])
#eval [arith| 10 - 3]                  -- 7
#eval [arith| 2 * (3 + 4) - 5]         -- 9   (`*` binds tighter than `-`)
