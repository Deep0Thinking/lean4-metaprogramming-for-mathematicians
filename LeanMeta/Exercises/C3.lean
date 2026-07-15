import Lean
import LeanMeta.C3_Syntax
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 3  (`Syntax`)

These drill the front end: writing macros (`Syntax → Syntax`), building syntax
with quotations, and extending a syntactic category with your own notation.

Write each answer below its prompt, run it, then compare with `Solutions/C3.lean`.
This file is all comments as shipped, so it builds; fill it in as you go. -/

-- E1.  Write a macro `triv2` that expands to `trivial`.  Prove `example : True := by triv2`.

-- E2.  Write a macro `split_and` that turns an `∧` goal into its two parts
--      (hint: `` `(tactic| refine ⟨?_, ?_⟩) ``).  Test with `split_and <;> assumption`.

-- E3.  In `CoreM`, let `t ← `(True)`, then build and `logInfo` the raw syntax of
--      `$t ∧ $t` (expect `True ∧ True`).

-- E4.  Extend the `arith` DSL from this chapter with subtraction `-`, mirroring the
--      `+` rule (same precedence 65).  Then `#eval [arith| 10 - 3]` (expect 7) and
--      `#eval [arith| 2 * (3 + 4) - 5]` (expect 9).
