import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 4  (Elaboration)

Worked answers: `Solutions/C4.lean`. -/

-- E1.  Write a term elaborator `double%` so that `double% n` elaborates directly to
--      the literal `2 * n` (hint: `elab "double% " n:num : term => return mkNatLit ...`).
--      Check `#eval double% 21` (42) and `example : double% 3 = 6 := rfl`.

-- E2.  Write `len% [a, b, c]` (like `sum%` in §4, but returning the LENGTH of the
--      list).  Hint: the arguments array is `xs.getElems`; its `.size` is the answer.

-- E3.  Write a command `#isProp t` that elaborates `t` and reports whether it is a
--      proposition (hint: `Command.liftTermElabM`, then `Meta.isProp`).  Try it on
--      `True` (true) and `Nat` (false).
