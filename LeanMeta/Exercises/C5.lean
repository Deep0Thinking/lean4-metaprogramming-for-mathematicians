import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 5  (`TacticM`)

These drill writing real tactics: the `MetaM`-core / `TacticM`-shell split, and the
`MVarId` primitives (`constructor`, `apply`, `clear`) that assign the goal.  E1 to
E5 re-implement tactics you use daily; E6 is a stretch.

Write each answer below its prompt, run it, then compare with `Solutions/C5.lean`.
This file is all comments as shipped, so it builds; fill it in as you go. -/

-- E1.  Write `my_trivial` as a MACRO: try `rfl`, else `assumption`.  (One line.)

-- E2.  Write `count_hyps`, which logs how many (non-implementation-detail)
--      hypotheses the main goal has.  (Reuse the §2 pattern; annotate the counter.)

-- E3.  Write `my_constructor` in `MetaM`, using `MVarId.constructor`.
--      Test: `example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by my_constructor <;> assumption`.

-- E4.  Write `my_left` and `my_right` for `∨` goals, using `MVarId.apply` and
--      `mkConstWithFreshMVarLevels ``Or.inl` / `` ``Or.inr ``.  (Remember the `do`.)

-- E5.  Write `my_exfalso`: turn any goal into `False`.  Hint: `apply` `False.elim`.

-- E6 (bonus).  Write `my_clear h` that drops the hypothesis named `h`.  Hint: resolve
--      the identifier with `(← getLCtx).findFromUserName? h.getId`, then `MVarId.clear`.
