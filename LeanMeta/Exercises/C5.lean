import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 5  (`TacticM`: writing real tactics)

The payoff set: you reimplement, from scratch, tactics you run every day.  Each one
drills the chapter's central move (§5.1): put the logic in a `MetaM` core on one
`MVarId`, keep only goal-list bookkeeping in the `TacticM` shell, and bridge the two
with the `liftMeta*` family.

The set runs easy to hard: two warm-ups (a macro, then a manager-level head count),
three `liftMetaTactic` cores that assign the goal, and one stretch that takes an
identifier argument.  Every exercise ends in a CHECK: write your answer, uncomment
the check, and the stated result tells you whether you got it right.  Peek at
`Solutions/C5.lean` only after your check passes.

HOW TO WORK THESE.  Write each answer below its prompt (in the answer space), run it
in the Infoview, then uncomment the check.  As shipped this file is ALL COMMENTS, so
`lake build` stays green; your answer and the check both start life commented, so
uncomment as you go. -/


-- ============================================================================
-- E1 (warm-up).  `my_trivial` as a macro
-- ============================================================================
-- MOTIVATION: the smallest thing that deserves to be called a tactic, pure Ch3
--   syntax with no `Expr` in sight; it shows that composing existing tactics is
--   often the whole job (§5.6).
-- TASK: write `my_trivial` as a MACRO that first tries `rfl`, and on failure falls
--   back to `assumption`.  One line.
-- HINT: the `first | t₁ | t₂` combinator (§5.8) runs the first branch that succeeds.
--
-- (write your answer here)
--
-- CHECK (write your macro, then uncomment): BOTH branches must fire.
--   example (p : Prop) (hp : p) : p := by my_trivial      -- the `assumption` branch
--   example : 2 + 2 = 4 := by my_trivial                  -- the `rfl` branch


-- ============================================================================
-- E2 (warm-up).  `count_hyps`
-- ============================================================================
-- MOTIVATION: your first look at the manager layer, reading a goal's local context
--   the way `my_assumption` does (§5.3), but only to COUNT, not to search.
-- TASK: write `count_hyps` (an `elab ... : tactic`) that logs how many real
--   hypotheses the main goal has, skipping implementation-detail locals.
-- HINT: enter `goal.withContext do`, then loop `for ldecl in ← getLCtx`, guarding on
--   `ldecl.isImplementationDetail`.  Annotate the counter `: Nat` (§0.4(h), Trap #2).
--
-- (write your answer here)
--
-- CHECK (uncomment): expect the message "3 hypotheses".
--   example (a b : Nat) (h : a = b) : True := by
--     count_hyps                      -- 3 hypotheses  (a, b, h)
--     trivial


-- ============================================================================
-- E3.  `my_constructor`
-- ============================================================================
-- MOTIVATION: your first genuine core; one `MetaM` primitive splits a conjunction
--   (indeed any single-constructor goal) into its fields, and the shell is one line.
-- TASK: write `my_constructor` with `liftMetaTactic` and `MVarId.constructor`.
-- HINT: `MVarId.constructor : MVarId → MetaM (List MVarId)` already returns the
--   subgoal list, exactly the shape `liftMetaTactic` wants, so no extra `do` needed.
--
-- (write your answer here)
--
-- CHECK (uncomment): the two subgoals fall to `<;> assumption`.
--   example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by my_constructor <;> assumption


-- ============================================================================
-- E4.  `my_left` and `my_right`
-- ============================================================================
-- MOTIVATION: choosing a disjunct is just `apply`ing a constructor; this is your
--   first hand-built `apply` (§5.4) and your first brush with universe levels.
-- TASK: write `my_left` and `my_right` for `∨` goals via `MVarId.apply`.
-- HINT: apply `mkConstWithFreshMVarLevels ``Or.inl` (resp. `` ``Or.inr ``).  The
--   fresh-levels wrapper matters: a raw `Or.inl` carries stuck universe metavariables.
--   You need the `do` here, so the `(← …)` sits inside a do-block (Solutions notes why).
--
-- (write your answer here)
--
-- CHECK (uncomment): one line per side, so BOTH tactics are exercised.
--   example (p q : Prop) (hq : q) : p ∨ q := by my_right; assumption
--   example (p q : Prop) (hp : p) : p ∨ q := by my_left;  assumption


-- ============================================================================
-- E5.  `my_exfalso`
-- ============================================================================
-- MOTIVATION: the same `apply` move, now used to REPLACE the goal rather than split
--   it; `apply`ing `False.elim` turns any goal into the single subgoal `False`.
-- TASK: write `my_exfalso`, which turns any goal into `False`.
-- HINT: `apply` the constant `mkConstWithFreshMVarLevels ``False.elim`
--   (recall `False.elim : False → C`, so its conclusion `C` unifies with any goal).
--
-- (write your answer here)
--
-- CHECK (uncomment): a `False` in context then closes the goal.
--   example (p : Prop) (h : False) : p := by my_exfalso; assumption


-- ============================================================================
-- E6 (stretch).  `my_clear h`
-- ============================================================================
-- MOTIVATION: your first tactic that takes an ARGUMENT and edits the context rather
--   than the goal; you resolve a user identifier to an `FVarId`, the same
--   "elaborate up in `TacticM`, do the work in `MetaM`" split as `my_apply` (§5.4).
-- TASK: write `my_clear h` (an `elab ... h:ident : tactic`) that drops the
--   hypothesis named `h` from the main goal.
-- HINT: inside `goal.withContext`, look the name up with
--   `(← getLCtx).findFromUserName? h.getId`, take its `.fvarId`, then finish with
--   `replaceMainGoal [← goal.clear fvarId]`.
--
-- (write your answer here)
--
-- CHECK (uncomment): `hjunk` is dropped, and `hp` still proves the goal.
--   example (p : Prop) (hp : p) (hjunk : p) : p := by
--     my_clear hjunk
--     exact hp
