import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 2  (`MetaM`)

Worked answers: `Solutions/C2.lean`. -/

-- E1.  Write `goalHead? : MVarId → MetaM Name` returning the head symbol of the
--      goal's target (hint: `(← goal.getType).getAppFnArgs.1`).

-- E2.  Write `countHypsMeta : MVarId → MetaM Nat` counting the real
--      (non-implementation-detail) hypotheses.  Remember `goal.withContext` and
--      the `: Nat` annotation on the `let mut` counter (§0.4(h), Trap #2).

-- E3.  Confirm Trap #8 yourself: make a fresh `Nat` metavariable, `assign` it `7`,
--      then `logInfo` both `m.isMVar` (still `true`!) and `← instantiateMVars m`
--      (now `7`).

-- E4.  Write a tactic `show_target` that logs the current goal's target type.
--      Try it on `example (n : Nat) : n = n := by show_target; rfl`.
