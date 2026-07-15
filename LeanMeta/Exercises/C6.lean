import Lean
import LeanMeta.C6_Capstone
open Lean Meta Elab Tactic MyTauto
set_option linter.unusedVariables false

/-! # Exercises for Chapter 6  (capstone `mytauto`)

Worked answers: `Solutions/C6.lean`.  These extend `MyTauto.core`; you may reuse
its helpers `assumptionCore` and `findDestructible?`, and the `succeeds` /
`orElseRestore` combinators from Chapter 5 (all in scope via the imports above). -/

-- ✎6  (the real one).  Make the prover CLASSICAL, so that `p ∨ ¬p` goes through.
--     Hint: `Classical.byContradiction : ¬¬a → a`.  As a last resort, when nothing
--     intuitionistic makes progress on a `Prop` goal, `apply` it and recurse.
--     ⚑ You MUST thread a `Bool` "have I already used byContradiction on this
--       branch?" through the search and NEVER reset it to `false` on the sub-goals
--       it creates; otherwise the search negates the goal forever.  Work out why.

-- ✎7.  Let the prover prove `∃` goals whose witness is forced, e.g.
--      `(h : P 3) : ∃ x, P x`.  Hint: `apply Exists.intro` with
--      `(cfg := { newGoals := .nonDependentOnly })` leaves the witness as a
--      metavariable; solving the `P ?w` subgoal by assumption unifies it.

-- ✎8  (reading).  Open `Lean/Meta/Tactic/Assumption.lean` in your toolchain source
--      and compare it with our `MyTauto.assumptionCore`.  What does the real one do
--      that ours does not?  (Look at how it handles metavariables and transparency.)
