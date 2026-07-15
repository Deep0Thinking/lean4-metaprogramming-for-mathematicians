import Lean
import LeanMeta.C6_Capstone
open Lean Meta Elab Tactic MyTauto
set_option linter.unusedVariables false

/-! # Exercises for Chapter 6  (capstone `mytauto`)

The hardest, most rewarding set: you extend the prover itself.  You now own a
real, sound tactic (§6.1); these exercises push its reach.  You will teach it to
name existential witnesses (✎7), turn it classical so `p ∨ ¬p` goes through (✎6),
and then read Lean's own `assumption` to see what a production tactic does that
ours does not (✎8).

Ordered by build effort, easy to hard, not by number.  A warm-up first to fix in
your mind exactly where the shipped intuitionistic prover stops.

HOW EACH EXERCISE WORKS.  Write your answer in the blank space under the exercise;
every CHECK is a commented `example`/`#check` you activate by deleting its leading
`-- `.  A green check is your proof you got it.  The file ships all-comments, so
`lake build` stays green until you start filling it in.

WHAT YOU MAY REUSE (all in scope through the imports above): the helpers
`assumptionCore` and `findDestructible?` from `MyTauto`, and the `succeeds` /
`orElseRestore` backtracking combinators from Chapter 5.  The natural move for ✎7
and ✎6 is to copy `MyTauto.core`, rename it `coreC`, front it with a `mytautoC`
tactic, and grow that one function.

Worked answers, both extensions folded into a single `coreC`: `Solutions/C6.lean`.
-/


-- ============================================================================
-- Warm-up W.  Map the border of the intuitionistic prover.
-- ============================================================================
-- MOTIVATION: before you extend a tool you must feel exactly where it stops;
--   §6.3 warned that `mytauto` is sound but not complete, and that the wall has
--   two very different bricks in it.
--
-- TASK: for each of the four goals below, PREDICT "closes" or "fails" under the
--   shipped intuitionistic `mytauto`, and say WHY, before you uncomment anything.
--   Two close; two fail, and they fail for different reasons: one is simply not
--   an intuitionistic truth, the other IS an intuitionistic tautology that
--   `mytauto` still cannot reach.  Which is which?
--
-- HINT: recall the move `mytauto` does NOT have (§6.3, "no implication-left
--   rule").  Excluded middle is not the only thing beyond it.
--
-- CHECK (uncomment the two you predicted "closes"; both compile):
-- example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by mytauto
-- example (p : Prop) : p → ¬¬p := by mytauto
--
-- CHECK (these two are the "fails"; leave them commented in a green build, then
--   uncomment one at a time to read the error and confirm your reason.  The first
--   is not intuitionistically valid; the second is, yet `mytauto` still misses it):
-- example (p : Prop) : p ∨ ¬p := by mytauto
-- example (p q : Prop) : ((p → q) → p) → ¬¬p := by mytauto


-- ============================================================================
-- ✎7.  Teach the prover to prove a forced existential.
-- ============================================================================
-- MOTIVATION: `∃ x, P x` needs a witness, but sometimes the context forces
--   exactly one; this is where a metavariable stops being scary and starts
--   doing your work, unification fills the witness in for you.
--
-- TASK: copy `MyTauto.core` into your own `coreC` and expose it as a `mytautoC`
--   tactic, then add an `Exists` case to the target rules so that a goal like
--   `(h : P 3) : ∃ x, P x` closes.  You supply NO witness by hand: leave it a
--   hole and let the later assumption step pin it down.
--
-- HINT: `apply Exists.intro` with `(cfg := { newGoals := .nonDependentOnly })`
--   keeps the witness OUT of the returned goal list, so it stays a metavariable;
--   solving the remaining `P ?w` subgoal by assumption unifies `?w := 3`.
--
--   (write coreC + the mytautoC tactic here, then:)
--
-- CHECK (uncomment; expected: closes):
-- example (P : Nat → Prop) (h : P 3) : ∃ x, P x := by mytautoC


-- ============================================================================
-- ✎6.  Make the prover CLASSICAL.
-- ============================================================================
-- MOTIVATION: the payoff move.  One last-resort rule turns your intuitionistic
--   searcher into a classical one, and the subtlety in wiring it is the whole
--   lesson about propagating state through a recursion.
--
-- TASK: add a final fallback to the SAME `coreC`: when no intuitionistic move
--   makes progress on a `Prop` goal, prove `a` by refuting `¬a`.  Guard it with a
--   `usedContra : Bool` you thread through every recursive call so it fires at
--   most once per branch.
--
-- HINT: `Classical.byContradiction : ¬¬a → a`; `apply` it and recurse with the
--   flag set true.  Gate the fallback on `← isProp target`.
--   ⚑ THE TRAP: you must PROPAGATE `usedContra` unchanged into the subgoals a
--     move creates, NEVER reset it to `false`.  Reset it and `byContradiction`
--     re-fires on the negated goal it just made, and the search negates forever.
--     Work out on paper why the reset loops before you trust the flag.
--
--   (extend coreC with the classical fallback here, then:)
--
-- CHECK, regressions first (uncomment; expected: all still close):
-- example (p q r : Prop) : p ∧ q → q ∧ p := by mytautoC
-- example (p q r : Prop) : (p → q) → (q → r) → p → r := by mytautoC
--
-- CHECK, the new classical power (uncomment; expected: all close, whereas the
--   intuitionistic `mytauto` failed every one):
-- example (p : Prop) : p ∨ ¬p := by mytautoC
-- example (p : Prop) : ¬¬p → p := by mytautoC
-- example (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by mytautoC
-- example (p q : Prop) : (p → q) → ¬p ∨ q := by mytautoC


-- ============================================================================
-- ✎8  (reading stretch, no tactic to write).  Read the real `assumption`.
-- ============================================================================
-- MOTIVATION: your `assumptionCore` (§6, the base case) is a teaching miniature
--   of a tactic that ships in every Lean.  Reading the production version is how
--   you calibrate what "the same idea, hardened" looks like.
--
-- TASK: open `Lean/Meta/Tactic/Assumption.lean` in your toolchain source and
--   find `Lean.MVarId.assumptionCore` and its helper `findLocalDeclWithType?`.
--   Compare with `MyTauto.assumptionCore`.  Name two concrete differences: what
--   guard does the real one run before it even looks for a hypothesis (think:
--   already-solved goals, i.e. metavariables), and in what ORDER does it scan the
--   local context versus ours?  How does that guard change behavior?
--
-- HINT: the guard is one method call on the goal, named for the very thing it
--   refuses to do; the scan direction hides in the helper's `...RevM?`.
--
-- CHECK (uncomment; both names must resolve, confirming you found the real
--   declarations.  Expected #check output:
--     MVarId.assumptionCore : MVarId → MetaM Bool
--     findLocalDeclWithType? : Expr → MetaM (Option FVarId) ):
-- #check @Lean.MVarId.assumptionCore
-- #check @Lean.Meta.findLocalDeclWithType?
