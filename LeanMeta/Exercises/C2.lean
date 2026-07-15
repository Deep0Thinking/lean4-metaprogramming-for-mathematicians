import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 2  (`MetaM`)

The chapter rests on one identification: a goal IS a metavariable (§2.3), a
well labelled hole carrying the target it must become (§2.2) and the local
context you may use to fill it (§2.1).  These exercises make that concrete:
you will read a goal's target and hypotheses from inside its context, and you
will feel Trap #8 bite, that an assigned mvar's raw `Expr` is still a hole
until you `instantiateMVars` (§2.2).

How to work: write each answer in the blank space under its prompt, then
uncomment that exercise's CHECK and run the file.  Each CHECK states the exact
result to expect, so you KNOW when you are done; compare with `Solutions/C2.lean`
only after.  Shipped, this file is all comments, so `lake build` stays green;
you fill it in as you go.  Ordered easy to hard: E1, E3 warm-ups, then E4, E2,
then an optional Stretch.
-/

-- ============================================================================
-- E1  (warm-up).  goalHead? : MVarId -> MetaM Name
-- ----------------------------------------------------------------------------
-- MOTIVATION: every dispatch tactic (`apply`, `rw`, `simp`) first asks "what
--   shape is this goal?".  The cheapest answer is the target's head symbol.
--
-- TASK: write `goalHead?` returning the head symbol of the goal's target, e.g.
--   `Eq` for `a = b`, `And` for `p /\ q`, `True` for `True`.
--
-- HINT: read the target with `goal.getType`, then take the head with
--   `Expr.getAppFnArgs` (§1.4); you want the first component of its pair.
--
--   (write goalHead? here)
--
-- CHECK (uncomment; expect the info message  head: Eq):
-- #eval show MetaM Unit from do
--   let goalType ← mkAppM ``Eq #[mkNatLit 1, mkNatLit 1]
--   let g ← mkFreshExprMVar (some goalType)
--   logInfo m!"head: {← goalHead? g.mvarId!}"


-- ============================================================================
-- E2  (core).  countHypsMeta : MVarId -> MetaM Nat
-- ----------------------------------------------------------------------------
-- MOTIVATION: reading the local context is half of what any tactic does, and
--   doing it correctly forces the two habits this chapter is about: entering
--   the goal's context, and skipping the machine-generated entries.
--
-- TASK: count the real hypotheses of a goal, i.e. the local declarations that
--   are NOT implementation details.
--
-- HINT: you must be inside the goal's world to read its context, so wrap the
--   body in `goal.withContext` (Trap #7); iterate `← getLCtx` and skip any
--   `ldecl.isImplementationDetail`.  Annotate the counter `let mut n : Nat := 0`
--   or the numeral defaults to the wrong type (§0.4(h), Trap #2).
--
--   (write countHypsMeta here)
--
-- CHECK (uncomment; expect the info message  count: 2):
-- #eval show MetaM Unit from do
--   withLocalDeclD `x (.const ``Nat []) fun _ => do
--   withLocalDeclD `y (.const ``Nat []) fun _ => do
--     let g ← mkFreshExprMVar (some (.const ``Nat []))
--     logInfo m!"count: {← countHypsMeta g.mvarId!}"


-- ============================================================================
-- E3  (warm-up).  Feel Trap #8 for yourself
-- ----------------------------------------------------------------------------
-- MOTIVATION: the single most common `MetaM` bug is trusting the screen.
--   Assigning a metavariable does NOT rewrite the `Expr` you hold; only
--   `instantiateMVars` applies the assignment (§2.2).  Prove it to yourself once
--   and you will never chase this ghost again.
--
-- TASK: in a `MetaM` `#eval`, make a fresh `Nat` mvar, assign it `7`, then log
--   two things side by side: whether the raw expression `isMVar` (it still is!),
--   and what it becomes after `instantiateMVars` (now `7`).
--
-- HINT: `mkFreshExprMVar (some (.const ``Nat []))`, then `m.mvarId!.assign
--   (mkNatLit 7)`; contrast `m.isMVar` against `← instantiateMVars m`.
--
--   (write your #eval here)
--
-- CHECK (uncomment; expect  raw isMVar? true   after instantiateMVars: 7):
-- #eval show MetaM Unit from do
--   let m ← mkFreshExprMVar (some (.const ``Nat []))
--   m.mvarId!.assign (mkNatLit 7)
--   logInfo m!"raw isMVar? {m.isMVar}   after instantiateMVars: {← instantiateMVars m}"


-- ============================================================================
-- E4  (core).  A tactic that reports the goal
-- ----------------------------------------------------------------------------
-- MOTIVATION: this is the smallest possible real tactic, the bridge from raw
--   `MetaM` to something a user types after `by`.  It does nothing but read the
--   goal, which is exactly what every inspection tactic (`show`, `trace_state`)
--   starts from.
--
-- TASK: write an `elab "show_target" : tactic` that logs the current goal's
--   target AND its head symbol (reuse `goalHead?` from E1).
--
-- HINT: grab the goal with `← getMainGoal`, then `← goal.getType` and
--   `← goalHead? goal`; report both with `logInfo m!"..."`.
--
--   (write show_target here)
--
-- CHECK (uncomment; the tactic prints  target: a + b = b + a   (head: Eq)):
-- example (a b : Nat) : a + b = b + a := by
--   show_target
--   exact Nat.add_comm a b


-- ============================================================================
-- Stretch  (bonus, optional).  Trap #8 where it actually hurts
-- ----------------------------------------------------------------------------
-- MOTIVATION: E3 showed the trap while PRINTING, where display auto-instantiates
--   and hides the bug.  The real damage is structural: when YOUR code takes an
--   `Expr` apart, it sees the un-instantiated hole.  This drills the reflex, call
--   `instantiateMVars` before you inspect, not merely before you print.
--
-- TASK: make a fresh `Nat` mvar, assign it `5`, then try to read it back as a
--   numeral with `Expr.nat?` BOTH before and after `instantiateMVars`.  Before,
--   the raw hole yields `none`; after, `some 5`.
--
-- HINT: `m.nat?` on the raw `m` versus `(← instantiateMVars m).nat?`.  (There is
--   no matching entry in Solutions/C2.lean; this one is yours to keep.)
--
--   (write your #eval here)
--
-- CHECK (uncomment; expect  before: none   after: some (5)):
-- #eval show MetaM Unit from do
--   let m ← mkFreshExprMVar (some (.const ``Nat []))
--   m.mvarId!.assign (mkNatLit 5)
--   logInfo m!"before: {m.nat?}   after: {(← instantiateMVars m).nat?}"
