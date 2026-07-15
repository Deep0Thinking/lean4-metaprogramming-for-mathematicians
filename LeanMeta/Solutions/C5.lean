import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 5 (`TacticM`)

Compare with `Exercises/C5.lean`.  These are the classic "write your own copy of
a core tactic" exercises. -/

-- E1.  `my_trivial` as a macro.
macro "my_trivial" : tactic => `(tactic| first | rfl | assumption)
example (p : Prop) (hp : p) : p := by my_trivial

-- E2.  `count_hyps`: note the `: Nat` annotation on the counter (§0.4(h), Trap #2).
elab "count_hyps" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let mut n : Nat := 0
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do n := n + 1
    logInfo m!"{n} hypotheses"
example (a b : Nat) (h : a = b) : True := by
  count_hyps                      -- 3 hypotheses  (a, b, h)
  trivial

-- E3.  `my_constructor` in `MetaM`.
elab "my_constructor" : tactic => liftMetaTactic fun goal => goal.constructor
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by my_constructor <;> assumption

-- E4.  `my_left` / `my_right` (the `do` is required so `(← …)` is inside a do-block).
elab "my_left"  : tactic =>
  liftMetaTactic fun goal => do goal.apply (← mkConstWithFreshMVarLevels ``Or.inl)
elab "my_right" : tactic =>
  liftMetaTactic fun goal => do goal.apply (← mkConstWithFreshMVarLevels ``Or.inr)
example (p q : Prop) (hq : q) : p ∨ q := by my_right; assumption

-- E5.  `my_exfalso`: turn any goal into `False`.
elab "my_exfalso" : tactic =>
  liftMetaTactic fun goal => do goal.apply (← mkConstWithFreshMVarLevels ``False.elim)
example (p : Prop) (h : False) : p := by my_exfalso; assumption

-- E6 (bonus).  `my_clear h`: drop a named hypothesis.  We resolve the user's
-- identifier to an `FVarId` by looking it up in the local context.
elab "my_clear " h:ident : tactic => do
  let goal ← getMainGoal
  let fvarId ← goal.withContext do
    let some ldecl := (← getLCtx).findFromUserName? h.getId
      | throwError m!"no hypothesis named {h.getId}"
    pure ldecl.fvarId
  replaceMainGoal [← goal.clear fvarId]
example (p : Prop) (hp : p) (hjunk : p) : p := by
  my_clear hjunk
  exact hp
