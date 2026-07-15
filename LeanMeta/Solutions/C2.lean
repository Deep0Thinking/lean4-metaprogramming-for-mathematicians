import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 2 (`MetaM`)

Compare with `Exercises/C2.lean`. -/

-- E1.  The head symbol of the goal's target.
def goalHead? (goal : MVarId) : MetaM Name := do
  return (← goal.getType).getAppFnArgs.1

-- E2.  Count the real (non-implementation-detail) hypotheses: the `MetaM` core.
def countHypsMeta (goal : MVarId) : MetaM Nat :=
  goal.withContext do
    let mut n : Nat := 0
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do n := n + 1
    return n

-- E3.  Trap #8 first-hand: an assigned mvar's raw `Expr` is still a hole.
#eval show MetaM Unit from do
  let m ← mkFreshExprMVar (some (.const ``Nat []))
  m.mvarId!.assign (mkNatLit 7)
  logInfo m!"raw isMVar? {m.isMVar}   after instantiateMVars: {← instantiateMVars m}"
  -- raw isMVar? true   after instantiateMVars: 7

-- E4.  A tactic that reports the goal's target and its head symbol.
elab "show_target" : tactic => do
  let goal ← getMainGoal
  logInfo m!"target: {← goal.getType}   (head: {← goalHead? goal})"

example (a b : Nat) : a + b = b + a := by
  show_target                     -- target: a + b = b + a   (head: Eq)
  exact Nat.add_comm a b
