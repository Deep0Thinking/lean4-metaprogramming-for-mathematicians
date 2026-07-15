import Lean
import LeanMeta.C5_TacticM
/-!
# Chapter 6. Capstone: `mytauto`, a backtracking propositional prover

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§6.  CAPSTONE: `mytauto`, A BACKTRACKING PROPOSITIONAL PROVER
--------------------------------------------------------------------------------
Everything so far, assembled into one real tactic.  It proves intuitionistic
propositional tautologies by:

  1.  closing the goal with a hypothesis                 (`assumption`)
  2.  taking a hypothesis apart                          (`cases`: ∧ ∨ ↔ ∃ False)
  3.  introducing                                        (`intro`: → ∀ ¬)
  4.  splitting the target                               (`constructor`: ∧ ↔)
  5.  choosing a disjunct, WITH BACKTRACKING             (`Or.inl` / `Or.inr`)
  6.  applying a hypothesis, WITH BACKTRACKING           (`h : A → B` against `B`)

with a fuel parameter to guarantee termination.  Read it top to bottom; each
helper uses only things defined earlier in this file.
-/

namespace MyTauto

initialize registerTraceClass `mytauto

/-- Which hypotheses can we usefully `cases` on? -/
def isDestructible (ty : Expr) : Bool :=
  match ty.getAppFnArgs with
  | (``And, _) | (``Or, _) | (``Iff, _) | (``Exists, _) | (``False, _) => true
  | _ => false

/-- The first hypothesis we can take apart, if any. -/
def findDestructible? (goal : MVarId) : MetaM (Option FVarId) :=
  goal.withContext do
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      -- `whnfR`, not `whnf`: we must not see through the user's own definitions.
      if isDestructible (← whnfR ldecl.type) then
        return some ldecl.fvarId
    return none

/-- Close `goal` using a hypothesis, or fail. -/
def assumptionCore (goal : MVarId) : MetaM Unit :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if ← isDefEq ldecl.type target then
        goal.assign ldecl.toExpr
        return
    throwTacticEx `mytauto goal m!"no matching hypothesis"

/-- The search itself.  `fuel` bounds the depth (see §5.5's note on termination). -/
partial def core (fuel : Nat) (goal : MVarId) : MetaM Unit := do
  if fuel == 0 then
    throwTacticEx `mytauto goal m!"search depth exhausted (try `mytauto n` for larger n)"
  goal.withContext do
    trace[mytauto] "[fuel {fuel}] {goal}"

    -- 1.  Already provable from a hypothesis?
    if ← succeeds (assumptionCore goal) then return

    -- 2.  Can we take a hypothesis apart?  (This always makes progress:
    --     `cases` removes the hypothesis and replaces it by strictly simpler ones.)
    if let some fvarId := (← findDestructible? goal) then
      let subgoals ← goal.cases fvarId          -- `False` yields ZERO subgoals: done.
      for sg in subgoals do
        core (fuel - 1) sg.mvarId
      return

    -- 3.  Look at the target.  `whnf` here so that `¬p` shows up as `p → False`.
    let target ← whnf (← instantiateMVars (← goal.getType))

    if target.isConstOf ``True then
      goal.assign (.const ``True.intro [])
      return

    if target.isForall then                     -- → , ∀ , ¬
      let (_, goal) ← goal.intro1P
      core (fuel - 1) goal
      return

    match target.getAppFnArgs with
    | (``And, _) | (``Iff, _) =>                -- split: one subgoal per field
        for g in ← goal.constructor do
          core (fuel - 1) g
        return
    | (``Or, _) =>                              -- guess, and be ready to take it back
        -- `mkConstWithFreshMVarLevels ``c` = the constant `c` with fresh
        -- universe-level holes for `apply` to unify (see §1.4).
        let tryLeft : MetaM Unit := do
          for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inl) do
            core (fuel - 1) g
        let tryRight : MetaM Unit := do
          for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inr) do
            core (fuel - 1) g
        orElseRestore tryLeft (fun _ => tryRight)
        return
    | _ => pure ()

    -- 4.  Last resort: backward chaining.  Try applying each `h : A → B`.
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if !(← whnf ldecl.type).isForall then continue
      let attempt : MetaM Unit := do
        for g in ← goal.apply ldecl.toExpr do
          core (fuel - 1) g
      if ← succeeds attempt then return

    throwTacticEx `mytauto goal m!"I cannot make progress on this goal"

/-- The front end.  `mytauto` uses depth 10; `mytauto 25` uses depth 25. -/
syntax "mytauto" (num)? : tactic

elab_rules : tactic
  | `(tactic| mytauto)         => liftMetaFinishingTactic (core 10)
  | `(tactic| mytauto $n:num)  => liftMetaFinishingTactic (core n.getNat)

end MyTauto

section Tests
variable (p q r : Prop)

example : True                                   := by mytauto
example (hp : p) (hq : q) : p ∧ q                := by mytauto
example : p ∧ q → q ∧ p                          := by mytauto
example : p ∨ q → q ∨ p                          := by mytauto
example : (p → q) → (q → r) → p → r              := by mytauto
example : p → ¬¬p                                := by mytauto
example (h : False) : p                          := by mytauto
example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)        := by mytauto
example : (p ↔ q) → (q ↔ p)                      := by mytauto
example : ¬(p ∨ q) → ¬p ∧ ¬q                     := by mytauto

-- ✗ Correctly FAILS: this is not intuitionistically provable.
-- example : p ∨ ¬p := by mytauto        (see Exercise ✎6)

end Tests

/-! ### §6.1  The payoff: look at what your tactic *made*

A tactic is a proof-term generator.  Ours generated an honest term, and the
kernel checked it.  Prove it to yourself: -/

theorem and_comm_demo (p q : Prop) (h : p ∧ q) : q ∧ p := by mytauto

#print and_comm_demo              -- the actual λ-term your search produced
#print axioms and_comm_demo       -- 'and_comm_demo' does not depend on any axioms
