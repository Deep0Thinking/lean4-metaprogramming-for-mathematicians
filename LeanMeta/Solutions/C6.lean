import Lean
import LeanMeta.C6_Capstone
open Lean Meta Elab Tactic MyTauto

set_option linter.unusedVariables false

/-! # Solutions for Chapter 6 (capstone `mytauto`)

Exercises ✎6 and ✎7: make the prover **classical** and let it prove `∃` goals.

We keep the intuitionistic skeleton of `MyTauto.core` (reusing its helpers
`assumptionCore` and `findDestructible?`, and the `succeeds` / `orElseRestore`
combinators from Chapter 5), and add two things:

* ✎7  an `Exists` case: `apply Exists.intro` leaves the witness as a metavariable,
       which a later `assumption` unifies into existence.
* ✎6  a **classical last resort**: when nothing intuitionistic makes progress on a
       `Prop` goal, prove it by contradiction (`Classical.byContradiction`).  A
       `usedContra` flag stops it from negating the same goal forever. -/

namespace SolutionsC6

/-- Classical propositional search.  `usedContra` records whether we have already
    fallen back to `byContradiction` on this branch (see ✎6). -/
partial def coreC (usedContra : Bool) (fuel : Nat) (goal : MVarId) : MetaM Unit := do
  if fuel == 0 then
    throwTacticEx `mytautoC goal m!"search depth exhausted"
  goal.withContext do
    -- Steps that ALWAYS make progress; take them and PROPAGATE `usedContra`
    -- unchanged (resetting it to `false` here is the classic bug: `byContradiction`
    -- would then fire again on the negated subgoal and the search would loop).
    if ← succeeds (assumptionCore goal) then return
    if let some fvarId := (← findDestructible? goal) then
      for sg in ← goal.cases fvarId do coreC usedContra (fuel - 1) sg.mvarId
      return
    let target ← whnf (← instantiateMVars (← goal.getType))
    if target.isConstOf ``True then
      goal.assign (.const ``True.intro [])
      return
    if target.isForall then
      let (_, g) ← goal.intro1P
      coreC usedContra (fuel - 1) g
      return
    match target.getAppFnArgs with
    | (``And, _) | (``Iff, _) =>
        for g in ← goal.constructor do coreC usedContra (fuel - 1) g
        return
    | _ => pure ()
    -- Steps that MIGHT fail: try each with rollback, then fall back to the next.
    -- (1) target-directed: choose an `Or` disjunct, or an `Exists` witness (✎7).
    let targetRule : MetaM Unit := do
      match target.getAppFnArgs with
      | (``Or, _) =>
          let l : MetaM Unit := do
            for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inl) do coreC usedContra (fuel - 1) g
          let r : MetaM Unit := do
            for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inr) do coreC usedContra (fuel - 1) g
          orElseRestore l (fun _ => r)
      | (``Exists, _) =>
          -- ✎7: `.nonDependentOnly` keeps the witness OUT of the returned goal
          -- list, leaving it a metavariable; proving `P ?w` by assumption then
          -- unifies `?w` into existence.
          let gs ← goal.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
                     (cfg := { newGoals := .nonDependentOnly })
          for g in gs do coreC usedContra (fuel - 1) g
      | _ => throwError "no target rule applies"
    if ← succeeds targetRule then return
    -- (2) backward chaining: apply some hypothesis `h : A → B`.
    let backward : MetaM Unit := do
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if !(← whnf ldecl.type).isForall then continue
        let attempt : MetaM Unit := do
          for g in ← goal.apply ldecl.toExpr do coreC usedContra (fuel - 1) g
        if ← succeeds attempt then return
      throwError "no applicable hypothesis"
    if ← succeeds backward then return
    -- (3) classical last resort (✎6): prove `a` by refuting `¬a`, once per branch.
    if !usedContra then
      if ← isProp target then
        let contra : MetaM Unit := do
          for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Classical.byContradiction) do
            coreC true (fuel - 1) g
        if ← succeeds contra then return
    throwTacticEx `mytautoC goal m!"cannot make progress"

/-- Classical `mytauto`.  `mytautoC` uses depth 25; `mytautoC n` uses depth `n`. -/
syntax "mytautoC" (num)? : tactic

elab_rules : tactic
  | `(tactic| mytautoC)        => liftMetaFinishingTactic (coreC false 30)
  | `(tactic| mytautoC $n:num) => liftMetaFinishingTactic (coreC false n.getNat)

end SolutionsC6

section Tests
variable (p q r : Prop)

-- Everything the intuitionistic `mytauto` proved still goes through:
example : p ∧ q → q ∧ p                  := by mytautoC
example : (p → q) → (q → r) → p → r      := by mytautoC

-- ✎6: classically-true tautologies the intuitionistic `mytauto` could NOT prove.
example : p ∨ ¬p                         := by mytautoC   -- excluded middle
example : ¬¬p → p                        := by mytautoC   -- double-negation elim
example : ¬(p ∧ q) → ¬p ∨ ¬q             := by mytautoC   -- a De Morgan law
example : (p → q) → ¬p ∨ q               := by mytautoC

-- ✎7: an existential whose witness is FORCED by a hypothesis (unification fills it).
example (P : Nat → Prop) (h : P 3) : ∃ x, P x := by mytautoC

/- FURTHER WORK: the limits of a BACKWARD-only prover.
   We chain backward and use `byContradiction` at most once per branch (the
   `usedContra` flag).  That guarantees termination but costs completeness: goals
   that need a hypothesis used FORWARD, computing `h · x : b` from `h : a → b`
   and `x : a`, are out of reach.  Each of these still fails with "cannot make
   progress":

       example : ((p → q) → p) → p   := by mytautoC   -- ✗ Peirce's law
       example : (¬q → ¬p) → p → q   := by mytautoC   -- ✗ contrapositive
       example : (p → q) ∨ (q → p)   := by mytautoC   -- ✗

   Real classical provers (e.g. Mathlib's `tauto`) add a forward-saturation step:
   repeatedly apply hypotheses to hypotheses to grow the context before searching.
   That is the natural next extension of this project. -/

end Tests
