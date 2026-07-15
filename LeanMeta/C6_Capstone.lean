import Lean
import LeanMeta.C5_TacticM
/-!
# Chapter 6. Capstone: `mytauto`, a backtracking propositional prover

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

This is where all six chapters pay off: a real tactic that proves theorems on its
own.  `mytauto` searches for a proof of an intuitionistic propositional goal, and
its strategy is one you already use when proving by hand.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§6.  CAPSTONE: `mytauto`, A BACKTRACKING PROPOSITIONAL PROVER
--------------------------------------------------------------------------------

THE STRATEGY: safe moves first, guess only when forced.

Some proof moves can never hurt: if the goal was provable, it is still provable
after the move.  Proof theorists call these rules *invertible*; think of them as
SAFE.  You apply them eagerly and never need to undo them:

    * destruct a compound hypothesis   (`cases` on `∧`, `∨`, `↔`, `∃`, `False`);
    * `intro` an implication, `∀`, or `¬`;
    * split a conjunction or `↔`        (`constructor`).

The other moves are GUESSES: they can turn a provable goal into a dead end, so you
must be ready to take them back, i.e. to BACKTRACK (Ch5):

    * which disjunct to prove for an `∨` goal   (`Or.inl` vs `Or.inr`);
    * which hypothesis `h : A → B` to apply       (backward chaining).

`mytauto` does exactly this: it fires every safe move it can, and only when none
applies does it guess, wrapped in the save/restore of Ch5.  (The mechanical reason a
guess needs save/restore: a failed attempt has already written metavariable
assignments to the shared state, Ch5's whiteboard, so it must be rolled back before
the next branch is tried; a safe move needs no rollback precisely because it makes no
choice.)  A `fuel` counter bounds the recursion so the search always terminates (Ch5,
Trap 11); without it, backward chaining on a hypothesis like `h : A → A` could loop
forever.

Read the search top to bottom; each helper uses only things defined earlier, here
or in Chapter 5.
-/

namespace MyTauto

initialize registerTraceClass `mytauto

/-- Which hypotheses are worth a `cases`?  The ones that break into strictly
    simpler pieces: `∧`, `∨`, `↔`, `∃`, and `False` (which breaks into nothing at
    all, closing the goal outright). -/
def isDestructible (ty : Expr) : Bool :=
  match ty.getAppFnArgs with
  | (``And, _) | (``Or, _) | (``Iff, _) | (``Exists, _) | (``False, _) => true
  | _ => false

/-- The first hypothesis we can take apart, if any. -/
def findDestructible? (goal : MVarId) : MetaM (Option FVarId) :=
  goal.withContext do
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      -- `whnfR` (reducible only), not `whnf`: we must not see through the user's
      -- own definitions when deciding a hypothesis's shape (Ch1, transparency).
      if isDestructible (← whnfR ldecl.type) then
        return some ldecl.fvarId
    return none

/-- Close `goal` using a hypothesis, or fail.  This is the search's base case:
    "are we already done?" -/
def assumptionCore (goal : MVarId) : MetaM Unit :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if ← isDefEq ldecl.type target then
        goal.assign ldecl.toExpr
        return
    throwTacticEx `mytauto goal m!"no matching hypothesis"

/-- The search itself.  It tries the moves in order of preference: cheap and SAFE
    first (assumption, then destruct a hypothesis, then the safe target rules), and
    only the risky GUESSES last, each guarded by the backtracking of Ch5.  `fuel`
    bounds the depth (Ch5, Trap 11).

    Two things to hold in mind.  INVARIANT: each `core` call either fully assigns its
    goal a proof term or throws, and every branch that made a *choice* restores the
    state before trying the next option.  ORDER: among the SAFE moves the order is
    free (they are invertible, so any order reaches the same reduced goals); the only
    ordering that matters is that all safe moves are used before any guess.  We
    destruct hypotheses early only because it can end the search at once (`h : False`
    closes with zero subgoals), not because correctness requires it. -/
partial def core (fuel : Nat) (goal : MVarId) : MetaM Unit := do
  if fuel == 0 then
    throwTacticEx `mytauto goal m!"search depth exhausted (try `mytauto n` for larger n)"
  goal.withContext do
    trace[mytauto] "[fuel {fuel}] {goal}"

    -- 1.  Base case: already provable from a hypothesis?
    if ← succeeds (assumptionCore goal) then return

    -- 2.  SAFE: take a hypothesis apart.  `cases` replaces the hypothesis by simpler
    --     pieces (`False` yields ZERO subgoals, closing the goal on the spot).  Mostly
    --     smaller, but `↔` splits into two arrows, so there is no clean decreasing
    --     measure; that is exactly why the search is `partial` and fuel-bounded rather
    --     than termination-checked.  No backtracking needed (an invertible move).
    if let some fvarId := (← findDestructible? goal) then
      let subgoals ← goal.cases fvarId
      for sg in subgoals do
        core (fuel - 1) sg.mvarId
      return

    -- 3.  Look at the target.  `whnf` here so that `¬p` shows up as `p → False`.
    let target ← whnf (← instantiateMVars (← goal.getType))

    if target.isConstOf ``True then             -- trivially true
      goal.assign (.const ``True.intro [])
      return

    if target.isForall then                     -- SAFE: intro  (→ , ∀ , ¬)
      let (_, goal) ← goal.intro1P
      core (fuel - 1) goal
      return

    match target.getAppFnArgs with
    | (``And, _) | (``Iff, _) =>                -- SAFE: split, one subgoal per field
        for g in ← goal.constructor do
          core (fuel - 1) g
        return
    | (``Or, _) =>                              -- GUESS: pick a disjunct, be ready to undo
        -- `mkConstWithFreshMVarLevels ``c` = the constant `c` with fresh
        -- universe-level holes for `apply` to unify (see §1.4).
        let tryLeft : MetaM Unit := do
          for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inl) do
            core (fuel - 1) g
        let tryRight : MetaM Unit := do
          for g in ← goal.apply (← mkConstWithFreshMVarLevels ``Or.inr) do
            core (fuel - 1) g
        orElseRestore tryLeft (fun _ => tryRight)   -- try inl; on failure roll back, try inr
        return
    | _ => pure ()

    -- 4.  GUESS of last resort: backward chaining.  Try applying each `h : A → B`
    --     against the goal, each attempt guarded by `succeeds` (rolls back on failure).
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      -- Full `whnf`, not `whnfR`, on purpose: a hypothesis `h : ¬X` must unfold to
      -- `X → False` to count as an arrow to apply.  The transparency dial is by
      -- PURPOSE, not given-vs-goal: reducible-only when deciding to `cases` (step 2,
      -- so we never shatter a user `def`); full `whnf` when asking "is this an arrow?"
      -- (both the target in step 3 and a hypothesis here).
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

/-! ### §6.1 (tests first)  It really proves things

Each `example` below is a genuine theorem `mytauto` closes on its own, exercising a
different part of the search. -/

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

-- ✗ Correctly FAILS, and this is not a bug: `p ∨ ¬p` (excluded middle) has NO
-- intuitionistic (constructive) proof, and `mytauto` is an intuitionistic prover,
-- so it rightly cannot find one.  Exercise ✎6 makes it classical.
-- example : p ∨ ¬p := by mytauto

end Tests

/-! ### §6.2  Watch the search run

`core` logs each step through `trace[mytauto]`.  Because we registered that class in
*this* file, `set_option trace.mytauto true` will not work here (Ch5, Trap 12); it
works only from a file that *imports* this one.  To watch the search in-file we reuse
the `withOptions` trick from §5.7, forcing the class on inside one demo tactic: -/

elab "mytauto_trace" : tactic =>
  withOptions (fun o => o.setBool `trace.mytauto true) do
    liftMetaFinishingTactic (MyTauto.core 10)

example (p q : Prop) : p ∨ q → q ∨ p := by mytauto_trace

/-! Put your cursor on that `example` and read the trace in the Infoview.  After
`intro` and `cases` on the hypothesis, the `∨` goal `⊢ q ∨ p` first tries `Or.inl`
(subgoal `⊢ q`, which dead-ends silently), then `orElseRestore` rolls back and
`Or.inr` (subgoal `⊢ p`) closes by assumption.  You are watching a guess get
retracted, the Ch5 backtracking at work.  (A goal like `p ∨ ¬p` shows the same dance
with *both* sides dead-ending, and `mytauto n` on `h : A → A ⊢ A` shows `⊢ A`
regenerating at each fuel level until fuel runs out.) -/

/-! ### §6.3  The payoff: look at what your tactic *made*

Here is the moment the whole tutorial was building toward.  `mytauto` did not merely
*decide* that the theorem holds; by Curry-Howard (Ch0, Ch1) it *constructed a proof
term*, an `Expr` whose type is the theorem statement, exactly the kind of object
Chapter 1 taught you to build.  And the kernel then re-checked that term from
scratch: even if our search had a bug, a wrong "proof" would be rejected, which is
why writing tactics is safe to experiment with (Ch0).  See both facts for yourself: -/

theorem and_comm_demo (p q : Prop) (h : p ∧ q) : q ∧ p := by mytauto

#print and_comm_demo              -- the actual λ-term your search produced
#print axioms and_comm_demo       -- 'and_comm_demo' does not depend on any axioms

/-
`#print and_comm_demo` prints

    fun p q h => And.casesOn h fun left right => ⟨right, left⟩

and you can read your own code in it: the `And.casesOn h` is the `goal.cases` of
step 2; the `⟨right, left⟩` is the `goal.constructor` that split the `∧` goal
(`And.intro`); and the two leaves `right`, `left` are the two `assumptionCore`
closes.  `#print axioms` reports no axioms at all: the proof is fully *constructive*,
using no classical or choice principle, which is the flip side of `mytauto` failing
on `p ∨ ¬p`.

`mytauto` is a genuine, working tactic, sound for intuitionistic logic and built from
the pieces of Chapters 1 through 5.  It is NOT a *complete* decision procedure,
though: it has no implication-left rule, so it misses some intuitionistic tautologies
(for instance `((a → b) → a) → ¬¬a`), and it is fuel-bounded.  Making it stronger, and
classical, is what the `Exercises/` are for.  Chapter 7 collects the debugging tools,
a cheat sheet, and where to go next.
-/
