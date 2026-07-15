import Lean
/-!
# Chapter 5. `TacticM`: writing real tactics

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§5.  `TacticM`: WRITING REAL TACTICS
--------------------------------------------------------------------------------

§5.1  Anatomy
-------------
`elab "foo" : tactic => body` is sugar.  Here is the same tactic written out in
full, so that you can read Lean's and Mathlib's source, which uses the long form: -/

syntax (name := myFirstTac) "my_first_tac" : tactic     -- 1. the syntax + its KIND

@[tactic myFirstTac]                                    -- 2. register an elaborator
def evalMyFirstTac : Tactic := fun _stx => do           --    Tactic = Syntax → TacticM Unit
  logInfo "I am a tactic, spelled out the long way."

example : True := by
  my_first_tac
  trivial

/-
The `TacticM` state is essentially `List MVarId`: the goals.  The API:

    getMainGoal      : TacticM MVarId          -- first goal (fails if none)
    getGoals         : TacticM (List MVarId)
    setGoals         : List MVarId → TacticM Unit
    replaceMainGoal  : List MVarId → TacticM Unit
    withMainContext  : TacticM α → TacticM α   -- enter the main goal's context
    liftMetaTactic          : (MVarId → MetaM (List MVarId)) → TacticM Unit
    liftMetaFinishingTactic : (MVarId → MetaM Unit)          → TacticM Unit
    evalTactic       : Syntax → TacticM Unit   -- run another tactic!

`liftMetaTactic` is the bridge, and it is how you should write 95% of your
tactics: do the work in `MetaM` on an `MVarId`, and let it manage the goal list.
Its cousin `liftMetaFinishingTactic` is for tactics that CLOSE the goal (leave no
subgoals).
-/

/-! ### §5.2  `my_rfl`: closing a goal with a term you built

Our first real tactic.  Read the four steps; every finishing tactic looks like
this.  Recall from §0.4(d) the `let some pat := e | fail` idiom; step 2 uses it
to insist the goal is an equality. -/

def myRflCore (goal : MVarId) : MetaM Unit := do
  goal.withContext do
    goal.checkNotAssigned `my_rfl                            -- 0. sanity
    let target ← instantiateMVars (← goal.getType)           -- 1. read the goal
    let some (_, lhs, rhs) := target.eq?                     -- 2. match its shape
      | throwTacticEx `my_rfl goal m!"target is not an equality:{indentExpr target}"
    unless ← isDefEq lhs rhs do                              -- 3. do the real work
      throwTacticEx `my_rfl goal m!"the two sides are not definitionally equal"
    goal.assign (← mkEqRefl lhs)                             -- 4. close it

elab "my_rfl" : tactic => liftMetaFinishingTactic myRflCore

example : 2 + 2 = 4 := by my_rfl
example (n : Nat) : n + 0 = n := by my_rfl
-- example (n : Nat) : 0 + n = n := by my_rfl    -- ✗ correctly fails: not defeq!
                                                 --    (`Nat.add` recurses on its
                                                 --     second argument: `n + 0`
                                                 --     reduces, `0 + n` gets stuck.)

/-! ### §5.3  `my_assumption`: searching the local context

Note the shape: iterate the context, test with `isDefEq`, assign. -/

def myAssumptionCore (goal : MVarId) : MetaM Unit := do
  goal.withContext do
    goal.checkNotAssigned `my_assumption
    let target ← goal.getType
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if ← isDefEq ldecl.type target then
        goal.assign ldecl.toExpr                  -- `toExpr` = the fvar itself
        return
    throwTacticEx `my_assumption goal m!"no hypothesis matches{indentExpr target}"

elab "my_assumption" : tactic => liftMetaFinishingTactic myAssumptionCore

example (p q : Prop) (hp : p) (hq : q) : q := by my_assumption

/-! ### §5.4  Tactics with a term argument: `my_exact`, `my_apply`

The new ingredient is *elaborating the user's term against the goal*.  Notice
`n:term` in the syntax: that binds the parsed argument so the body can use it. -/

elab "my_exact " t:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let e ← elabTermEnsuringType t (some target)   -- Syntax → Expr, checked against the goal
    goal.assign e
    replaceMainGoal []                             -- no goals left

elab "my_apply " t:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let e ← elabTerm t none                        -- no expected type: `apply` unifies
    let newGoals ← goal.apply e                    -- ← all the hard work is here
    replaceMainGoal newGoals

example (p q : Prop) (hpq : p → q) (hp : p) : q := by
  my_apply hpq
  my_exact hp

/-
What `MVarId.apply e` actually does, and it is worth knowing:
  * infer the type of `e`, say `A₁ → ... → Aₙ → C`;
  * create fresh metavariables `?a₁ ... ?aₙ`;
  * `isDefEq C target`: unifying, which may solve some of the `?aᵢ`;
  * assign `goal := e ?a₁ ... ?aₙ`;
  * return the `?aᵢ` that are still unassigned: *those are your new goals*.
That is the entire mechanism of backwards reasoning in Lean.
-/

/-! ### §5.5  Recursion: `my_intros`

`partial` marks a function Lean should accept without a termination proof.  Meta
search functions rarely have obvious termination, and you do not want to prove it,
so `partial` is idiomatic here, not a code smell. -/

partial def introsAllCore (goal : MVarId) : MetaM MVarId := do
  let target ← whnf (← instantiateMVars (← goal.getType))
  if target.isForall then
    let (_, goal) ← goal.intro1P            -- `1P` = one, Preserving the binder name
    introsAllCore goal
  else
    return goal

elab "my_intros" : tactic =>
  liftMetaTactic fun goal => do return [← introsAllCore goal]

example (p q : Prop) : p → q → p := by
  my_intros
  my_assumption

/-
⚑ TRAP #11: meta-level recursion almost always needs `partial def`.  Lean cannot
see why your search terminates (it usually does not, in general), and you do not
want to prove it.  For *search*, add an explicit fuel parameter, as we do in §6,
so the recursion is bounded no matter what.
-/

/-! ### §5.6  Calling other tactics: `evalTactic`

Your tactic can run existing tactics.  Build the syntax with a quotation, splice
in the user's arguments, and hand it to `evalTactic`. -/

elab "use_hyp " n:ident : tactic => do
  evalTactic (← `(tactic| exact $n))          -- construct `exact n` and run it

example (p : Prop) (hp : p) : p := by use_hyp hp

/-- Reimplementing `<;>`: run `a`, then run `b` on *every* goal that `a` left.

    This is a good exercise in the goal-list mechanics of §5.1: we grab the
    goals `a` produced, run `b` on each in turn, and collect whatever goals `b`
    leaves behind (there may be several, or none). -/
elab "and_then " a:tactic b:tactic : tactic => do
  evalTactic a                          -- 1. run `a`; several goals may remain
  let goals ← getGoals
  let mut newGoals : Array MVarId := #[] -- 2. accumulate what `b` leaves
  for goal in goals do
    setGoals [goal]                     --    focus on one goal...
    evalTactic b                        --    ...run `b` there...
    newGoals := newGoals ++ (← getGoals) -- ...and keep its leftovers
  setGoals newGoals.toList              -- 3. install the combined goal list

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  and_then (constructor) (assumption)

/-! ### §5.7  Errors, messages, and traces: how to be a good citizen

    throwError m!"..."                     -- generic failure
    throwTacticEx `tac goal m!"..."        -- failure, with the goal attached (preferred)
    logInfo / logWarning / logError        -- non-fatal messages
    withRef stx do ...                     -- report errors AT the user's syntax

A tactic that fails must fail with a message that says what it looked at.  Note
`indentExpr`, which formats an `Expr` on its own indented line. -/

elab "blame " t:term : tactic => withRef t do
  throwError "I refuse to look at this term"
-- example : True := by blame (1+1)      -- ✗ the squiggle sits under `(1+1)`, not `blame`

/-
For debugging your own tactic, `logInfo` is a blunt instrument (it fires always).
Use a *trace class* instead: it is off by default and switchable per-example. -/

initialize registerTraceClass `tutorial

elab "noisy" : tactic => do
  trace[tutorial] "the goal is {← getMainGoal}"    -- silent unless the class is on
  evalTactic (← `(tactic| trivial))

/-
⚑ TRAP #12: a trace (or option) you register with `initialize registerTraceClass`
is NOT visible to `set_option` in the SAME file.  It only becomes a real option
in files that *import* this one.  So the natural

        set_option trace.tutorial true in
        example : True := by noisy

works from an importing file, but NOT here in the file that defines the class.
(This is why real projects keep their trace classes in a small imported module.)

To still *see* the trace fire within this very file, we can enable the option
programmatically with `withOptions`, which sets it by name and bypasses the
`set_option` restriction.  Compare `noisy` (silent) with `noisy_seen` below;
put your cursor on the `example` and read the Infoview: -/

elab "noisy_seen" : tactic => do
  withOptions (fun o => o.setBool `trace.tutorial true) do
    trace[tutorial] "the goal is {← getMainGoal}"  -- now this prints
  evalTactic (← `(tactic| trivial))

example : True := by noisy_seen                     -- Infoview shows: [tutorial] the goal is ⊢ True

/-! ### §5.8  ⚑ TRAP #13: BACKTRACKING.  Exceptions do NOT restore state.

`MetaM` state (in particular metavariable assignments) lives behind a mutable
reference.  If a tactic half-succeeds, assigning some metavariables, and *then*
throws, those assignments **survive the exception**.  `try ... catch ...` alone
is therefore not backtracking, and using it as if it were produces bugs that are
absolutely miserable to debug.

Always save and restore explicitly.  `Meta.saveState` snapshots the state;
`s.restore` rewinds to the snapshot: -/

/-- Run `x`; if it fails, roll the state back completely and run `y` instead. -/
def orElseRestore {α : Type} (x : MetaM α) (y : Unit → MetaM α) : MetaM α := do
  let s ← Meta.saveState
  try
    x
  catch _ =>
    s.restore
    y ()

/-- Run `x`; report whether it succeeded, rolling back if it did not. -/
def succeeds (x : MetaM Unit) : MetaM Bool := do
  let s ← Meta.saveState
  try
    x
    return true
  catch _ =>
    s.restore
    return false

/-
Lean also provides `withoutModifyingState`, `commitWhen`, and the syntactic
combinators you already know: `first | t₁ | t₂`, `try t`, `repeat t`,
`all_goals t`, `any_goals t`, `focus t`.  Under the hood they all do the
save/restore dance so that you do not have to.
-/
