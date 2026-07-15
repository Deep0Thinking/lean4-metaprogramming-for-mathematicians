import Lean
/-!
# Chapter 5. `TacticM`: writing real tactics

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

This is the payoff chapter.  Everything so far, `Expr` (Ch1), goals as
metavariables (Ch2), `Syntax` (Ch3), and elaboration (Ch4), now assembles into
actual tactics.  We build small versions of tactics you use daily (`my_rfl`,
`my_assumption`, `my_exact`, `my_apply`, `my_intros`, and a `<;>`), then cover
errors and traces, and finish with the one genuinely surprising hazard of
meta-programming: backtracking.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§5.  `TacticM`: WRITING REAL TACTICS
--------------------------------------------------------------------------------

§5.1  Two layers: `TacticM` (the manager) and `MetaM` (the worker)
------------------------------------------------------------------
`elab "foo" : tactic => body` is sugar.  Here is the same tactic written out in
full, so you can read Lean's and Mathlib's source, which uses the long form: -/

syntax (name := myFirstTac) "my_first_tac" : tactic     -- 1. the syntax + its KIND

@[tactic myFirstTac]                                    -- 2. register an elaborator
def evalMyFirstTac : Tactic := fun _stx => do           --    Tactic = Syntax → TacticM Unit
  logInfo "I am a tactic, spelled out the long way."

example : True := by
  my_first_tac
  trivial

/-
A tactic runs in `TacticM`, whose state is essentially the `List MVarId` of open
goals.  But almost all the interesting work, matching a target, unifying, assigning
a proof, happens one goal at a time in `MetaM` (Ch2).  So think of two layers:

    TacticM   the MANAGER: holds the to-do list of goals, parses the syntax
    MetaM     the WORKER : does one job on one goal, and reports back new jobs

DESIGN RULE, and it is the rule every real tactic follows: put the *logic* in
`MetaM` on a single `MVarId`, and keep only goal-list bookkeeping in `TacticM`.
Why bother?  Two concrete payoffs: the `MetaM` logic is then reusable by *other*
tactics (our capstone in Ch6 calls its own cores directly), and it is testable in
isolation with `#eval`, no `by` block required.

The bridge between the layers is `liftMetaTactic` (the `MetaM ⊆ TacticM` lift of
§0.3, specialized to goals): hand it a worker `MVarId → MetaM (List MVarId)` and it
runs it on the main goal and splices the returned goals back into the manager's
list.  The core `TacticM` API:

    getMainGoal      : TacticM MVarId          -- first goal (fails if none)
    getGoals         : TacticM (List MVarId)
    setGoals         : List MVarId → TacticM Unit
    replaceMainGoal  : List MVarId → TacticM Unit
    withMainContext  : TacticM α → TacticM α   -- enter the main goal's context
    liftMetaTactic          : (MVarId → MetaM (List MVarId)) → TacticM Unit
    liftMetaFinishingTactic : (MVarId → MetaM Unit)          → TacticM Unit
    evalTactic       : Syntax → TacticM Unit   -- run another tactic!

`liftMetaFinishingTactic` is the variant for tactics that CLOSE the goal (leave no
subgoals).  Use these two and you rarely touch the goal list by hand.

THE RECURRING SHAPE.  Nearly every `MetaM` tactic core is the same five steps, and
once you see it you will recognise it in all of Lean's source:

    0.  goal.withContext do ...          -- enter the goal's hypotheses (Ch2, Trap 7)
    1.  let target ← instantiateMVars (← goal.getType)   -- read the goal (Ch2, Trap 8)
    2.  match target ...                 -- inspect its shape (Ch1)
    3.  ... isDefEq / apply / cases ...  -- do the real work (Ch1, Ch2)
    4.  goal.assign proof   (or return subgoals)         -- fill the hole (Ch2)

Watch for this skeleton in every core below.
-/

/-! ### §5.2  `my_rfl`: closing a goal with a term you built

Our first real tactic, and a textbook instance of the five-step shape.  Recall from
§0.4(d) the `let some pat := e | fail` idiom; step 2 uses it to insist the goal is
an equality. -/

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

/-! Now the payoff of the two-layer split, made real.  Because `myRflCore` is plain
`MetaM` on one `MVarId`, we can run it with NO `by` block and NO goal list: build the
goal by hand and call the core directly.  This is the "testable in isolation" the
design rule promised, and the reason the same core is reusable inside a bigger tactic
(Ch6). -/

#eval show MetaM Unit from do
  let lhs ← mkAppM ``HAdd.hAdd #[mkNatLit 2, mkNatLit 2]   -- build `2 + 2`
  let goalType ← mkEq lhs (mkNatLit 4)                     -- the goal `2 + 2 = 4`
  let goal ← mkFreshExprMVar (some goalType)               -- as a metavariable (Ch2)
  myRflCore goal.mvarId!                                   -- run the core directly
  logInfo m!"core ran, no `by`: {← instantiateMVars goal}" -- Eq.refl (2 + 2)

/-! (A double-entry you may wonder about: the cores call `goal.withContext`, while
the §5.1 API lists `withMainContext`.  They are the same operation at two layers:
`withMainContext` enters the main goal's context in `TacticM`; `goal.withContext`
does it in `MetaM` for a specific `MVarId`.  `liftMetaTactic` already wraps your core
in `withMainContext`, so the core's own `goal.withContext` is redundant *when
lifted*, but it is exactly what makes the standalone call above work.) -/

/-! ### §5.3  `my_assumption`: searching the local context

The same five steps, with step 3 a search: iterate the context, test each
hypothesis against the target with `isDefEq`, assign the first that matches.
(Unlike `my_rfl`, this core reads a *bare* `goal.getType` with no `instantiateMVars`:
`isDefEq` instantiates metavariables internally as it unifies, so you only need
`instantiateMVars` yourself when YOU take the `Expr` apart, as `my_rfl`'s `.eq?`
does.) -/

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

The new ingredient is *elaborating the user's term*, and here Chapter 4 pays off:
**the goal is the expected type**.  So `my_exact e` elaborates `e` with the goal as
its expected type (`elabTermEnsuringType t (some target)`), which is exactly what
makes `exact` type-check `e` against the goal.  `my_apply e` instead passes `none`,
because a term like `hpq : p → q` does NOT have the goal's type `q`; only its
*conclusion* does.  Forcing expected-type = goal would fail, so we let `MVarId.apply`
(box below) unify that conclusion with the goal.

Two asides.  First, these two tactics deliberately break the `liftMeta*` mold of
§5.2 and run directly in `TacticM` with `getMainGoal` / `replaceMainGoal`.  The
reason is layering (§0.3): *elaborating* the user's term needs the `TermElabM` layer,
which a bare `MVarId → MetaM _` core cannot reach, so the elaboration must happen up
in `TacticM`; the real logic still lives in `MetaM` (`goal.apply`, `goal.assign`).
Second, what `my_apply` writes by hand, `getMainGoal → work → replaceMainGoal`, *is*
`liftMetaTactic` unrolled; we unroll it only because of that elaboration step.
(`n:term` in the syntax binds the parsed argument so the body can use it.) -/

elab "my_exact " t:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let e ← elabTermEnsuringType t (some target)   -- expected type = the goal (Ch4)
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
What `MVarId.apply e` actually does, and it is worth knowing, because it is the
whole of backwards reasoning:
  * infer the type of `e`, say `A₁ → ... → Aₙ → C`;
  * create fresh metavariables `?a₁ ... ?aₙ` (Ch2: holes = subgoals);
  * `isDefEq C target`: unify the conclusion with the goal, which may solve some `?aᵢ`;
  * assign `goal := e ?a₁ ... ?aₙ`;
  * return the `?aᵢ` that are still unassigned: *those are your new goals*.
-/

/-! ### §5.5  Recursion: `my_intros`

`partial` marks a function Lean should accept without a termination proof.  Meta
search functions rarely have obvious termination, and you do not want to prove it,
so `partial` is idiomatic here, not a code smell. -/

partial def introsAllCore (goal : MVarId) : MetaM MVarId := do
  -- `whnf` so a goal that only *reduces* to a `∀` (a def unfolding to a function
  -- type) still counts; `isForall` on the raw target is a purely structural test.
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

You do not always have to work at the `Expr` level.  Your tactic can *run existing
tactics*: build the tactic syntax with a quotation (Ch3), splice in the user's
arguments, and hand it to `evalTactic`.  This is often the shortest route. -/

elab "use_hyp " n:ident : tactic => do
  evalTactic (← `(tactic| exact $n))          -- construct `exact n` and run it

example (p : Prop) (hp : p) : p := by use_hyp hp

/-- Reimplementing `<;>`: run `a`, then run `b` on *every* goal that `a` left.

    A good exercise in the manager-level (goal-list) mechanics of §5.1: grab the
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

A tactic is a tool other people (including future you) will run, so it should fail
loudly and informatively.  The vocabulary:

    throwError m!"..."                     -- generic failure
    throwTacticEx `tac goal m!"..."        -- failure, with the goal attached (preferred)
    logInfo / logWarning / logError        -- non-fatal messages
    withRef stx do ...                     -- report the error AT the user's syntax

A failing tactic should say what it looked at.  Note `indentExpr`, which formats an
`Expr` on its own indented line, and `withRef`, which points the red squiggle at the
offending piece of the user's input rather than at your tactic's name. -/

elab "blame " t:term : tactic => withRef t do
  throwError "I refuse to look at this term"
-- example : True := by blame (1+1)      -- ✗ the squiggle sits under `(1+1)`, not `blame`

/-
For debugging your own tactic, `logInfo` is a blunt instrument (it fires always,
for every user).  Use a *trace class* instead: it is off by default and switchable
per example with `set_option trace.myclass true`. -/

initialize registerTraceClass `tutorial

elab "noisy" : tactic => do
  trace[tutorial] "the goal is {← getMainGoal}"    -- silent unless the class is on
  evalTactic (← `(tactic| trivial))

/-
⚑ TRAP #12: a trace class you register with `initialize registerTraceClass` is NOT
visible to `set_option` in the SAME file; it only becomes a usable option in files
that *import* this one.  So the natural

        set_option trace.tutorial true in
        example : True := by noisy

works from an importing file, but NOT here in the file that defines the class.
(This is why real projects keep their trace classes in a small imported module.)

To still *see* the trace fire within this very file, we enable the option
programmatically with `withOptions`, which sets it by name and bypasses the
`set_option` restriction.  Compare `noisy` (silent) with `noisy_seen` below; put
your cursor on the `example` and read the Infoview: -/

elab "noisy_seen" : tactic => do
  withOptions (fun o => o.setBool `trace.tutorial true) do
    trace[tutorial] "the goal is {← getMainGoal}"  -- now this prints
  evalTactic (← `(tactic| trivial))

example : True := by noisy_seen                     -- Infoview shows: [tutorial] the goal is ⊢ True

/-! ### §5.8  ⚑ TRAP #13: BACKTRACKING.  Exceptions do NOT restore state.

This is the one place where meta-programming violates a mathematician's instinct,
so slow down.  You expect that if a tactic fails, everything it did is undone,
because in mathematics a failed attempt leaves no trace.  That is FALSE here, and
the reason is how the state is stored.

Lean's metavariable assignments (the `MetavarContext`) live in a single *mutable
reference* threaded through the computation, not in a value that unwinds as an
exception propagates.  (This sharpens §0.4(h): that `State → (α, State)` value
picture is a useful simplification, and the metavariable table is exactly the part
it simplifies away.  Because `isDefEq` assigns holes as a side effect from deep
inside nested calls, Lean keeps that table in one shared mutable cell, the §2.2 side
table, rather than threading it through every return.  A `throw` unwinds the call
stack and abandons the *value* half of the state, but does not revert edits already
written to that shared cell.  Control unwinds; the side table does not.)  Picture a
shared whiteboard: assigning a metavariable writes
on the board.  If a tactic writes on the board and *then* throws, the throw stops
execution but the writing STAYS on the board; nothing wipes it.  So a plain
`try ... catch ...` catches the failure but does NOT undo the half-finished
assignments, and using it as if it were backtracking produces bugs that are
genuinely miserable to track down.  Watch an assignment survive a caught throw: -/

#eval show MetaM Unit from do
  let m ← mkFreshExprMVar (some (.const ``Nat [])) (userName := `m)
  try
    m.mvarId!.assign (mkNatLit 5)      -- write on the whiteboard
    throwError "boom"                  -- then fall over
  catch _ => pure ()                   -- catch the fall
  logInfo m!"survived the throw: value = {← instantiateMVars m}, hole? = {(← instantiateMVars m).isMVar}"
  -- survived the throw: value = 5, hole? = false   ← the assignment STAYED

/-! The fix is to photograph the board and, on failure, redraw from the photo.
`Meta.saveState` takes the snapshot; `s.restore` rewinds to it: -/

#eval show MetaM Unit from do
  let m ← mkFreshExprMVar (some (.const ``Nat [])) (userName := `m)
  let s ← Meta.saveState               -- photograph the board
  try
    m.mvarId!.assign (mkNatLit 5)
    throwError "boom"
  catch _ => s.restore                 -- failed: redraw from the photo
  logInfo m!"after saveState/restore: hole? = {(← instantiateMVars m).isMVar}"
  -- after saveState/restore: hole? = true   ← rolled back

/-! These two helpers wrap that save/restore pattern, and are used all through the
capstone in Ch6: -/

/-- Run `x`; if it fails, roll the state back completely and run `y` instead. -/
def orElseRestore {α : Type} (x : MetaM α) (y : Unit → MetaM α) : MetaM α := do
  let s ← Meta.saveState               -- photograph the whiteboard
  try
    x
  catch _ =>
    s.restore                          -- failed: wipe and redraw from the photo
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
You rarely have to write this dance yourself: Lean provides `withoutModifyingState`,
`commitWhen`, and the syntactic combinators you already use, `first | t₁ | t₂`,
`try t`, `repeat t`, `all_goals t`, `any_goals t`, `focus t`.  Every one of them
does the save/restore internally.  But when you build a search by hand, as we do
next in the capstone, you must do it yourself, and forgetting is Trap 13.

Next: Chapter 6 assembles everything here into `mytauto`, a real backtracking
prover, and this save/restore discipline is exactly what makes its search correct.
-/
