import Lean
/-!
# Chapter 2. `MetaM`: metavariables, contexts, and what a goal really is

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§2.  `MetaM`: METAVARIABLES, CONTEXTS, AND WHAT A GOAL REALLY IS
--------------------------------------------------------------------------------

§2.1  The local context
-----------------------
Free variables (`.fvar`) are entries in the *local context* (`LocalContext`), a
map from `FVarId` to a `LocalDecl` (user name, type, value if it is a `let`).
Your hypotheses are exactly this.

⚑ TRAP #7, and you WILL hit it: an `Expr` only makes sense relative to a local
context.  If you try to `inferType` an expression mentioning `h` while you are
not "inside" the goal that declares `h`, you get the dreaded

        unknown free variable '_uniq.1234'

The fix is always the same: wrap your work in `goal.withContext do ...`
(or, in `TacticM`, `withMainContext do ...`).  When in doubt, wrap.
-/

/-- Print every hypothesis of a goal. -/
def printHypotheses (goal : MVarId) : MetaM Unit :=
  goal.withContext do                        -- ← §2.1: MANDATORY
    for ldecl in ← getLCtx do                -- getLCtx : the local context, iterable
      if ldecl.isImplementationDetail then continue   -- skip machine-generated ones
      logInfo m!"{ldecl.userName} : {ldecl.type}"

elab "print_hyps" : tactic => do printHypotheses (← getMainGoal)

example (n : Nat) (h : n > 0) (hh : n ≠ 0) : True := by
  print_hyps                                 -- prints  n : Nat,  h : n > 0,  hh : n ≠ 0
  trivial

/-! ### §2.2  Metavariables: the holes

A metavariable is a named hole `?m` with a type and a local context.  It may be
*assigned* an `Expr`.  Assignment is recorded in a global `MetavarContext`. -/

#eval show MetaM Unit from do
  let m ← mkFreshExprMVar (some (.const ``Nat [])) (userName := `m)
  logInfo m!"fresh hole      : {m}"                              -- ?m
  logInfo m!"its type        : {← inferType m}"                 -- Nat
  m.mvarId!.assign (mkNatLit 5)
  -- The raw `Expr` in `m` is UNCHANGED by the assignment: structurally it is
  -- still a metavariable node.  `instantiateMVars` is what applies the assignment.
  logInfo m!"still a hole?   : {m.isMVar}"                       -- true   ← unchanged!
  logInfo m!"after instMVars : {(← instantiateMVars m).isMVar}" -- false  ← now it's `5`
  logInfo m!"but printing m  : {m}"                             -- 5   (display auto-instantiates)

/-
⚑ TRAP #8: Assigning a metavariable does NOT rewrite the `Expr` you are holding.
The assignment lives in a side table (the `MetavarContext`); your `Expr` still
contains the raw `.mvar` node, as `m.isMVar` showed above.  There is a catch that
fools everyone: pretty-printing (`m!` / `logInfo` / the delaborator) instantiates
mvars for *display*, so the SCREEN shows `5` and the problem stays invisible.  But
any time YOUR code inspects an `Expr`'s shape (a `match`, `getAppFnArgs`, `.eq?`,
an `isDefEq` comparison), it sees the un-instantiated hole.  So the rule is: call
`instantiateMVars` before you take an `Expr` apart or compare it, not merely before
you print it.  (This is why real tactics call it at the top, as `myRflCore` does in
§5.2.)

§2.3  A GOAL IS A METAVARIABLE
------------------------------
This is the central identification of the whole subject:

    goal   `h : p ⊢ q`
      =
    a metavariable `?g` whose TYPE is `q` and whose LOCAL CONTEXT contains `h : p`

    "proving the goal"   =   "assigning `?g` a term of type `q`"
    "producing subgoals" =   "assigning `?g` a term containing NEW metavariables"

The tactic state is just: a list of metavariable ids that are not yet assigned.
`by` creates one such metavariable and hands it to your tactic block.

Here is a proof, constructed by hand, with no `by` in sight: -/

#eval show MetaM Unit from do
  let goal ← mkFreshExprMVar (some (.const ``True [])) (userName := `goal)
  logInfo m!"the goal  : {goal} : {← inferType goal}"    -- ?goal : True
  goal.mvarId!.assign (.const ``True.intro [])           -- "prove" it
  logInfo m!"the proof : {← instantiateMVars goal}"      -- True.intro

/-
⚑ TRAP #9: `MVarId.assign` does NOT type-check what you give it.  It is a raw
store.  If you assign junk, you get an error much later, from the kernel, with a
confusing message.  When debugging a proof-producing tactic, run
`Lean.Meta.check e` on your term, or `#print axioms` on the resulting theorem.

§2.4  The `MVarId` API = the real tactic API
--------------------------------------------
These are the actual primitives.  Every tactic you know is built from them.
Ctrl-click each one and read the source; this is the fastest way to learn.
(`#check @f` prints the full type of `f`, implicit arguments and all.) -/

#check @Lean.MVarId.getType        -- the target
#check @Lean.MVarId.withContext    -- enter the goal's local context
#check @Lean.MVarId.assign         -- close the goal with a term (unchecked!)
#check @Lean.MVarId.intro          -- `intro x`
#check @Lean.MVarId.intro1P        -- intro one hyp, keeping the binder's own
                                   --   (accessible) name.  (`MVarId.intro1` instead
                                   --   gives it an inaccessible name, as `intro _` does.)
#check @Lean.MVarId.apply          -- `apply e`      → new goals
#check @Lean.MVarId.assert         -- `have h : t := v`
#check @Lean.MVarId.clear          -- `clear h`
#check @Lean.MVarId.cases          -- `cases h`      → one goal per constructor
#check @Lean.MVarId.assumption     -- `assumption`
#check @Lean.MVarId.constructor    -- `constructor`
#check @Lean.MVarId.rewrite        -- the engine of `rw`
#check @Lean.Meta.mkFreshExprMVar  -- make a new hole (= a new goal)
