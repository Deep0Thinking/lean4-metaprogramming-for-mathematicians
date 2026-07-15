import Lean
/-!
# Chapter 2. `MetaM`: metavariables, contexts, and what a goal really is

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

Chapter 1 said a tactic builds an `Expr` whose type is the goal.  The catch is
that it builds that term *incrementally*, leaving holes for the parts it has not
constructed yet.  This chapter is about those holes (metavariables), about the
hypotheses available to fill them (the local context), and about the one
identification that the entire subject rests on: **a goal is a metavariable**.
Once that clicks, every tactic looks the same: a structured way to fill a hole.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§2.  `MetaM`: METAVARIABLES, CONTEXTS, AND WHAT A GOAL REALLY IS
--------------------------------------------------------------------------------

§2.1  The local context: your hypotheses
-----------------------------------------
When you prove `h : p ⊢ q`, the `h : p` on the left is the *local context*: the
list of named, typed local variables you are allowed to use.  Internally each is a
free variable (`.fvar` from §1), and the context (`LocalContext`) maps its id
(`FVarId`) to a `LocalDecl` recording its user name, its type, and its value if it
came from a `let`.  Your hypotheses are exactly this list.

Here is the subtlety that costs everyone an afternoon.  A free variable is, on its
own, just an opaque id like `_uniq.1234`; everything meaningful about it (its name,
its type) lives in the local context.  So an `Expr` that mentions `h` is only
meaningful *relative to a context that declares `h`*.  It is the same as in
ordinary mathematics: a symbol introduced by "let h be a proof of p" is meaningless
once you step outside that argument.

⚑ TRAP #7, and you WILL hit it: if you `inferType` (or otherwise inspect) an
expression mentioning `h` while you are not "inside" the goal that declares `h`,
you get the dreaded

        unknown free variable '_uniq.1234'

The fix is always the same: step into the goal's world first, with
`goal.withContext do ...` (or, in `TacticM`, `withMainContext do ...`); each goal
carries its own context table, so you must enter the right one.  When in doubt,
wrap.  (`MVarId`, used just below, is a *handle to a goal*, that is, to one of the
holes we meet in §2.2; §2.3 explains why a goal just *is* a hole.  For now read
`MVarId` as "a goal" and `.withContext` as "step inside that goal".)  The function
below both prints the hypotheses and shows the pattern: -/

/-- Print every hypothesis of a goal. -/
def printHypotheses (goal : MVarId) : MetaM Unit :=
  goal.withContext do                        -- ← §2.1: step into the goal's context (MANDATORY)
    for ldecl in ← getLCtx do                -- getLCtx : the local context, iterable
      if ldecl.isImplementationDetail then continue   -- skip machine-generated entries
      logInfo m!"{ldecl.userName} : {ldecl.type}"

elab "print_hyps" : tactic => do printHypotheses (← getMainGoal)

example (n : Nat) (h : n > 0) (hh : n ≠ 0) : True := by
  print_hyps                                 -- prints  n : Nat,  h : n > 0,  hh : n ≠ 0
  trivial

/-! ### §2.2  Metavariables: the holes you leave and later fill

Why do these exist at all?  Because you cannot write a whole proof term in one
breath; you build it top-down, and wherever a piece is not ready yet you leave a
*hole*.  A **metavariable** is exactly such a hole, but a well-labelled one: it
carries the *type* that must eventually fill it and the *local context* available
for filling it.  Written `?m`.

The analogy a mathematician already owns: it is the "solve for the unknown `x`" of
a computation, or a numbered blank in a fill-in-the-blank proof.  You know what
*kind* of thing goes in the blank (its type) and what you may use to produce it
(its context); you just have not determined the value yet.  (One honest disanalogy:
unlike a numeric unknown, a proof-hole has no *unique* solution; any term of the
right type will do.  The analogy is about the hole's role, not a unique value.)

Two things you can do with a hole: read off its type and context, and eventually
*assign* it a term (plug the hole).  Crucially, assignment is recorded in a
separate side table (the `MetavarContext`); it does NOT rewrite the `Expr` you are
holding.  Watch both facts at once: -/

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
Who fills these holes in practice?  Often *unification* does, automatically.
Recall from §1.4 that `isDefEq` may assign metavariables as a side effect: making
`?m` and `5` definitionally equal just IS assigning `?m := 5`.  This is why
`apply`, `exact`, and `rw` can leave you fewer goals than you expected; matching
against the goal solved some holes for you.

⚑ TRAP #8: Assigning a metavariable does NOT rewrite the `Expr` you are holding.
The assignment lives in the side table; your `Expr` still contains the raw `.mvar`
node, as `m.isMVar` showed above.  There is a catch that fools everyone:
pretty-printing (`m!` / `logInfo` / the delaborator) instantiates mvars for
*display*, so the SCREEN shows `5` and the problem stays invisible.  But any time
YOUR code inspects an `Expr`'s shape (a `match`, `getAppFnArgs`, `.eq?`, an
`isDefEq` comparison), it sees the un-instantiated hole.  So the rule is: call
`instantiateMVars` before you take an `Expr` apart or compare it, not merely before
you print it.  (`instantiateMVars e` is just *substitution*: it walks `e` and
replaces every assigned metavariable by its value, the same move as plugging a
solved unknown back into a formula.  This is why real tactics call it at the top,
as `myRflCore` does in §5.2.)

§2.3  A GOAL IS A METAVARIABLE
------------------------------
Here is the payoff, the single identification the rest of the tutorial is built on.

Recall the job of a `by` block: produce a proof term whose type is the goal
(Curry-Howard, Chapter 0).  It does not produce that term all at once.  It starts
life as a single hole:

    the goal   `h : p ⊢ q`
      is literally stored as
    a metavariable `?g` whose TYPE is `q` and whose LOCAL CONTEXT holds `h : p`.

So the thing you stare at in the Infoview as "the goal" *is* a metavariable: the
Infoview simply renders it, with its local context shown above the `⊢` and its
type below.  And now every tactic is the same move, filling that hole:

    to CLOSE the goal  =  assign `?g` a complete term of type `q` (no holes left)
    to make SUBGOALS   =  assign `?g` a term that still contains fresh holes;
                          each new hole is a new metavariable, and those are
                          exactly the goals you see next.

The tactic state is nothing more than the list of metavariables not yet assigned:
the very list of goals you watch in the Infoview, each open goal one unfilled hole,
and closing goals is that list shrinking toward empty.
`by` creates the first one and hands it to your tactic block; `rfl` and `exact`
assign it outright; `constructor` and `apply` assign it a term with fresh holes,
which become your next goals.

You can act this out by hand, with no `by` in sight.  First the simplest case,
closing a goal: make a hole of type `True`, plug it with `True.intro`, done.  This
is exactly what `by trivial` does under the hood: -/

#eval show MetaM Unit from do
  let goal ← mkFreshExprMVar (some (.const ``True [])) (userName := `goal)
  logInfo m!"the goal  : {goal} : {← inferType goal}"    -- ?goal : True
  goal.mvarId!.assign (.const ``True.intro [])           -- "prove" it: plug the hole
  logInfo m!"the proof : {← instantiateMVars goal}"      -- True.intro

/-! And here is the other half, *producing a subgoal*: fill the goal with a term
that itself contains a fresh hole, and watch that hole become a new goal.  This is,
in miniature, what `apply` does. -/

#eval show MetaM Unit from do
  let g ← mkFreshExprMVar (some (.const ``Nat [])) (userName := `g)  -- goal: produce a Nat
  let h ← mkFreshExprMVar (some (.const ``Nat [])) (userName := `h)  -- a fresh hole
  g.mvarId!.assign (← mkAppM ``Nat.succ #[h])            -- fill g with `h.succ`; h stays open
  logInfo m!"proof so far    : {← instantiateMVars g}"   -- Nat.succ ?h
  logInfo m!"new subgoal (h) : {← h.mvarId!.getType}"    -- Nat
  logInfo m!"h assigned yet? : {← h.mvarId!.isAssigned}" -- false   (h is a real, open goal)

/-! The everyday experience is `constructor` splitting one goal into *two*.  Same
move, now with a two-holed term.  Watch the goal count go from 1 to 2: -/

#eval show MetaM Unit from do
  let goalType ← mkAppM ``And #[.const ``True [], .const ``True []]   -- goal: True ∧ True
  let g ← mkFreshExprMVar (some goalType) (userName := `g)
  let a ← mkFreshExprMVar (some (.const ``True [])) (userName := `a)  -- fresh hole 1
  let b ← mkFreshExprMVar (some (.const ``True [])) (userName := `b)  -- fresh hole 2
  g.mvarId!.assign (← mkAppM ``And.intro #[a, b])        -- one hole in, a TWO-holed term out
  logInfo m!"proof so far : {← instantiateMVars g}"      -- ⟨?a, ?b⟩   (`And.intro a b`, in ⟨⟩ form)
  logInfo m!"subgoal 1    : {← a.mvarId!.getType}  (open? {! (← a.mvarId!.isAssigned)})"  -- True  (open? true)
  logInfo m!"subgoal 2    : {← b.mvarId!.getType}  (open? {! (← b.mvarId!.isAssigned)})"  -- True  (open? true)

/-
So filling a hole with a term that itself carries holes is what *creates* goals:
`Nat.succ ?h` left one, `And.intro ?a ?b` left two (`?a` and `?b`), exactly the
pair `constructor` hands you.  (Those `?a`, `?b` are just holes; the auto-updating
*goal list* you watch in the Infoview lives one layer up, in `TacticM` (§5).  Here
in raw `MetaM` we read openness by hand with `isAssigned`.)  That is the entire
mechanism.  `apply`, `intro`, `cases`, and the rest (§2.4) are convenient
*verbs* that assign the goal metavariable in structured ways and hand you back
whatever holes they left open.

⚑ TRAP #9: `MVarId.assign` does NOT type-check what you give it.  It is a raw
store, so if you assign a term of the wrong type you get no complaint here; the
error surfaces much later, from the kernel, with a confusing message far from the
real mistake.  When debugging a proof-producing tactic, run `Lean.Meta.check e` on
the term you built (that catches an internally ill-typed term, though a mere type
*mismatch with the goal* still only bites later, when the hole is used), or
`#print axioms` on the resulting theorem.

§2.4  The `MVarId` API = the real tactic API
--------------------------------------------
These are the actual primitives: the structured "verbs" from §2.3 that assign a
goal metavariable and return the new ones.  Every tactic you know is built from
them, so this list is worth real time.  Ctrl-click each one and read the source;
that is the fastest way to learn.  (`#check @f` prints the full type of `f`,
implicit arguments and all.) -/

#check @Lean.MVarId.getType        -- the target (the type of the goal metavariable)
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

/-
Next, Chapter 3 turns to the OTHER language, `Syntax`, and how you give your tactic
a surface notation for users to type.
-/
