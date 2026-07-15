import Lean
/-!
# Chapter 7. Debugging, testing, where to go next, and reference

Part of **Lean 4 Metaprogramming for Mathematicians**.  This chapter closes the
tutorial with a debugging toolbox, advice on reading Lean's source, a one-page
cheat sheet, and a glossary.  The exercises live in `Exercises/` (with worked
answers in `Solutions/`).
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§7.  DEBUGGING, TESTING, AND WHERE TO GO NEXT
--------------------------------------------------------------------------------

§7.1  The debugging toolbox
---------------------------
You know your SYMPTOM, not (yet) your tool.  So start here: find the symptom, apply
the reflex.  All of these are traps this tutorial already met; the pointer says
where.

  SYMPTOM you see                          CAUSE                       REFLEX
  ----------------------------------------------------------------------------------
  a term prints `?m.5` / `?m.N`,           you hold the pre-           `instantiateMVars e`
    or a `match`/`.eq?` unexpectedly       substitution `Expr`;         BEFORE any match /
    fails                                  the mvar is assigned         `.eq?` / compare
                                           in a side table (Trap 8)
  `unknown free variable '_uniq.N'`        you inspected an fvar        wrap in
                                           outside the goal that        `goal.withContext` /
                                           declares it (Trap 7)         `withMainContext`
  an assignment / hypothesis survived      a `throw` does NOT undo      bracket with
    a failed or caught branch              metavariable assignments     `Meta.saveState` /
                                           (Trap 13)                    `s.restore` (or a
                                                                        combinator, §A)
  kernel error far from where you built    `goal.assign` is             `Lean.Meta.check e`
    the term ("motive is not type          UNCHECKED; you stored an     at build time;
    correct", "has metavariables")         ill-typed `Expr` (Trap 9)    `#print axioms foo`
  `isDefEq` returns `false` when you are    not unfolded enough         `whnf e` first, or
    sure it should hold                                                 raise transparency
  two `Expr`s print identically but        a hidden implicit /          `set_option pp.all
    will not unify                         universe / coercion          true`, then
                                           differs                      `trace.Meta.isDefEq`
  your tactic silently never fires         a one-backtick `` `name ``   use the checked
                                           typo, an unresolved raw      two-backtick
                                           `Name` (Trap 3)              `` ``name ``

Raw options behind the reflexes (each with WHEN to reach for it):

    set_option pp.all true          -- everything: implicits, universes, coercions.
                                    --   WHEN: two terms print the same but won't unify.
    set_option pp.explicit true     -- just the implicit/instance args.
                                    --   WHEN: you suspect a wrong instance is inserted.
    set_option pp.notation false    -- `HAdd.hAdd a b`, not `a + b`.
                                    --   WHEN: to see which operation/instance really runs.
    set_option pp.fullNames true    -- fully-qualified names.
                                    --   WHEN: an `open` makes `succ` ambiguous; confirm `Nat.succ`.
    set_option trace.Meta.isDefEq true  -- watch unification (VERY noisy).
                                        --   WHEN: an apply/exact/isDefEq mysteriously (mis)fires.
    set_option trace.Elab.step true     -- watch elaboration (VERY noisy).
    #print foo / #print axioms foo      -- what did my tactic actually produce, and on what axioms?
    Lean.Meta.check e                   -- type-check an `Expr` I built by hand.
    dbg_trace / logInfo / trace[myclass]-- printf debugging, in increasing order of taste.

(`#help option pp` lists the rest of the pretty-printer switches.)
-/

set_option pp.all true in
#check (2 + 2 = 4)                   -- @Eq Nat (@HAdd.hAdd Nat Nat Nat ...) ...

/-
§7.2  Testing your tactics
--------------------------
Write `example`s.  They are your unit tests, and they break loudly when Lean
changes.  A test that a tactic *fails* should be a commented-out `example` with a
note (Lean core also has `#guard_msgs`, which pins a tactic's exact output; look
it up once you need it).  The `Solutions/` files in this project are exactly this
kind of test suite.

But test the `MetaM` *core* even before you have any syntax, with `#eval`: build a
goal by hand, run the core on it, and instantiate to read the result.  This is the
build / run / read pattern from Chapters 2 and 5, and the reason to write the core
first (§7.5): -/

#eval show MetaM Unit from do
  let g ← mkFreshExprMVar (some (mkConst ``Nat))   -- a goal: produce a `Nat`
  g.mvarId!.assign (mkNatLit 7)                    -- or: `myCore g.mvarId!`
  logInfo m!"{← instantiateMVars g}"               -- 7

/-
§7.3  How to find things (this is the real skill)
-------------------------------------------------
  1.  Ctrl-click / F12 on ANY identifier in this project.  You land in Lean's
      source.  Read it.  This is by far the highest-bandwidth way to learn.
  2.  The source lives in your toolchain, at roughly
          ~/.elan/toolchains/<version>/src/lean/
      The files you will actually want:
          Lean/Expr.lean                  -- the Expr type and its API
          Lean/Meta/Basic.lean            -- MetaM, whnf, isDefEq, telescopes
          Lean/Meta/Tactic/*.lean         -- Apply, Intro, Cases, Assumption, Rewrite,
                                          --   Subst, Simp/*   ← the real tactic logic
          Lean/Elab/Tactic/Basic.lean     -- TacticM, evalTactic, the combinators
          Lean/Elab/Tactic/*.lean         -- the syntactic front ends (e.g. `evalApply`
                                          --   for `apply` lives in ElabTerm.lean)
          Init/Tactics.lean               -- the *syntax* of the core tactics
      In Mathlib: `Mathlib/Tactic/`, hundreds of readable, real examples.
  3.  Pick a small real tactic and read it end to end.  Good first victims:
      `Lean/Meta/Tactic/Assumption.lean` (tiny), then `Apply.lean`, then Mathlib's
      `Mathlib/Tactic/Use.lean` or `Mathlib/Tactic/Cases.lean`.

§7.4  Next steps, in the order I would take them
------------------------------------------------
  * "Metaprogramming in Lean 4" (the community book): the canonical long-form
    treatment; this tutorial is a compressed, tactic-focused path through it.
  * `Qq` (already a Mathlib dependency): type-safe `Expr` quotations.  Instead of
    `mkAppM ``Nat.add #[a, b]` you write `q($a + $b)` and Lean *type-checks the
    Expr you are building*.  Once your tactic outgrows a page, switch to Qq.
  * `Aesop`: Mathlib's extensible proof-search engine.  The safe-move-first,
    guess-and-backtrack search you wrote by hand in `mytauto` (Ch6) IS Aesop's
    model, safe vs unsafe rules, priorities, backtracking, all provided.  Reach for
    it instead of hand-rolling when the *rules* must grow with a library (each
    lemma registered via `@[aesop]`) rather than being a fixed handful baked into
    one `core` loop.
  * *Extensible* tactics: study how `@[simp]`, `@[norm_num]` and `@[positivity]`
    let users register new cases via attributes and environment extensions.  This
    is the pattern you want for any tactic that must grow with a library.
  * The Zulip stream `#lean4 > metaprogramming`: where these questions get
    answered.

§7.5  A closing word of advice
------------------------------
Write the `MetaM` core first, test it with `#eval` (§7.2), and only then wrap it in
syntax.  Keep a `trace[...]` class in your tactic from day one.  And when something
inexplicable happens, read it as a symptom (§7.1):

    prints `?m.N`             →  you forgot `instantiateMVars`
    `unknown free variable`   →  you forgot `withContext`
    state survived a failure  →  you forgot to `saveState` / `restore`

Those three account for most of the afternoons you would otherwise lose.
-/

/-
--------------------------------------------------------------------------------
§A.  CHEAT SHEET
--------------------------------------------------------------------------------
BUILDING Expr                        INSPECTING Expr
  mkConst n / mkConstWithFreshMVarLevels n   e.getAppFnArgs : Name × Array Expr
  mkApp f a / mkAppN f #[...]                e.getAppFn / e.getAppArgs
  mkAppM ``f #[...]        (fills implicits) e.isForall / e.isApp / e.isConstOf n
  mkNatLit n / mkStrLit s                    e.eq? / e.arrow? / e.not?
  mkLambdaFVars #[x] b                       e.fvarId! / e.mvarId!
  mkForallFVars  #[x] b                      describeExpr e   (Chapter 1, §1.2)
  mkEq a b / mkEqRefl a / mkEqSymm h

MetaM                                 GOALS (MVarId)
  inferType e                           goal.getType
  whnf e / whnfR e / withReducible      goal.withContext do ...
  isDefEq a b            (unifies!)     goal.assign e            (unchecked!)
  instantiateMVars e     (DO IT)        goal.intro n / goal.intro1P
  getLCtx                               goal.apply e             → List MVarId
  withLocalDeclD n t k                  goal.assert n t v / goal.clear h
  forallTelescope / lambdaTelescope     goal.cases h             → Array CasesSubgoal
  mkFreshExprMVar (some t)              goal.constructor / goal.assumption
  Meta.saveState / s.restore            goal.checkNotAssigned `tac

TacticM                               SYNTAX
  getMainGoal / getGoals                `(term| ...)  `(tactic| ...)
  replaceMainGoal gs                    $x  $xs,*   (antiquotations)
  withMainContext do ...                stx.getId / stx.getNat / stx.raw
  liftMetaTactic f                      macro / macro_rules      (Syntax → Syntax)
  liftMetaFinishingTactic f             elab / elab_rules        (Syntax → Expr/action)
  elabTerm t none                       declare_syntax_cat
  elabTermEnsuringType t (some τ)       syntax:prec ... : cat
  evalTactic (← `(tactic| simp))        @[tactic myKind] def ... : Tactic
  setGoals / getGoals                   all_goals / focus  (as syntax)

BACKTRACKING  (Trap 13: a throw does NOT roll back mvar assignments)
  withoutModifyingState x   -- run x, ALWAYS discard its state changes
  observing? x              -- run x; on failure roll back and return `none`
  Meta.saveState / s.restore-- the manual form (photograph / redraw)
  first | t | t   try t   repeat t   -- (as syntax) roll back internally
  reflex: speculative run + rollback → `withoutModifyingState` / `observing?`

ERRORS / TRACES
  throwError m!"..."                    logInfo / logWarning
  throwTacticEx `tac goal m!"..."       indentExpr e     (Expr on its own line)
  withRef stx do ...  (blame the input) initialize registerTraceClass `c
                                        trace[c] "..."

WHEN IT BREAKS  (symptom → reflex; see §7.1 for the full table)
  prints ?m.N            → instantiateMVars e         (Trap 8)
  unknown free variable  → withMainContext / goal.withContext   (Trap 7)
  survived a throw       → saveState/s.restore or withoutModifyingState   (Trap 13)
  can't see the mismatch → set_option pp.all true
  kernel rejects my term → Lean.Meta.check e          (Trap 9)
  what did I build?      → #print foo / #print axioms foo

RUNNING / TESTING a MetaM core, no `by` needed
  #eval show MetaM Unit from do
    let g ← mkFreshExprMVar (some t); myCore g.mvarId!; logInfo m!"{← instantiateMVars g}"
--------------------------------------------------------------------------------

§D.  GLOSSARY
--------------------------------------------------------------------------------
  Elaboration    Turning `Syntax` into `Expr`, inserting implicits, coercions,
                 instances, and running tactics.
  Expr           The kernel's language.  Proof terms are `Expr`s.
  fvar           Free variable = a hypothesis in the local context.
  bvar           Bound variable, by de Bruijn index.  Never handle these directly.
  mvar           Metavariable = a hole.  A GOAL IS A METAVARIABLE.
  Local context  The hypotheses available in a given goal.
  defeq          Definitional equality: equal after computation.  `isDefEq` decides
                 it (and unifies metavariables while doing so).
  whnf           Weak-head normal form: unfold until the outermost symbol is
                 rigid.  The workhorse of goal matching.
  Transparency   How aggressively defeq/whnf unfold: reducible ⊂ instances ⊂
                 default ⊂ all.
  Telescope      A chain of binders; `forallTelescope` / `lambdaTelescope` open
                 them all into fvars for you.
  Hygiene        Macro-introduced names cannot capture user names, and vice versa.
  Backtracking   A `throw` does NOT undo metavariable assignments (the state is a
                 shared mutable table); roll back with `saveState`/`restore` or
                 `withoutModifyingState`/`observing?`.
  Monad          The "kind of computation" a `do` block builds; each meta monad
                 (`CoreM`/`MetaM`/`TermElabM`/`TacticM`) threads more of Lean's
                 state.  `←` runs a computation; `:=` binds a plain value.
  Syntax         The parse tree.  `TSyntax c` is a parse tree of category `c`.
  Kind           The `Name` tagging a `Syntax` node; what elaborators dispatch on.
  MetaM          The monad with the local context and metavariables.  Write your
                 logic here.
  TacticM        The monad with the goal list.  Write only your front end here.
================================================================================
-/
