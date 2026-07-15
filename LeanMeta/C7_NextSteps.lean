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
    set_option pp.all true            -- show EVERYTHING: implicits, universes, coercions
    set_option pp.explicit true       -- just the implicit arguments
    set_option pp.notation false      -- no notation: see `HAdd.hAdd a b`, not `a + b`
    set_option pp.fullNames true
    set_option trace.Meta.isDefEq true   -- watch unification happen (VERY noisy)
    set_option trace.Elab.step true      -- watch elaboration happen (VERY noisy)
    #print foo / #print axioms foo       -- what did my tactic actually produce?
    Lean.Meta.check e                    -- type-check an Expr I built by hand
    dbg_trace / logInfo / trace[myclass] -- printf debugging, in increasing order of taste
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
  * `Aesop`: Mathlib's extensible proof-search engine.  Before writing a big
    search tactic, ask whether you actually want an Aesop rule set instead.
  * *Extensible* tactics: study how `@[simp]`, `@[norm_num]` and `@[positivity]`
    let users register new cases via attributes and environment extensions.  This
    is the pattern you want for any tactic that must grow with a library.
  * The Zulip stream `#lean4 > metaprogramming`: where these questions get
    answered.

§7.5  A closing word of advice
------------------------------
Write the `MetaM` core first, test it with `#eval`, and only then wrap it in
syntax.  Keep a `trace[...]` class in your tactic from day one.  And whenever
something inexplicable happens, the answer is almost always one of:
`instantiateMVars`, `withContext`, or a state you forgot to restore.
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
  check e                               throwTacticEx `tac goal m!"..."

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
