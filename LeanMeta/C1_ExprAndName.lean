import Lean
/-!
# Chapter 1. `Name` and `Expr`: the language the kernel speaks

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§1.  `Name` AND `Expr`
--------------------------------------------------------------------------------

§1.1  Names
-----------
`Name` is a list of components: `Nat.succ` is `Name.str (Name.str .anonymous "Nat") "succ"`.
There are two quotation forms, and the difference matters:

    `foo.bar     -- ONE backtick: a raw Name literal.  Not checked.  Might not exist.
    ``Nat.succ   -- TWO backticks: resolved and CHECKED at compile time,
                 --                and expanded to the full name.

⚑ TRAP #3: always prefer two backticks when you mean an existing constant.  With
one backtick, a typo (`` `Nat.suc ``) silently produces a name that resolves to
nothing, and your tactic mysteriously never fires.

(In `#eval`, a `Name` prints back with a leading backtick, e.g. `` `Nat.succ ``.
That backtick is just how `Name` displays; it is not part of the name.)
-/

#eval `foo.bar               -- `foo.bar         (no check performed)
#eval ``Nat.succ             -- `Nat.succ        (checked: the constant exists)
-- #eval ``Nat.suckzess      -- ✗ compile error: unknown identifier.  Good!

/-! ### §1.2  `Expr`, the core language

Everything Lean *means* (every term, every type, every proof) is an `Expr`.
Look at the real definition (put your cursor on the next line): -/

#print Lean.Expr

/-
The twelve constructors, in plain words:

    .bvar   i           -- bound variable, by de Bruijn INDEX (see §1.3)
    .fvar   id          -- free variable = a hypothesis in the local context
    .mvar   id          -- metavariable  = a HOLE.  Goals are these.
    .sort   u           -- `Prop`, `Type`, `Type 1`, ...  (u is a universe level)
    .const  n us        -- a declared constant, e.g. `Nat.add`, with universe args
    .app    f a         -- application, always ONE argument at a time: f a
    .lam    x t b bi    -- fun (x : t) => b
    .forallE x t b bi   -- (x : t) → b     -- also how `t → b` and `∀ x, b` are stored!
    .letE   x t v b _   -- let x : t := v; b
    .lit    l           -- a literal: 37, "hi"
    .mdata  d e         -- metadata attached to e; semantically invisible
    .proj   S i e       -- projection: the i-th field of structure S out of e

⚑ TRAP #4: `p → q` is NOT a separate constructor.  It is `.forallE _ p q _` with
a body that ignores the binder.  Likewise `¬p` is not a constructor: it is the
constant `Not` applied to `p` (and it *unfolds* to `p → False`).

⚑ TRAP #5: application is unary.  `f a b` is `.app (.app f a) b`.  Use
`Expr.getAppFn` / `getAppArgs` / `getAppFnArgs` instead of peeling by hand.

Let us make the tree visible.  This function is your microscope.  It is a plain
recursive function that matches on each constructor (see §0.4(c)); read it as a
catalogue of the twelve cases. -/

/-- A crude structural printer for `Expr`.  Universe levels are elided. -/
def describeExpr : Expr → String
  | .bvar i           => s!"bvar {i}"
  | .fvar id          => s!"fvar {id.name}"
  | .mvar id          => s!"mvar {id.name}"
  | .sort _           => "sort"
  | .const n _        => s!"const {n}"
  | .app f a          => s!"app ({describeExpr f}) ({describeExpr a})"
  | .lam n t b _      => s!"lam {n} : ({describeExpr t}) => ({describeExpr b})"
  | .forallE n t b _  => s!"forallE {n} : ({describeExpr t}) → ({describeExpr b})"
  | .letE n t v b _   => s!"letE {n} : ({describeExpr t}) := ({describeExpr v}); ({describeExpr b})"
  | .lit (.natVal n)  => s!"lit {n}"
  | .lit (.strVal s)  => s!"lit {s}"
  | .mdata _ e        => s!"mdata ({describeExpr e})"
  | .proj S i e       => s!"proj {S} {i} ({describeExpr e})"

/-! ### §1.3  de Bruijn indices

Bound variables carry no names, only *indices*: `.bvar 0` means "the variable
bound by the nearest enclosing binder", `.bvar 1` the next one out, and so on.
The `Name` stored in `.lam`/`.forallE` is a *display hint only*. -/

#eval show MetaM Unit from do
  -- fun (x : Nat) => x     : the body is `.bvar 0`, i.e. "the nearest binder"
  let idNat : Expr := .lam `x (.const ``Nat []) (.bvar 0) .default
  logInfo m!"{idNat}"                       -- fun x => x
  logInfo (describeExpr idNat)              -- lam x : (const Nat) => (bvar 0)

  -- fun (x : Nat) => fun (y : Nat) => x        ← note the 1, not 0
  let konst : Expr :=
    .lam `x (.const ``Nat [])
      (.lam `y (.const ``Nat []) (.bvar 1) .default) .default
  logInfo m!"{konst}"                       -- fun x y => x
  logInfo (describeExpr konst)              -- lam x : ... => (lam y : ... => (bvar 1))

/-
⚑ TRAP #6: THE classic beginner bug.  A `.bvar` that is not underneath its
binder is a *loose* bound variable, and it is nonsense.  You must never build an
`Expr` by taking the body of a `.lam` and using it on its own.

The cure, and the idiom you will use forever: never touch `.bvar` yourself.
Instead, open the binder into a fresh *free* variable, work with that, and close
it again.  In `MetaM`:

    withLocalDeclD name type  fun x => ...   -- open: gives you a free variable `x`
    mkLambdaFVars #[x] body                  -- close: abstracts `x` back to a bvar

This open / work / close idiom is how you safely operate under a binder.  (To open
*several* nested binders at once you will later reach for `lambdaTelescope` /
`forallTelescope`; a *telescope* is the whole chain of binders; see the §D
glossary.)  Watch, and note that `x` here is an honest `Expr` (a free variable)
you can pass around, with no index arithmetic: -/

#eval show MetaM Unit from do
  let e ← withLocalDeclD `x (.const ``Nat []) fun x => do
    -- inside here, `x` is an honest free variable; no index arithmetic
    let body ← mkAppM ``Nat.add #[x, mkNatLit 1]
    mkLambdaFVars #[x] body                     -- re-binds `x` correctly
  logInfo m!"{e}"                               -- fun x => x.add 1   (i.e. fun x => x + 1)
  logInfo m!"{← inferType e}"                   -- Nat → Nat

/-! Note the printer shows `x.add 1`, not `x + 1`: we built the raw constant
`Nat.add` rather than the `+` notation, and the pretty-printer echoes that.  They
are the same function; only the display differs.

### §1.4  Building expressions

Prefer these helpers over raw constructors; they insert implicit arguments,
universe levels and instances for you.

One builder you will meet in §6 and §C deserves a word now:
`mkConstWithFreshMVarLevels ``c` makes the constant `c` with *fresh universe-level
metavariables* filled in, so that later unification can solve them.  Reach for it
instead of `.const ``c []` whenever `c` might be universe-polymorphic (e.g.
`False.elim : {C : Sort u} → False → C`, or `Exists.intro`) where the empty level
list `[]` would be wrong.  It is simply the safe, general form of "name the
constant `c`". -/

#eval show MetaM Unit from do
  -- `mkAppM` looks up `Nat.add`, works out its implicit args, and applies it.
  let e ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
  logInfo m!"e            = {e}"                          -- Nat.add 2 3
  logInfo m!"type of e    = {← inferType e}"             -- Nat
  logInfo m!"whnf e       = {← whnf e}"                  -- 5   (it computed!)
  logInfo m!"2+3 =?= 5    : {← isDefEq e (mkNatLit 5)}"  -- true
  logInfo m!"2+3 =?= 6    : {← isDefEq e (mkNatLit 6)}"  -- false

/-
The three `MetaM` workhorses you just met, and which you will use in every
tactic you ever write:

    inferType e      : MetaM Expr    -- the type of e
    whnf     e       : MetaM Expr    -- weak-head normal form: unfold until the
                                     -- HEAD symbol is a constructor/binder
    isDefEq  a b     : MetaM Bool    -- definitional equality, up to computation
                                     -- ⚠ may ASSIGN metavariables as a side effect

`isDefEq` is unification, not just a test.  `isDefEq ?m 5` returns `true` *and*
assigns `?m := 5`.  This is the engine behind `apply`, `exact`, `rw`, everything.
(On failure it rolls its own state back, so a failed `isDefEq` is harmless.)

TRANSPARENCY.  How eagerly `whnf`/`isDefEq` unfold definitions is controlled by a
"transparency setting":  `.reducible` (only `@[reducible]` defs) ⊂ `.instances`
⊂ `.default` (everything except `@[irreducible]`) ⊂ `.all`.
    whnf   e             -- ambient setting (usually `.default`)
    whnfR  e             -- forced to `.reducible`
    withReducible do ... -- run a block at `.reducible`
Rule of thumb: matching on the *user's* goal shape → `.reducible`, so you do not
accidentally see through their definitions.  Deciding whether two things are
*really* equal → `.default`.
-/

/-! ### §1.5  Taking expressions apart

Never pattern-match a nested `.app` chain by hand.  Use `getAppFnArgs`: it splits
`f a b c` into the head `f` and the argument array `#[a, b, c]` in one step. -/

/-- Classify a proposition by its head symbol. -/
def analyse (e : Expr) : MetaM String := do
  match e.getAppFnArgs with          -- : Name × Array Expr
  | (``And, #[_, _])    => return "a conjunction  (And a b)"
  | (``Or,  #[_, _])    => return "a disjunction  (Or a b)"
  | (``Iff, #[_, _])    => return "an iff         (Iff a b)"
  | (``Not, #[_])       => return "a negation     (Not a)"
  | (``Eq,  #[_, _, _]) => return "an equation    (@Eq α lhs rhs)"
  | (``Exists, #[_, _]) => return "an existential (Exists p)"
  | _ =>
    if e.isForall then return "a ∀ / →  (forallE)"
    else if e.isConstOf ``True then return "True"
    else return "something else"

#eval show MetaM Unit from do
  logInfo (← analyse (← mkAppM ``And #[.const ``True [], .const ``False []]))  -- a conjunction
  logInfo (← analyse (← mkAppM ``Eq  #[mkNatLit 1, mkNatLit 1]))               -- an equation

/-! Note that `#[_, _]` above is a *pattern*: the array analogue of the `[]` and
`x :: _` list patterns from §0.4(d).  It matches an array of *exactly two*
elements (`#[_]` exactly one, `#[_, _, _]` exactly three); a wrong length simply
falls through to the next branch.  That length test is exactly what separates the
two-argument heads (`And`/`Or`/`Iff`, and `Exists` stored as `@Exists α p`) and
the one-argument `Not` from `Eq`, which carries three (`@Eq α lhs rhs`). -/

/-
Other useful destructors (all in `Lean.Expr`, all worth Ctrl-clicking):
    e.isForall  e.isLambda  e.isApp  e.isConstOf n  e.isFVar  e.isMVar
    e.getAppFn  e.getAppArgs  e.getAppNumArgs
    e.eq?    : Option (Expr × Expr × Expr)   -- (type, lhs, rhs)
    e.arrow? e.not? e.and?
    e.fvarId!  e.mvarId!                     -- partial; only after checking

The `?`-suffixed ones return `Option` (see §0.4(d)): `e.eq?` gives
`some (α, lhs, rhs)` if `e` is an equality, else `none`.  The `!`-suffixed ones
crash if you are wrong, so guard them with an `is...` check first.
-/
