import Lean
/-!
# Chapter 1. `Name` and `Expr`: the language the kernel speaks

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

Chapter 0 ended on a slogan: *a tactic builds an `Expr` whose type is the goal.*
This chapter answers the obvious next question: what *is* an `Expr`?  It is the
single datatype in which Lean stores every term, every type, and every proof.
Manipulating proofs means reading and building `Expr`s, so this is the core
vocabulary of the whole subject.  We also meet `Name` (how constants are referred
to) and the three operations you will use in every tactic: `inferType`, `whnf`,
and `isDefEq`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§1.  `Name` AND `Expr`
--------------------------------------------------------------------------------

§1.1  Names
-----------
Why this exists: a tactic constantly needs to *refer to declared constants*, a
theorem like `Nat.add_comm`, a constructor like `Or.inl`, a definition like
`Nat.add`.  Lean identifies each by a `Name`, which is a *list* of components
rather than a flat string (`Nat.succ` is `"succ"` under `"Nat"`, over the empty
root `.anonymous`).  It is structured this way because Lean constantly appends
namespaces, strips prefixes, and tests prefix containment: exact on a component
list, but error-prone when slicing a string at its dots.

There are two ways to write a `Name` literal, and the difference is exactly the
difference between an unchecked citation and a validated cross-reference:

    `foo.bar     -- ONE backtick: a raw Name literal.  NOT checked.  Might not exist.
    ``Nat.succ   -- TWO backticks: resolved and CHECKED at compile time, and
                 --                expanded to the fully-qualified name.

⚑ TRAP #3: prefer two backticks whenever you mean an existing constant.  With one
backtick a typo like `` `Nat.suc `` silently produces a `Name` that resolves to
nothing; your tactic then looks for a constant that is not there and mysteriously
never fires, with no error to tell you why.  Two backticks turn that typo into a
compile-time error at the point you wrote it.

(In `#eval`, a `Name` prints back with a leading backtick, e.g. `` `Nat.succ ``.
That backtick is only how a `Name` displays; it is not part of the name.)
-/

#eval `foo.bar               -- `foo.bar         (no check performed)
#eval ``Nat.succ             -- `Nat.succ        (checked: the constant exists)
-- #eval ``Nat.suckzess      -- ✗ compile error: unknown identifier.  Good!

/-! ### §1.2  `Expr`, the core language

Here is the idea that makes one datatype enough for everything.  In Lean's
foundations (dependent type theory) there is no wall between "terms", "types", and
"proofs":

  * a *type* is itself a term (`Nat` is a value, of type `Type`; `Type` is a value,
    of type `Type 1`; and so on up a hierarchy);
  * a *proof* is a term too, namely a term whose type is a proposition (this is the
    Curry-Howard slogan from Chapter 0: a proof of `P` is a value of type `P`).

So the natural number `2 + 2`, the type `Nat`, the proposition `∀ n, n + 0 = n`,
and a proof of it are all the *same kind of object*, and Lean stores them all in
one datatype, `Expr`.  Learn `Expr` and you have learned the entire language every
proof is written in.  You can see the "types and proofs are values" claim directly
(put your cursor on each line): -/

#check Nat            -- Nat : Type       a type is a value, here of type `Type`
#check Type           -- Type : Type 1    and `Type` is itself a value, one level up
#check (rfl : 1 = 1)  -- rfl : 1 = 1      a proof is a value whose type is the proposition

/-! Now look at the real definition of `Expr`: -/

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

Twelve looks like a lot, but they fall into four small groups:

  * the three kinds of VARIABLE: `.bvar` (bound, see §1.3), `.fvar` (a free
    variable, which for us always means a hypothesis in the goal), `.mvar` (a hole
    still to be filled; a goal is one of these, see §2);
  * the ATOMS: `.const` (a named constant with its universe arguments), `.sort` (a
    universe such as `Prop` or `Type`), `.lit` (a numeric or string literal);
  * the LAMBDA-CALCULUS core, which is where all the structure lives: `.app` (apply
    a function to an argument) plus the two binders `.lam` (build a function
    `fun x => ...`) and `.forallE` (form a function type, which is *also* how `→`
    and `∀` are stored);
  * the RARELY-hand-built rest: `.letE`, `.mdata` (annotations the kernel ignores),
    `.proj` (project a field out of a structure value).

About `.sort` and universe levels: to avoid Russell's paradox Lean does not have
`Type : Type`; instead `Prop = Sort 0`, `Type = Sort 1`, `Type 1 = Sort 2`, and so
on up a hierarchy of *universe levels*.  You rarely touch levels by hand, and the
`mkConstWithFreshMVarLevels` helper in §1.4 handles them for you; for now just know
that the `us` in `.const n us` and the `u` in `.sort u` are these levels.

Three traps live in this list, and each has bitten everyone:

⚑ TRAP #4: `p → q` is NOT a separate constructor.  An implication is a *degenerate*
`∀`: it is `.forallE _ p q _` whose body ignores the bound variable.  Likewise
`¬p` is not a constructor: it is the constant `Not` applied to `p` (and `Not p`
unfolds to `p → False`).  So when you look for an implication, you look for a
`.forallE`.

⚑ TRAP #5: application is UNARY.  `f a b` is not one node with two arguments; it is
`.app (.app f a) b`, a left-leaning spine.  Never peel it apart by hand; use
`Expr.getAppFn` / `getAppArgs` / `getAppFnArgs` (§1.5), which recover the head and
the whole argument list in one step.

One framing before we look inside: an `Expr` is an *abstract syntax tree*.  Just as
`2 + 3 * 4` is really the tree with `+` at the root and children `2` and `3 * 4`
(not a flat string), every `Expr` is a tree whose node kinds are exactly the twelve
constructors above.  The function below is your microscope: a plain recursive
function (the definition-by-cases from §0.4(c)) that walks that tree and names each
node.  Read it as a catalogue, then run it on real terms in §1.3. -/

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

/-! ### §1.3  de Bruijn indices: why bound variables have no names

This is the single most alien piece of `Expr`, so here is the reason it is built
this way.  Consider `fun x => x` and `fun y => y`.  As functions they are *the
same*; the choice of letter is meaningless (this is alpha-equivalence).  If Lean
stored the letter, it would have to compare terms "up to renaming" everywhere, and
substituting one term into another could accidentally *capture* a variable (a free
`y` sliding under a binder that also uses `y`).  Both problems are classic and
fiddly.

The fix, due to de Bruijn, is to give bound variables no names at all, only a
*number*: `.bvar i` means "the variable bound by the `i`-th enclosing binder,
counting outward from 0".  Now the *bodies* of `fun x => x` and `fun y => y` are
the identical tree `.bvar 0`.  The one thing still distinguishing the two terms is
the display-only `Name` label kept in `.lam`, and Lean's equality test `==` (with
its hashing) deliberately ignores that label, so the two count as equal; and
substitution can no longer capture.  See it: -/

#eval (Expr.lam `x (.const ``Nat []) (.bvar 0) .default) ==
      (Expr.lam `y (.const ``Nat []) (.bvar 0) .default)   -- true: `==` ignores the binder name

/-! That retained name exists only so the pretty-printer can show `fun x =>` rather
than `fun #0 =>`; it carries no logical meaning.

Analogy: instead of naming the variable of an integral you refer to "the variable
of the innermost integral" (∫f(x)dx and ∫f(y)dy are the same integral).  `.bvar 0`
is the innermost binder, `.bvar 1` the next one out.  Watch it happen: -/

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
⚑ TRAP #6: THE classic beginner bug.  A `.bvar i` only means something *underneath*
its binder.  If you grab the body of a `.lam` and use it on its own, its `.bvar`s
now point at binders that are not there; this is a *loose* bound variable, and it
is nonsense that will crash the kernel or produce gibberish.

The cure, and the single idiom you will use forever, is to never touch `.bvar`
yourself.  Instead, *open* the binder into a fresh named free variable, do your
work with that honest variable, then *close* it back up.  In `MetaM`:

    withLocalDeclD name type  fun x => ...   -- OPEN: gives you a free variable `x`
    mkLambdaFVars #[x] body                  -- CLOSE: abstracts `x` back into a bvar

Between the two, `x` is an ordinary `Expr` (a free variable) you can pass around
and apply, with no index arithmetic anywhere.  (To open *several* nested binders at
once you will later reach for `lambdaTelescope` / `forallTelescope`; a *telescope*
is the whole chain of binders, see the §D glossary.)  Here we build `fun x => x + 1`
without ever writing a `.bvar`: -/

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

### §1.4  Building expressions, and the three workhorses

Why not just use the raw constructors?  Because a real constant almost never
stands alone: it comes with implicit arguments, universe levels, and typeclass
instances that must be filled in.  `Nat.add 2 3` as an `Expr` is fine, but
`@Eq Nat 1 1` already needs the implicit type argument, and `@HAdd.hAdd ...` needs
an instance.  The `mk...` helpers do all of that bookkeeping for you.  The one
worth naming now (you meet it in §6 and §C):

`mkConstWithFreshMVarLevels ``c` builds the constant `c` with *fresh universe-level
metavariables* filled in, so later unification can solve them.  Reach for it
instead of `.const ``c []` whenever `c` might be universe-polymorphic (e.g.
`False.elim : {C : Sort u} → False → C`, or `Exists.intro`), where the empty level
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
Three `MetaM` operations appeared there, and you will use them in every tactic you
ever write.  Two need real intuition, so take them slowly.

    inferType e   : MetaM Expr    -- the type of e (recall: types are terms too)

    whnf e        : MetaM Expr    -- "weak-head normal form": compute just enough
                                  --   to expose the OUTERMOST symbol, no further.

    isDefEq a b   : MetaM Bool    -- are a and b DEFINITIONALLY equal?
                                  --   ⚠ may ASSIGN metavariables as a side effect.

DEFINITIONAL EQUALITY is the concept to internalize.  Two terms are *definitionally
equal* (defeq) when they become identical after unfolding definitions and
computing.  The example every mathematician already owns: `2 + 2` and `4` are not
merely "provably equal"; they are the *same natural number*, because `2 + 2`
*computes* to `4`.  That sameness is definitional equality, and Lean's typechecker
uses it silently everywhere.  For instance this is accepted with no rewriting at
all, because `P (2 + 2)` and `P 4` are the very same type: -/

example (P : Nat → Prop) (h : P (2 + 2)) : P 4 := h   -- accepted: 2 + 2 is defeq to 4

-- The sharpest contrast, worth staring at.  `Nat.add` computes by recursion on its
-- SECOND argument, so `n + 0` reduces straight to `n` (defeq), while `0 + n` gets
-- stuck on the variable `n` and is only PROPOSITIONALLY equal to it:
example (n : Nat) : n + 0 = n := rfl        -- ✓ `rfl` works: the two sides are DEFEQ
-- example (n : Nat) : 0 + n = n := rfl      -- ✗ rejected: NOT defeq (`0 + n` is stuck)
example (n : Nat) : 0 + n = n := by simp     -- ✓ but this needs a real proof (induction)

/-
Contrast this with *propositional* equality `a = b`, which is a proposition you
state and prove (with `rw`, `simp`, ...).  Definitional equality is stronger and
automatic: if two things are defeq, you may use one where the other is expected,
for free.  `rfl` proves `a = b` exactly when `a` and `b` are defeq, which is why
`example : 2 + 2 = 4 := rfl` works.

`isDefEq a b` decides defeq, but it does one thing more: it is *unification*.  If
either side contains a metavariable (a hole), `isDefEq` will try to *assign* that
hole to make the two sides equal.  `isDefEq ?m 5` returns `true` and, as a side
effect, sets `?m := 5`.  This is the engine underneath `apply`, `exact`, and `rw`:
each one works by asking "can I make these defeq, filling holes as needed?".  (A
failed `isDefEq` rolls back any assignments it tried, so failure is harmless.)

`whnf` (weak-head normal form) answers a narrower question: what is the OUTERMOST
symbol here?  To decide "is this goal an equation? a conjunction? a `∀`?" you do
not need the term fully computed; you need only its head.  `whnf` unfolds and
computes just until the head is rigid (a constructor, a binder, a constant that
will not reduce), then stops.  It is the standard first move when matching on a
goal's shape.  You can watch it see through a definition to expose a hidden head: -/

/-- A user-defined abbreviation, opaque until `whnf` unfolds it. -/
def MyConj (p q : Prop) : Prop := p ∧ q

#eval show MetaM Unit from do
  let e ← mkAppM ``MyConj #[.const ``True [], .const ``False []]
  logInfo m!"before whnf, head = {e.getAppFn}"           -- MyConj  (opaque)
  logInfo m!"after  whnf, head = {(← whnf e).getAppFn}"  -- And     (whnf saw through it)

/-
TRANSPARENCY controls how eagerly `whnf` and `isDefEq` unfold definitions, and it
matters for a real reason.  Suppose a user wrote `def Positive x := x > 0`.  When
your tactic inspects a goal `Positive n`, should it see `Positive n` or unfold to
`n > 0`?  Usually you want to respect their abbreviation and NOT unfold.  The
transparency setting is that dial:

    `.reducible`  (only `@[reducible]` defs)  ⊂  `.instances`
                  ⊂  `.default` (everything except `@[irreducible]`)  ⊂  `.all`

    whnf   e             -- uses the ambient setting (usually `.default`)
    whnfR  e             -- forces `.reducible`
    withReducible do ... -- runs a whole block at `.reducible`

Rule of thumb: when you match on the *user's* goal shape, work at `.reducible` so
you do not accidentally see through their definitions.  When you need to decide
whether two things are *really* the same, use `.default`.
-/

/-! ### §1.5  Taking expressions apart

You now build `Expr`s; the other half of the job is reading them.  The one tool to
reach for first is `getAppFnArgs`: because application is unary (Trap #5), a term
like `@And p q` is really `.app (.app (.const `And) p) q`, and matching that by
hand is miserable.  `getAppFnArgs` undoes the spine in one step, handing you the
head constant's `Name` and the argument `Array`.  Classifying a proposition by its
head symbol then reads like a table: -/

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
the one-argument `Not` from `Eq`, which carries three (`@Eq α lhs rhs`), because
the implicit type argument counts. -/

/-
Other useful destructors (all in `Lean.Expr`, all worth Ctrl-clicking):
    e.isForall  e.isLambda  e.isApp  e.isConstOf n  e.isFVar  e.isMVar
    e.getAppFn  e.getAppArgs  e.getAppNumArgs
    e.eq?    : Option (Expr × Expr × Expr)   -- (type, lhs, rhs)
    e.arrow? e.not? e.and?
    e.fvarId!  e.mvarId!                     -- partial; only after checking

Two naming conventions worth learning here, because they recur across the whole
API:
  * a `?`-suffixed function returns an `Option` (§0.4(d)): `e.eq?` gives
    `some (α, lhs, rhs)` if `e` is an equality and `none` otherwise, so you handle
    the "not an equality" case honestly;
  * a `!`-suffixed function is its reckless cousin that CRASHES if you are wrong
    (`e.fvarId!` assumes `e` really is an `.fvar`).  Only use `!` right after an
    `is...` check has already guaranteed the shape.

That is `Expr`.  Next, Chapter 2 introduces the one variable kind we have kept
deferring, the metavariable, and reveals that a *goal is a metavariable*.
-/
