import Lean
/-!
# Chapter 4. Elaboration: `Syntax → Expr`

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

The pipeline of Chapter 0 was `Syntax → (elaboration) → Expr`.  Chapter 3 was the
first box; this chapter is the arrow.  A macro (Chapter 3) rewrote notation into
*other notation Lean already understood*.  An *elaborator* is strictly more
powerful: it runs code to build the `Expr` (the meaning) directly.  §4.1 pins down
exactly what that extra power is; the rest of the chapter demonstrates each part on
small term and command elaborators.  The tactics of Chapter 5 are just elaborators
for the `tactic` category.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§4.  ELABORATION: `Syntax → Expr`
--------------------------------------------------------------------------------

§4.1  What an elaborator can do that a macro cannot
---------------------------------------------------
It is tempting to say "an elaborator can compute and a macro cannot", but that is
false: a macro also runs in a monad and can loop.  A macro that summed a list could
even emit the numeral `6` directly, indistinguishable from the elaborator below.
So computation is NOT the dividing line.  Here is what genuinely separates them, and
what the rest of this chapter demonstrates:

  * an elaborator sees the **expected type** (the type the context is asking for);
    a macro has none, because it runs before types are known (§4.3);
  * an elaborator can inspect the **meaning** of the environment, a constant's type,
    value, and instances (via `inferType`, `getConstInfo`, ...); a macro can resolve
    a *name* but cannot look up what it *means* (§4.4).

§4.2  A term elaborator: computing at elaboration time
------------------------------------------------------
Still, computing during elaboration is useful, and a term elaborator is the
simplest example.  `sum% [1,2,3]` runs a loop while elaborating and emits the
numeral `6`, with no addition left in the term. -/

/-- `sum% [1,2,3]` is computed at ELABORATION time; the resulting term is the
    numeral `6`, no addition left.

    `ns:num,*` matches a comma-separated list of number literals; `ns.getElems`
    is the `Array` of them, `n.getNat` reads each `Nat`, and `mkNatLit` turns the
    final total back into an `Expr`. -/
elab "sum% " "[" ns:num,* "]" : term => do
  let mut total : Nat := 0
  for n in ns.getElems do
    total := total + n.getNat
  return mkNatLit total

#eval sum% [1, 2, 3, 4]                 -- 10
#check (sum% [1, 2, 3])                 -- 6 : Nat   ← the term IS `6`, not `1 + 2 + 3`

/-! (A looping *macro* could also emit `6` here, so this example alone does not show
the elaborator's advantage.  The next two sections show powers a macro simply lacks.)

### §4.3  Power 1: the expected type (type-directed elaboration)

Elaboration is not context-free: it is steered by the *expected type*, the type the
surrounding context asks for.  You already rely on this: the same syntax `2` becomes
a different `Expr` depending on what is expected.  With `pp.explicit` turned on you
can see the two different terms (both are `OfNat.ofNat`, but over different types,
with different instances): -/

set_option pp.explicit true in
#check (2 : Nat)     -- @OfNat.ofNat Nat 2 (instOfNatNat 2)   : Nat
set_option pp.explicit true in
#check (2 : Int)     -- @OfNat.ofNat Int 2 (@instOfNat 2)     : Int   ← expected type chose this

/-! A *coercion* is a related but distinct thing: an automatically inserted map, the
inclusion `ℕ ↪ ℤ` you already know.  Write a `Nat` *value* where an `Int` is
expected and elaboration inserts `↑` (which is `Nat.cast`) for you.  Note this fires
on the *mismatch* between expected and actual type; the polymorphic literal `2`
above did not coerce, it just adapted through `OfNat`. -/

#check (fun (n : Nat) => (n : Int))    -- fun n => ↑n : Nat → Int   (`↑` = Nat.cast)

/-! `_`-inference is the same mechanism from the other side: the expected type is
what determines a `_` placeholder.  All of this, coercions, `_`-inference, and
overload resolution, is the "coercions and instance synthesis" promised back in the
§0.3 monad table, and it all flows from the expected type.

The payoff for us: in a tactic, **the goal is the expected type**.  A goal is a
metavariable (§2) and its type is what you must produce, so `by exact e` elaborates
your `e` against the goal exactly as `(e : goalType)` would.  Chapter 5 picks up
this thread.

### §4.4  Power 2: inspecting the environment

A macro can mention the name `Nat.add_comm`, but it cannot ask what that name *is*.
An elaborator can.  Here is one that fails the build unless a named declaration
exists, something a macro fundamentally cannot do (it reads the environment via
`getEnv` and checks membership): -/

elab "#assertExists " n:ident : command => do
  if (← getEnv).contains n.getId then
    logInfo m!"{n.getId} is in the environment"
  else
    throwError m!"{n.getId} does NOT exist"

#assertExists Nat.add_comm              -- Nat.add_comm is in the environment
-- #assertExists Nat.total_nonsense     -- ✗ would fail the build: does NOT exist

/-! ### §4.5  A command elaborator, and finishing postponed work

The top-level commands (`#check`, `#eval`, `def`) are elaborators too, for the
`command` category.  Here is a home-made `#check`.  A command runs in `CommandElabM`
(the top layer of §0.3); elaborating a term needs the `TermElabM` layer, so
`Command.liftTermElabM` performs the ⊆-lift down into it.  `Term.elabTerm t none`
turns the `Syntax` `t` into an `Expr` (the `none` is the expected type from §4.3:
"no expectation"). -/

/-- A custom *command*: a home-made `#check`. -/
elab "#typeof " t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t none                       -- Syntax → Expr (no expected type)
    Term.synthesizeSyntheticMVarsNoPostponing          -- force any postponed elaboration to finish
    logInfo m!"{e} : {← inferType e}"

#typeof Nat.add_comm                    -- Nat.add_comm : ∀ (n m : Nat), n + m = m + n
#typeof (fun n : Nat => n + 1)          -- fun n => n + 1 : Nat → Nat

/-! What is that `synthesizeSyntheticMVarsNoPostponing` line for?  Elaboration is
not a single pass.  When Lean hits a subproblem it cannot solve yet, an instance to
search, a `_` whose type is not pinned down, it plants a *synthetic* metavariable (a
hole it promises to fill) and *postpones*.  So `elabTerm t none` can return a term
that still has unsolved holes, and `inferType` on it gives the wrong answer.  The
call says "solve all pending holes now."  Delete it and the difference is visible:
`inferType (2 + 2)` returns a raw metavariable instead of `Nat`. -/

elab "#inferNoForce " t:term : command =>
  Command.liftTermElabM do
    logInfo m!"without the force call, inferType = {← inferType (← Term.elabTerm t none)}"

#inferNoForce (2 + 2)     -- without the force call, inferType = ?m.NNN   (a metavariable!)
#typeof (2 + 2)           -- 2 + 2 : Nat                                  (with the force call)

/-
(The same `synthesizeSyntheticMVarsNoPostponing` pattern appears in this chapter's
`Solutions/C4.lean`, in the `#isProp` command, for the same reason.)

So the three elaborator flavours you have now seen, term (`sum%`), command
(`#typeof`, `#assertExists`), and the tactic elaborators coming in Chapter 5, are
all the same `elab` mechanism pointed at different syntactic categories.  A tactic
is nothing but an elaborator for the `tactic` category, whose job is to fill the
goal metavariable (Chapter 2).  That is the door we walk through next.
-/
