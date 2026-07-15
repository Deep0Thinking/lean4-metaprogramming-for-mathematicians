import Lean
/-!
# Chapter 4. Elaboration: `Syntax → Expr`

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§4.  ELABORATION: `Syntax → Expr`
--------------------------------------------------------------------------------
A macro maps `Syntax → Syntax`.  An *elaborator* maps `Syntax → Expr`, and can
therefore do arbitrary computation, look at the expected type, inspect the
environment, and so on.  This is where the power is.
-/

/-- `sum% [1,2,3]` is computed at ELABORATION time; the resulting proof term
    contains the literal `6`, with no addition left in it at all.

    `ns:num,*` matches a comma-separated list of number literals; `ns.getElems`
    is the `Array` of them, and each `n.getNat` reads its `Nat` value. -/
elab "sum% " "[" ns:num,* "]" : term => do
  let mut total : Nat := 0
  for n in ns.getElems do
    total := total + n.getNat
  return mkNatLit total

#eval sum% [1, 2, 3, 4]                 -- 10
example : sum% [1, 2, 3] = 6 := rfl     -- the elaborator really did the arithmetic

/-- A custom *command*: a home-made `#check`. -/
elab "#typeof " t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t none                       -- Syntax → Expr
    Term.synthesizeSyntheticMVarsNoPostponing          -- force pending elaboration
    logInfo m!"{e} : {← inferType e}"

#typeof Nat.add_comm                    -- Nat.add_comm : ∀ (n m : Nat), n + m = m + n
#typeof (fun n : Nat => n + 1)          -- fun n => n + 1 : Nat → Nat

/-
The `Option Expr` argument to `Term.elabTerm` is the *expected type* (see
§0.4(d): `none` = "no expectation").  Passing `none` means "elaborate freely";
passing `some τ` means "this had better be a τ", which is what enables coercions
and `_`-inference.  In a tactic, the expected type is normally the goal.
-/
