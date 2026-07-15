import Lean
import LeanMeta.C1_ExprAndName
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 1  (`Name` and `Expr`)

These drill the core skill of the chapter: building `Expr`s by hand (with the
binder-safe open/close idiom) and taking them apart with `getAppFnArgs` / `.eq?`.

Write each answer below its prompt, run it, then compare with `Solutions/C1.lean`.
This file is all comments as shipped, so it builds; fill it in as you go. -/

-- E1.  Build the identity function on `Bool` as a raw `Expr`
--      (`.lam` + `.bvar 0`, cf. §1.3) and `logInfo` both it and `← inferType` of it.
--      Expect:  fun x => x : Bool → Bool

-- E2.  Write `headName : Expr → Name` returning the head symbol of an application
--      (hint: `e.getAppFnArgs.1`).  Test it on `mkAppM ``Nat.add #[1, 2]`.

-- E3.  Using the open/close idiom (`withLocalDeclD` + `mkLambdaFVars`, §1.3),
--      build `fun x : Nat => x * x` and check its type is `Nat → Nat`.

-- E4.  Write `isNatEq : Expr → MetaM Bool`, true iff the expression is an equality
--      whose sides are `Nat`s.  (Hint: `e.eq?` gives `some (type, lhs, rhs)`;
--      test the `type` with `Expr.isConstOf ``Nat`.)
