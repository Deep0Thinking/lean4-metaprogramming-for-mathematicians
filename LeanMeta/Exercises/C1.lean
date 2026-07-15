import Lean
import LeanMeta.C1_ExprAndName
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 1  (`Name` and `Expr`)

These drill the two halves of the chapter: BUILDING `Expr`s (raw constructors, and
the binder-safe open/close idiom of §1.3) and TAKING them apart (`getAppFnArgs` and
`.eq?`, §1.5).  Each is a miniature of what a real tactic does all day.

HOW TO WORK THESE: write each answer as the named top-level definition the prompt
asks for, then uncomment its CHECK and run it (watch the Infoview).  The expected
output is stated in the trailing comment, so you will know at a glance whether you
got it.  Only then compare with the answer key in `Solutions/C1.lean`.  As shipped
this file is all comments, so it builds; fill it in as you go.  Exercises run easy
to hard; E5 is an optional stretch with no worked solution, only its check. -/


-- E1.  [warm-up]  Assemble a binder and a `.bvar` by hand, so the de Bruijn story
--      of §1.3 stops being abstract.
--
--      TASK: define  idBool : Expr  equal to the identity function on `Bool`, built
--      from raw constructors only (`.lam` with a `.bvar 0` body, cf. the `idNat`
--      in §1.3).  No `mkAppM`, no free variables: this one is pure tree-building.
--
--      HINT: `.lam name type body .default`, and the body of `fun x => x` is `.bvar 0`.
--
--      CHECK (uncomment after defining `idBool`):
-- #eval show MetaM Unit from do
--   logInfo m!"{idBool} : {← inferType idBool}"     -- fun x => x : Bool → Bool
--   logInfo (describeExpr idBool)                   -- lam x : (const Bool) => (bvar 0)


-- E2.  The head symbol is how a tactic decides what a term even is; recovering it
--      through the unary-application spine (Trap #5) is the first reflex of §1.5.
--
--      TASK: write  headName : Expr → Name  returning the head symbol of an
--      application (the leading constant, or `.anonymous` if the head is not one).
--
--      HINT: `getAppFnArgs` hands back `(Name, Array Expr)` in one step; you want
--      just the first component.
--
--      CHECK (uncomment after defining `headName`):
-- #eval show MetaM Unit from do
--   let e ← mkAppM ``Nat.add #[mkNatLit 1, mkNatLit 2]
--   logInfo m!"{headName e}"                         -- Nat.add


-- E3.  The open / work / close idiom is the one move you will use forever: build
--      under a binder with an honest free variable, never touching an index (§1.3).
--
--      TASK: write  mkSquare : MetaM Expr  producing `fun x : Nat => x * x`, using
--      the binder-safe idiom rather than a hand-written `.bvar`.
--
--      HINT: `withLocalDeclD` opens a fresh free variable `x`; `mkLambdaFVars #[x] _`
--      closes it back up.  Build the body with `mkAppM ``Nat.mul #[x, x]`.
--
--      CHECK (uncomment after defining `mkSquare`):
-- #eval show MetaM Unit from do
--   let sq ← mkSquare
--   logInfo m!"{sq} : {← inferType sq}"             -- fun x => x.mul x : Nat → Nat


-- E4.  Reading an equation out of an `Expr`, its type and its two sides, is the
--      daily bread of any rewriting tactic (§1.5).
--
--      TASK: write  isNatEq : Expr → MetaM Bool, true exactly when the expression
--      is an equality whose sides live in `Nat`.
--
--      HINT: `e.eq?` returns `some (type, lhs, rhs)` or `none`; pattern-match with
--      `let some (ty, _, _) := e.eq? | return false`, then test `ty.isConstOf ``Nat`.
--
--      CHECK (uncomment after defining `isNatEq`):
-- #eval show MetaM Unit from do
--   logInfo m!"{← isNatEq (← mkAppM ``Eq  #[mkNatLit 1, mkNatLit 1])}"                 -- true
--   logInfo m!"{← isNatEq (← mkAppM ``Iff #[.const ``True [], .const ``True []])}"     -- false


-- E5.  [stretch]  Combine both halves of the chapter: take an equation apart, then
--      ask the defeq engine (§1.4) whether its two sides are already the same term.
--      (No solution is provided; the check is your oracle.)
--
--      TASK: write  isReflEq : Expr → MetaM Bool, true when the expression is an
--      equality `a = b` whose sides are DEFINITIONALLY equal (so `4 = 2 + 2` counts,
--      `1 = 2` does not), and false when it is not an equality at all.
--
--      HINT: destructure with `e.eq?` as in E4, then hand the two sides to `isDefEq`.
--
--      CHECK (uncomment after defining `isReflEq`):
-- #eval show MetaM Unit from do
--   let two2 ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 2]
--   let eqA  ← mkAppM ``Eq #[mkNatLit 4, two2]          -- @Eq Nat 4 (2 + 2)
--   let eqB  ← mkAppM ``Eq #[mkNatLit 1, mkNatLit 2]    -- @Eq Nat 1 2
--   logInfo m!"{← isReflEq eqA}"                        -- true   (2 + 2 is defeq to 4)
--   logInfo m!"{← isReflEq eqB}"                        -- false  (1 and 2 are not defeq)
