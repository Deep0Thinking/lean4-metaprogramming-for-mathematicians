import Lean
import LeanMeta.C1_ExprAndName
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 1 (`Name` and `Expr`)

Compare with `Exercises/C1.lean`.  We reuse `describeExpr` from the chapter. -/

-- E1.  Build the identity function on `Bool` as a raw `Expr` and check its type.
#eval show MetaM Unit from do
  let idBool : Expr := .lam `x (.const ``Bool []) (.bvar 0) .default
  logInfo m!"{idBool} : {← inferType idBool}"     -- fun x => x : Bool → Bool
  logInfo (describeExpr idBool)                   -- lam x : (const Bool) => (bvar 0)

-- E2.  The head symbol of an application (`.anonymous` if the head is not a constant).
def headName (e : Expr) : Name := e.getAppFnArgs.1
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.add #[mkNatLit 1, mkNatLit 2]
  logInfo m!"{headName e}"                         -- Nat.add

-- E3.  Build `fun x : Nat => x * x` with the open / work / close idiom (§1.3).
#eval show MetaM Unit from do
  let sq ← withLocalDeclD `x (.const ``Nat []) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``Nat.mul #[x, x])
  logInfo m!"{sq} : {← inferType sq}"             -- fun x => x.mul x : Nat → Nat

-- E4.  Is this `Expr` an equation between `Nat`s?  (Uses `Expr.eq?`, §1.5.)
def isNatEq (e : Expr) : MetaM Bool := do
  let some (ty, _, _) := e.eq? | return false
  return ty.isConstOf ``Nat
#eval show MetaM Unit from do
  logInfo m!"{← isNatEq (← mkAppM ``Eq  #[mkNatLit 1, mkNatLit 1])}"                 -- true
  logInfo m!"{← isNatEq (← mkAppM ``Iff #[.const ``True [], .const ``True []])}"     -- false
