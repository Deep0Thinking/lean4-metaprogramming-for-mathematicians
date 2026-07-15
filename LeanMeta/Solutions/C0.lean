import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 0

Warm-ups on the functional Lean introduced in §0.4.  Compare with
`Exercises/C0.lean`. -/

-- W1.  A three-argument-free function.
def thrice (n : Nat) : Nat := n + n + n
#eval thrice 4                    -- 12

-- W2.  Pattern-free predicate via `%`.
def isEven (n : Nat) : Bool := n % 2 == 0
#eval isEven 10                   -- true
#eval isEven 7                    -- false

-- W3.  `Option` + list patterns: the sum of the first two elements, if present.
def sumFirstTwo : List Nat → Option Nat
  | x :: y :: _ => some (x + y)
  | _           => none
#eval sumFirstTwo [3, 4, 5]       -- some 7
#eval sumFirstTwo [3]             -- none

-- W4.  A `MetaM` computation: build `6 * 7` and compute it.
#eval show MetaM Unit from do
  let e ← mkAppM ``Nat.mul #[mkNatLit 6, mkNatLit 7]
  logInfo m!"{e}  ⇝  {← whnf e}"  -- Nat.mul 6 7  ⇝  42
