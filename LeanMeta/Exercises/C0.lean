import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 0  (the functional Lean of §0.4)

These warm-ups drill the small slice of functional Lean the whole tutorial rests
on: functions, pattern matching, `Option`, and a first `MetaM` computation.  If
these feel comfortable, the later chapters will too.

HOW TO WORK THESE: write each answer below its prompt, run it (watch the Infoview),
and only then compare with the answer key in `Solutions/C0.lean`.  As shipped this
file is all comments, so it builds; fill it in as you go. -/

-- W1.  Write `thrice : Nat → Nat` returning `n + n + n`, and `#eval thrice 4` (expect 12).

-- W2.  Write `isEven : Nat → Bool` using `n % 2`.  Check `isEven 10` and `isEven 7`.

-- W3.  Write `sumFirstTwo : List Nat → Option Nat` returning the sum of the first
--      two elements, or `none` if there are fewer than two.  (Pattern-match on
--      `x :: y :: _`.)

-- W4.  In `MetaM`, build the expression `6 * 7` with `mkAppM ``Nat.mul #[...]`
--      and `logInfo` its `whnf` (expect it to compute to 42).  Template:
--
-- #eval show MetaM Unit from do
--   let e ← mkAppM ``Nat.mul #[mkNatLit 6, mkNatLit 7]
--   logInfo m!"{e}  ⇝  {← whnf e}"
