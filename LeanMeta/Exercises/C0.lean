import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 0  (the functional Lean of §0.4)

These warm-ups drill the small slice of functional Lean the whole tutorial rests
on: functions (§0.4(a)), pattern matching (§0.4(c)), `Option` (§0.4(d)), and a first
`MetaM` computation (§0.4(h)).  If these feel comfortable, the later chapters will
too.

Work top to bottom; the exercises run easy to hard.  For each one, write your
answer in the blank space below the prompt, then UNCOMMENT the `-- CHECK` line(s)
and run them.  A `#eval` prints the stated result in the Infoview; if it matches,
you got it.  Compare with `Solutions/C0.lean` only after you have tried.  As
shipped this file is all comments, so `lake build` stays green; you fill it in as
you go. -/


-- ============================================================================
-- W1  (warm-up).  Your first function.
-- ----------------------------------------------------------------------------
-- MOTIVATION: `def name (args) : Type := value` is the single most common line in
--   all meta-code; get the muscle memory before anything else (§0.4(a)).
-- TASK: write `thrice : Nat → Nat` returning `n + n + n`.
-- HINT: no pattern matching needed; one arithmetic expression on the right of `:=`.
--
-- (write your answer here)
--
-- CHECK (uncomment):
-- #eval thrice 4                    -- 12


-- ============================================================================
-- W2  (warm-up).  A predicate, computed not matched.
-- ----------------------------------------------------------------------------
-- MOTIVATION: a `Bool`-valued test is how a tactic later decides "does this case
--   apply?"; the humblest one is arithmetic (§0.4(a)).
-- TASK: write `isEven : Nat → Bool` using `n % 2`.
-- HINT: compare the remainder to `0` with `==` (the `Bool`-valued equality test),
--   not the propositional `=`.
--
-- (write your answer here)
--
-- CHECK (uncomment):
-- #eval isEven 10                   -- true
-- #eval isEven 7                    -- false


-- ============================================================================
-- W3.  Pattern matching meets `Option`: an honestly partial function.
-- ----------------------------------------------------------------------------
-- MOTIVATION: "read two things off the front, if they are there" is the exact
--   shape of the lookups a tactic does constantly; `Option` makes the missing
--   case a value you must handle, not a crash (§0.4(c), §0.4(d)).
-- TASK: write `sumFirstTwo : List Nat → Option Nat` returning the sum of the first
--   two elements, or `none` if there are fewer than two.
-- HINT: match on `x :: y :: _` for the two-element-or-more case, and let a wildcard
--   `_` catch the rest as `none`.
--
-- (write your answer here)
--
-- CHECK (uncomment):
-- #eval sumFirstTwo [3, 4, 5]       -- some 7
-- #eval sumFirstTwo [3]             -- none


-- ============================================================================
-- W4.  First contact with `MetaM`: build a term, then compute it.
-- ----------------------------------------------------------------------------
-- MOTIVATION: this is the whole game in miniature, a `do` block that assembles an
--   `Expr` and asks Lean to evaluate it; every tactic you write is a longer
--   version of this (§0.4(h)).
-- TASK: in `MetaM`, build the expression `6 * 7` with `mkAppM ``Nat.mul #[...]`
--   and `logInfo` its `whnf` (it should compute to 42).
-- HINT: `mkNatLit 6` and `mkNatLit 7` are the two arguments; a line with `←` RUNS a
--   computation, so reach for `(← whnf e)` inside the message.
--
-- (write your answer here, inside a `#eval show MetaM Unit from do` block)
--
-- CHECK (uncomment):
-- #eval show MetaM Unit from do
--   let e ← mkAppM ``Nat.mul #[mkNatLit 6, mkNatLit 7]
--   logInfo m!"{e}  ⇝  {← whnf e}"  -- Nat.mul 6 7  ⇝  42


-- ============================================================================
-- S1  (stretch, no solution key).  A loop that accumulates.
-- ----------------------------------------------------------------------------
-- MOTIVATION: many tactics fold over a list of hypotheses or goals with exactly
--   this `let mut` + `for` shape; practising it now defuses TRAP #2 before it bites
--   in a real tactic (§0.4(h)).
-- TASK: in `MetaM`, use a mutable accumulator and a `for` loop to compute the
--   PRODUCT of `[1, 2, 3, 4]`, then `logInfo` it (it should be 24).
-- HINT: start the accumulator at `1`, not `0`, and annotate it `let mut prod : Nat`
--   so Lean does not guess the type from the later message (that is TRAP #2).
--
-- (write your answer here, inside a `#eval show MetaM Unit from do` block)
--
-- CHECK (uncomment):
-- #eval show MetaM Unit from do
--   let mut prod : Nat := 1
--   for i in [1, 2, 3, 4] do
--     prod := prod * i
--   logInfo m!"product = {prod}"     -- product = 24
