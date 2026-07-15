import Lean
import LeanMeta.C3_Syntax
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 3  (`Syntax`)

These drill the front end: the cheapest kind of tactic (a macro, `Syntax → Syntax`),
building syntax with quotations and antiquotations, and extending a syntactic
category with your own notation.

Work top to bottom; the exercises run easy to hard.  For each one, write your answer
in the blank space below the prompt, then UNCOMMENT the `-- CHECK` line(s) and run
them.  A check passes silently (for an `example`) or prints the stated result (for a
`#eval`); if it does, you got it.  Compare with `Solutions/C3.lean` only after you
have tried.  This file is all comments as shipped, so `lake build` stays green; you
fill it in as you go. -/


-- ============================================================================
-- E1  (warm-up).  The shortest tactic there is.
-- ----------------------------------------------------------------------------
-- MOTIVATION: a macro that rewrites your notation into notation Lean already
--   knows is the first tactic you should reach for (§3.3); start with the
--   one-liner form.
-- TASK: write a macro `triv2` that expands to the existing tactic `trivial`.
-- HINT: the shape is `macro "name" : tactic => `(tactic| ...)`.
--
-- (write your answer here)
--
-- CHECK (uncomment):
-- example : True := by triv2


-- ============================================================================
-- E2  (warm-up).  A macro that expands to a tactic taking arguments.
-- ----------------------------------------------------------------------------
-- MOTIVATION: most useful macros expand to a tactic that does structural work;
--   here you abbreviate the "split a goal in two" move.
-- TASK: write a macro `split_and` that turns an `∧` goal into its two halves.
-- HINT: `refine ⟨?_, ?_⟩` leaves one goal per conjunct; wrap it as
--   `` `(tactic| refine ⟨?_, ?_⟩) ``.
--
-- (write your answer here)
--
-- CHECK (uncomment):
-- example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
--   split_and <;> assumption


-- ============================================================================
-- E3.  Build syntax from syntax with an antiquotation.
-- ----------------------------------------------------------------------------
-- MOTIVATION: a quotation is a template with holes (§3.2); `$x` splices one piece
--   of `Syntax` into another, which is how every macro assembles its output.
-- TASK: in `CoreM`, let `t ← `(True)`, then build the syntax `$t ∧ $t` and
--   `logInfo` its raw form.
-- HINT: splice with `$t` inside a quotation, and print the tree with `.raw`.
--
-- (write your answer here, inside a `#eval show CoreM Unit from do` block)
--
-- CHECK (uncomment):
-- #eval show CoreM Unit from do
--   let t ← `(True)
--   logInfo m!"{(← `($t ∧ $t)).raw}"     -- True✝ ∧ True✝   (✝ = hygiene marks on the quoted `True`, §3.4)


-- ============================================================================
-- E4.  Grow a syntactic category: add an operator to the `arith` DSL.
-- ----------------------------------------------------------------------------
-- MOTIVATION: extending a category is exactly how DSLs (and `conv`, and `calc`)
--   are built (§3.5); you add one `syntax` rule for the grammar and one
--   `macro_rules` case for its meaning.
-- TASK: extend the chapter's `arith` DSL with subtraction `-`, mirroring the `+`
--   rule at the same precedence (65).  Then evaluate the two checks below.
-- HINT: copy the `+` lines and swap the token, keeping the `arith:65 " - " arith:66`
--   precedence pattern; the `macro_rules` case rewrites `-` on `arith` into `-` on
--   `term`, just as `+` does.
--
-- (write your answer here: one `syntax` line plus one `macro_rules` case)
--
-- CHECK (uncomment):
-- #eval [arith| 10 - 3]                  -- 7
-- #eval [arith| 2 * (3 + 4) - 5]         -- 9   (`*` binds tighter than `-`)


-- ============================================================================
-- E5  (stretch).  Quotations run in reverse: match, then rebuild.
-- ----------------------------------------------------------------------------
-- MOTIVATION: the same `` `(...) `` that BUILDS syntax also MATCHES it as a
--   pattern (§3.2, §3.3), binding the antiquotations to the pieces it found; this
--   match-then-rebuild move is the heart of every `macro_rules` case.
-- TASK: in `CoreM`, build `stx ← `(1 + 2)`, match it as a sum `` `($a + $b) ``,
--   and `logInfo` the RAW syntax of the same sum with its operands swapped.
-- HINT: `` match stx with | `($a + $b) => ... | _ => ... ``; in the sum branch,
--   build `` `($b + $a) `` and print its `.raw`.
--
-- (write your answer here, inside a `#eval show CoreM Unit from do` block)
--
-- CHECK (uncomment):
-- #eval show CoreM Unit from do
--   let stx ← `(1 + 2)
--   match stx with
--   | `($a + $b) => logInfo m!"{(← `($b + $a)).raw}"   -- 2 + 1
--   | _          => logInfo "not a sum"
