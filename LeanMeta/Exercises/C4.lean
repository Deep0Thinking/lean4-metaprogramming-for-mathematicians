import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Exercises for Chapter 4  (Elaboration: `Syntax → Expr`)

These drill the arrow of the pipeline: writing elaborators, term and command, that
run code at ELABORATION time to build an `Expr` directly (something a macro cannot
do).  E1 and E2 exercise a term elaborator that computes now and hands back a
finished literal (§4.2); E3 crosses from `CommandElabM` down into `MetaM` to query a
term's meaning (§4.5); the E4 stretch exercises Power 2, inspecting the environment
(§4.4).

Write each answer below its prompt, run it, then compare with `Solutions/C4.lean`.
This file is all comments as shipped, so it builds; fill it in as you go.  Each
exercise ends with a CHECK: uncomment those lines once your answer is written, and
you will KNOW it is right when the stated result appears. -/

-- E1  (warm-up).  A term elaborator earns its keep the moment it computes: `double% n`
--     should come back as a single numeral, with no multiplication surviving into the
--     term (§4.2).
--     TASK:  write a term elaborator `double%` so that `double% n` elaborates DIRECTLY
--            to the literal `2 * n` (do the arithmetic now; do not emit `2 * n`).
--     HINT:  `elab "double% " n:num : term => ...`; `n.getNat` reads the `Nat` out of
--            the numeral, and `mkNatLit` turns a `Nat` back into an `Expr`.
--
--     (write your `double%` here)
--
--     CHECK (uncomment; the `rfl` is the real proof the doubling happened at elab time):
-- #eval double% 21                 -- 42
-- example : double% 3 = 6 := rfl   -- the elaborator really doubled it

-- E2.  Like `sum%` in §4.2, but instead of summing the values you count them.  The
--      new skill is reading a VARIADIC syntax match and pulling its elements array.
--     TASK:  write `len% [a, b, c]` returning the LENGTH of the bracketed list as a
--            literal.  The elements' values must not matter, only how many there are.
--     HINT:  match `"[" xs:term,* "]"`; the elements are `xs.getElems`, and its `.size`
--            is your answer.
--
--     (write your `len%` here)
--
--     CHECK (uncomment):
-- #eval len% [10, 20, 30]          -- 3
-- #eval len% []                    -- 0

-- E3.  Cross the monad boundary.  A command lives in `CommandElabM`, but "is this a
--      proposition?" is a `MetaM` question about a real `Expr`, so you must elaborate
--      the term first, then ask (§4.5).
--     TASK:  write a command `#isProp t` that elaborates `t` and reports whether its
--            type is a `Prop`.  Force any postponed elaboration BEFORE you query it.
--     HINT:  `Command.liftTermElabM`, then `Term.elabTerm t none`, then (§4.5)
--            `Term.synthesizeSyntheticMVarsNoPostponing`, then `Meta.isProp`.
--
--     (write your `#isProp` here)
--
--     CHECK (uncomment):
-- #isProp True                     -- True : isProp = true
-- #isProp Nat                      -- Nat : isProp = false

-- E4  (stretch).  Power 2 of §4.4: a macro can SPELL the name `Nat.add_comm`, but it
--      cannot ask what the name MEANS.  An elaborator can look the declaration up in
--      the environment and read its stored type.
--     TASK:  write a command `#constType n` that takes an identifier for an already
--            declared constant and logs its type as recorded in the environment.
--            (Contrast `#typeof` in §4.5, which elaborates an arbitrary term; here you
--            look a NAME up directly.)
--     HINT:  inside `Command.liftTermElabM`, `getConstInfo n.getId` returns the
--            `ConstantInfo`, and its `.type` field is the `Expr` you want.
--
--     (write your `#constType` here)
--
--     CHECK (uncomment):
-- #constType Nat.add_comm          -- Nat.add_comm : ∀ (n m : Nat), n + m = m + n
-- #constType Nat.succ              -- Nat.succ : Nat → Nat
