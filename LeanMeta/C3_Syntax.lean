import Lean
/-!
# Chapter 3. `Syntax`: the front end (quotations, macros, hygiene)

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§3.  `Syntax`: THE FRONT END
--------------------------------------------------------------------------------

§3.1  The type
--------------
`Syntax` is a plain, untyped tree.  Four constructors: -/

#print Lean.Syntax

/-
    .missing               -- parse error / absent optional part
    .node info kind args   -- an internal node, tagged with a SyntaxNodeKind (a Name)
    .atom info val         -- a token: "+", "by", "("
    .ident info _ name _   -- an identifier

`TSyntax c` is `Syntax` tagged (in the *Lean* type system, at compile time) with
the syntactic category `c`.  So `TSyntax `term` is a term-shaped tree,
`TSyntax `tactic` a tactic-shaped one.  It is a phantom-typed wrapper: `.raw`
gets you the underlying `Syntax`.  It exists to stop you passing a tactic where a
term is expected.

Let us look at a real tree.  `describeSyntax` is another recursive printer, like
`describeExpr`; `partial` tells Lean not to worry about proving it terminates
(see §5.5). -/

/-- A structural printer for `Syntax`. -/
partial def describeSyntax (stx : Syntax) (indent : String := "") : String :=
  match stx with
  | .missing            => indent ++ "<missing>\n"
  | .atom _ val         => indent ++ s!"atom {repr val}\n"
  | .ident _ _ val _    => indent ++ s!"ident {val}\n"
  | .node _ kind args   =>
      args.foldl (fun acc a => acc ++ describeSyntax a (indent ++ "  "))
        (indent ++ s!"node {kind}\n")

#eval show CoreM Unit from do
  let stx ← `(1 + 2 * 3)          -- a *quotation*: builds Syntax, does not elaborate
  logInfo m!"pretty : {stx.raw}"  -- 1 + 2 * 3
  logInfo (describeSyntax stx.raw)

/-
Read that output.  You are looking at the parse tree, with the node kinds
(`«term_+_»`, `«term_*_»`, `num`) that the parser assigned.  Those kind names are
exactly what `macro_rules` and `@[tactic ...]` dispatch on.

§3.2  Quotations and antiquotations
-----------------------------------
    `(1 + 1)                  -- a `TSyntax `term`
    `(tactic| rfl)            -- a `TSyntax `tactic`
    `(command| def x := 1)    -- a `TSyntax `command`

The `category|` prefix tells the quotation which parser to use.  Bare `` `(...) ``
means a term.

Inside a quotation, `$x` splices in another piece of syntax (an *antiquotation*),
and `$xs,*` splices a comma-separated list.  Quotations are also *patterns*: you
can match on them.  This is how you write macros. -/

#eval show CoreM Unit from do
  let x ← `(37)
  let stx ← `($x + $x)              -- build `37 + 37` out of pieces
  logInfo m!"{stx.raw}"             -- 37 + 37

/-! ### §3.3  Your first tactic: a macro

The cheapest kind of tactic does not touch `Expr` at all.  It just rewrites
syntax into other syntax.  If your tactic is expressible as a combination of
existing tactics, **write a macro**; it is shorter, safer, and free. -/

macro "obvious" : tactic => `(tactic| first | rfl | assumption | trivial)

example (p : Prop) (hp : p) : p := by obvious
example : 2 + 2 = 4 := by obvious
example : True := by obvious

/- The two-step form, which you will see in real code, is equivalent: -/

syntax "obvious2" : tactic                      -- declare the syntax...
macro_rules                                     -- ...and how to expand it
  | `(tactic| obvious2) => `(tactic| first | rfl | assumption | trivial)

example (p : Prop) (hp : p) : p := by obvious2

/-! ### §3.4  Hygiene  (⚑ TRAP #10, and it surprises everyone)

Identifiers created inside a quotation are *hygienic*: they are secretly
decorated with a "macro scope" so that they cannot capture, or be captured by,
the user's names. -/

macro "intro_h" : tactic => `(tactic| intro h)

example : Nat → Nat := by
  intro_h
  -- exact h        -- ✗ ERROR: unknown identifier 'h'.  The `h` above is NOT this `h`.
  exact 0

/-
This is a feature: it means your macro can never accidentally shadow a user's
variable.  But sometimes you *want* to introduce a name the user chose.  Then you
must take the identifier from the user's syntax: it carries the user's scopes.
The next tactic reads an identifier `n` from the call site and introduces THAT: -/

elab "intro_as " n:ident : tactic =>
  liftMetaTactic fun goal => do
    let (_, goal) ← goal.intro n.getId          -- the user's own Name
    return [goal]

example : Nat → Nat := by
  intro_as k
  exact k                                       -- ✓ works: `k` came from the user

/-! ### §3.5  Syntactic categories (an aside worth ten minutes)

`term`, `tactic`, `command` are *syntactic categories*.  You can declare your
own, which is how DSLs (and `conv`, and `calc`) are built.  A miniature: -/

declare_syntax_cat arith
syntax:max num                    : arith
syntax:max "(" arith ")"          : arith
syntax:65 arith:65 " + " arith:66 : arith        -- left-assoc, precedence 65
syntax:70 arith:70 " * " arith:71 : arith        -- binds tighter
syntax "[arith| " arith "]"       : term         -- the door back into `term`

macro_rules
  | `([arith| $n:num])            => `($n)
  | `([arith| ($e:arith)])        => `([arith| $e])
  | `([arith| $a:arith + $b:arith]) => `([arith| $a] + [arith| $b])
  | `([arith| $a:arith * $b:arith]) => `([arith| $a] * [arith| $b])

#eval [arith| 2 * (3 + 4)]        -- 14

/-
The numbers are precedences: `syntax:65 arith:65 " + " arith:66` says "`+` is at
level 65, its left argument may be at level ≥65 and its right at ≥66", which is
exactly the encoding of *left associativity*.  Lean's own `infixl:65 " + "` does
the same thing.

Now note the important part: **`tactic` is just another category**, and `by` is
just a term-level door into it.  There is nothing magic about tactics.
-/
