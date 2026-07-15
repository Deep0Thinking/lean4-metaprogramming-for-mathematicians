import Lean
/-!
# Chapter 3. `Syntax`: the front end (quotations, macros, hygiene)

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

Chapters 1 and 2 were about *meaning*: `Expr`, and the goals you fill.  This
chapter is about the other language, `Syntax`: the raw notation you type, before
it means anything.  Why care about mere notation?  Because the cheapest and safest
tactics never build a proof term at all; they just rewrite the notation you typed
into other notation Lean already understands.  That rewrite is a *macro*, and it is
the first kind of tactic you should reach for.  This chapter covers what `Syntax`
is, how to build and match it with *quotations*, how to write a macro, the one
genuine surprise (*hygiene*), and how to invent your own notation.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§3.  `Syntax`: THE FRONT END
--------------------------------------------------------------------------------

§3.1  The type
--------------
When you type `1 + 2 * 3`, the parser turns those characters into a tree, without
yet knowing what `+` means, which `+` it is, or what types are involved.  That raw
tree is a `Syntax`.  It is deliberately dumb: it records "you wrote a `+` with these
two operands" and nothing more.  Compare with an `Expr`, which records the *meaning*
(`HAdd.hAdd` over `Nat`, with instances resolved).  The analogy from Chapter 0
holds: `Syntax` is the notation on the page, `Expr` is the object it denotes, and
elaboration (Chapter 4) is the bridge.  The full ladder, three representations and
then a value, is:

    characters  "1 + 2 * 3"
        │  parse
        ▼
    Syntax      the tokens and their grouping (a `+` whose right operand is `2 * 3`)
        │  elaborate
        ▼
    Expr        which `+`, over which type, with which instance: HAdd.hAdd 1 (HMul.hMul 2 3)
        │  evaluate
        ▼
    the value   7

Precedence (that `*` groups before `+`) is decided in the *parse* step; it shapes
the `Syntax` tree, and from then on the grouping is explicit in both `Syntax` and
`Expr`.

`Syntax` has just four constructors: -/

#print Lean.Syntax

/-
    .missing               -- a parse error, or an absent optional piece
    .node info kind args   -- an internal node, tagged with a SyntaxNodeKind (a Name)
    .atom info val         -- a token: "+", "by", "("
    .ident info _ name _   -- an identifier

`TSyntax c` is a `Syntax` carrying a compile-time TAG `c` saying which *syntactic
category* it belongs to (a grammar bucket like `term` / `tactic` / `command`; see
§3.5).  `TSyntax `term`` is a term-shaped tree, `TSyntax `tactic``
a tactic-shaped one.  The tag is a phantom label the Lean type system checks (`.raw`
strips it back to plain `Syntax`); its whole purpose is to stop you from, say,
splicing a tactic into a position where a term is required.  Think of it as a typed
wrapper around an otherwise untyped tree.

Let us see a real tree.  `describeSyntax` is a recursive printer like `describeExpr`
from Chapter 1; `partial` tells Lean not to worry about proving it terminates
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
  let stx ← `(1 + 2 * 3)          -- a *quotation* (see §3.2): builds Syntax, does NOT elaborate
  logInfo m!"pretty : {stx.raw}"  -- 1 + 2 * 3
  logInfo (describeSyntax stx.raw)

/-
Read that output.  You are looking at the parse tree, with the node kinds the
parser assigned (`«term_+_»`, `«term_*_»`, `num`).  Those ugly kind names are the
labels that `macro_rules` and `@[tactic ...]` dispatch on, the way you would branch
on a constructor.  Notice the tree already groups `2 * 3` under the `+` (precedence,
see §3.5); the notation's structure is captured, but none of its meaning is.

§3.2  Quotations and antiquotations: templates for `Syntax`
-----------------------------------------------------------
You could build a `Syntax` by hand out of `.node`s and `.atom`s, but that is as
painful as it sounds.  A *quotation* lets you instead write the ordinary surface
notation and have Lean hand you the corresponding parse tree:

    `(1 + 1)                  -- a `TSyntax `term`
    `(tactic| rfl)            -- a `TSyntax `tactic`
    `(command| def x := 1)    -- a `TSyntax `command`

The `category|` prefix says which parser to use; a bare `` `(...) `` means a term.
A quotation is a *template*.  Like a fill-in-the-blank (or a Python f-string), it can
contain holes: `$x` splices another piece of syntax into the template (this is an
*antiquotation*), and `$xs,*` splices a comma-separated list of them.  (Unlike an
f-string, `$x` must itself be a piece of `Syntax`, not an arbitrary value.)  The
alternative to quotation is assembling `.node`s and `.atom`s by hand: the
`describeSyntax` tree printed just above is exactly what `` `(1 + 2 * 3) `` builds
for you, `SourceInfo` and all, which is why nobody writes it out by hand. -/

#eval show CoreM Unit from do
  let x ← `(37)
  let stx ← `($x + $x)              -- fill the template `_ + _` with 37 on both sides
  logInfo m!"{stx.raw}"             -- 37 + 37

/-! The same quotations work in reverse, as *patterns*: you can `match` a `Syntax`
against `` `(...) `` and bind the antiquotations to the matched pieces.  This is how
a macro recognizes the shape it should rewrite. -/

#eval show CoreM Unit from do
  let stx ← `(1 + 2)
  match stx with
  | `($a + $b) => logInfo m!"a sum: left = {a}, right = {b}"   -- a sum: left = 1, right = 2
  | _          => logInfo "not a sum"

/-! ### §3.3  Your first tactic: a macro

A *macro* is a rule `Syntax → Syntax`: "wherever you see this notation, replace it
with that notation".  It is the tactic-writer's abbreviation, exactly like defining
`notation` for a term.  It never touches `Expr` or `MetaM`, which makes it the
shortest, safest, and cheapest kind of tactic.  Rule of thumb: **if your tactic is
just a combination of existing tactics, write a macro.** -/

macro "obvious" : tactic => `(tactic| first | rfl | assumption | trivial)

example (p : Prop) (hp : p) : p := by obvious   -- expands to: first | rfl | assumption | trivial
example : 2 + 2 = 4 := by obvious
example : True := by obvious

/- The two-step form does the same thing, and you will see it in real code: first
`syntax` declares the new token, then `macro_rules` gives one or more expansion
rules.  In each rule the `` `(...) `` on the LEFT of `=>` is a *pattern* (the
matching use from §3.2) and the one on the RIGHT is a *builder*.  Reach for this
two-step form (over `macro`) when one notation needs SEVERAL rules, or when you want
to declare a notation in one place and give its meaning elsewhere; you will see
exactly that in §3.5, where one `arith` syntax gets four `macro_rules` cases.  A
`macro` is just the one-rule shorthand. -/

syntax "obvious2" : tactic                      -- declare the syntax...
macro_rules                                     -- ...and how to expand it
  | `(tactic| obvious2) => `(tactic| first | rfl | assumption | trivial)

example (p : Prop) (hp : p) : p := by obvious2

/-! ### §3.4  Hygiene  (⚑ TRAP #10, and it surprises everyone)

Run the next example and read the comment: the `h` that `intro_h` introduces is
*not* accessible as `h` afterward. -/

macro "intro_h" : tactic => `(tactic| intro h)

example : Nat → Nat := by
  intro_h
  -- exact h        -- ✗ ERROR: unknown identifier 'h'.  The `h` above is NOT this `h`.
  exact 0

-- The other direction is protected too: a user's `h` is safe from a macro's `h`.
example (h : Nat) : Nat → Nat := by
  intro_h        -- the macro introduces its OWN fresh (inaccessible) `h`
  exact h        -- ✓ still resolves to the USER's `h : Nat`, untouched by the macro

/-
Why?  This is *hygiene*, and it is the same problem you already met in Chapter 1.
There, bound variables were made nameless (de Bruijn indices) so that substitution
could never accidentally *capture* a variable.  Here the danger is a macro's
identifiers colliding with the user's: if `intro_h` introduced a plain `h`, it might
silently shadow an `h` you already had, or be captured by one you write later.  Lean
prevents this by secretly stamping every identifier a macro creates with a "macro
scope", so a macro-made `h` and a user-written `h` are, to Lean, different names that
can never collide.  Same disease (variable capture), same philosophy of cure (make
the names guaranteed-distinct).  The mechanism differs, though: de Bruijn removed
names entirely, whereas hygiene *keeps* the name `h` and adds an invisible scope (an
automatic α-rename; the macro's version even prints as `h✝`).

That is a feature: your macro can never accidentally shadow the user's variables.
But sometimes you *do* want to introduce a name the user chose.  Then you must take
the identifier from the user's own syntax, because it carries the user's scopes, not
the macro's.  The next tactic reads an identifier `n` from the call site and
introduces THAT name: -/

elab "intro_as " n:ident : tactic =>
  liftMetaTactic fun goal => do
    let (_, goal) ← goal.intro n.getId          -- the user's own Name, with the user's scopes
    return [goal]

example : Nat → Nat := by
  intro_as k
  exact k                                       -- ✓ works: `k` came from the user

/-! Notice this one is `elab`, not `macro`.  A macro can only rewrite notation into
*existing* notation, and no existing tactic introduces a caller-chosen name, so
there is nothing to rewrite into; we drop down and call `intro` ourselves.  The line
is: `macro` = pure `Syntax → Syntax`; `elab` = do real elaboration work (Chapter 4).

### §3.5  Syntactic categories, and precedence you already know

`term`, `tactic`, `command` are *syntactic categories*: the different kinds of
notation Lean parses.  You can declare your own category, which is exactly how DSLs
(and `conv`, and `calc`) are built.  Here is a miniature arithmetic language. -/

declare_syntax_cat arith
syntax:max num                    : arith
syntax:max "(" arith ")"          : arith
syntax:65 arith:65 " + " arith:66 : arith        -- `+` at precedence 65 (looser)
syntax:70 arith:70 " * " arith:71 : arith        -- `*` at precedence 70 (binds tighter)
syntax "[arith| " arith "]"       : term         -- a door from `arith` back into `term`

/-! In the rules below, `$n:num` and `$a:arith` are antiquotations *pinned to a
category*: `$n:num` matches (or requires) only syntax of category `num`, `$a:arith`
only `arith`.  You add the `:cat` suffix when Lean cannot infer the hole's category
by itself, as it cannot inside our custom `[arith| ...]` bracket. -/

macro_rules
  | `([arith| $n:num])            => `($n)
  | `([arith| ($e:arith)])        => `([arith| $e])
  | `([arith| $a:arith + $b:arith]) => `([arith| $a] + [arith| $b])
  | `([arith| $a:arith * $b:arith]) => `([arith| $a] * [arith| $b])

#eval [arith| 2 * (3 + 4)]        -- 14
#eval [arith| 2 * 3 + 4]          -- 10, read as (2 * 3) + 4   (`*` binds tighter, no parens)
#eval [arith| 2 + 3 * 4]          -- 14, read as 2 + (3 * 4)

/-
Those numbers after the colons are *operator precedence*, the same convention you
use by hand, with one rule: **a higher number binds tighter**.  `*` sits at 70 and
`+` at 65, so `*` wins and `2 + 3 * 4` parses as `2 + (3 * 4)` with no parentheses;
the two parens-free `#eval`s above show it, `2 * 3 + 4` coming out 10, not 14.
(`:max`, used on the number and parenthesis rules, is the tightest level of all, so
those forms always parse no matter what surrounds them.)

The small asymmetry in `syntax:65 arith:65 " + " arith:66` encodes *left*
associativity, and you can derive it: a `+`-expression itself sits at level 65, but
the right operand of `+` is required to be at level ≥ 66.  Since 65 < 66, another
bare `+` cannot attach on the right, so it is forced to nest on the left, giving
`(a + b) + c`.  Flip the two numbers and you would get right associativity instead.
Lean's built-in `infixl:65 " + "` is shorthand for exactly this.

The punchline of the chapter: **`tactic` is just another syntactic category**, and
`by` is simply a term-level door into it, the same kind of door `[arith| ... ]` is
into `arith`.  There is nothing magic about tactics; they are notation like any
other, which is why you can define your own.
-/
