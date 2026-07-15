import Lean
/-!
# Chapter 0. Orientation: what metaprogramming is, the four monads, and a Lean primer

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§0.  ORIENTATION
--------------------------------------------------------------------------------

§0.1  What "metaprogramming" means here
-----------------------------------------
Lean 4 is written in Lean 4.  The parser, the elaborator, `simp`, `ring`,
`linarith`: all of them are ordinary Lean programs living in ordinary Lean
files.  They are not privileged.  This has a consequence that is the single most
important idea in this file:

    A tactic is just a program that manipulates the proof state.
    You can write one, and it will be exactly as "real" as `simp`.

"Meta"-programming means: programs that manipulate programs.  When you write a
tactic, you write a program whose *data* is the proof you are building.

§0.2  The pipeline
------------------
When you type `example : 2 + 2 = 4 := by rfl`, Lean does this:

    source text
        │  parser
        ▼
    Syntax          -- a concrete syntax tree.  Dumb.  Untyped.  Just a tree.
        │  elaborator   (this is where tactics run)
        ▼
    Expr            -- the core language: λ-calculus + inductive types.
        │  kernel
        ▼
    accepted / rejected

  * `Syntax` is what you *wrote*.
  * `Expr` is what Lean *means*.  Proof terms are `Expr`s.
  * The kernel is the final, paranoid arbiter.  It re-checks every `Expr`.

A tactic sits in the middle box: it consumes `Syntax` (its own arguments) and
produces `Expr` (a proof term), incrementally.

⚑ TRAP #1 for beginners: confusing `Syntax` and `Expr`.  They are completely
different types.  `Syntax` is text-shaped; `Expr` is meaning-shaped.  The whole
job of "elaboration" is to turn the first into the second.

§0.3  The four monads
---------------------
Meta-code runs in a stack of "monads".  Do not worry about the word yet; §0.4
explains it.  For now: a monad is the *kind of computation* you are writing, and
each one gives you access to more of Lean's internal state.  You will constantly
need to know which one you are in, because that determines what you may call.

    ┌───────────────┬────────────────────────────────┬──────────────────────────┐
    │ Monad         │ Gives you access to            │ You use it for           │
    ├───────────────┼────────────────────────────────┼──────────────────────────┤
    │ CoreM         │ the environment (all declared  │ looking up constants     │
    │               │ constants), name generator     │                          │
    ├───────────────┼────────────────────────────────┼──────────────────────────┤
    │ MetaM         │ + local context, metavariables,│ EVERYTHING interesting:  │
    │               │   `whnf`, `inferType`,`isDefEq`│ this is the real API     │
    ├───────────────┼────────────────────────────────┼──────────────────────────┤
    │ TermElabM     │ + postponement, coercions,     │ elaborating user terms   │
    │               │   instance synthesis machinery │                          │
    ├───────────────┼────────────────────────────────┼──────────────────────────┤
    │ TacticM       │ + the list of *goals*          │ the tactic front end     │
    └───────────────┴────────────────────────────────┴──────────────────────────┘

They are nested: `CoreM ⊆ MetaM ⊆ TermElabM ⊆ TacticM`.  Anything you can do in
`MetaM` you can do in `TacticM` (it is lifted automatically).  Not conversely.

(`CommandElabM` sits off to the side: it is the monad of top-level commands like
`#check` and `def`.)

DESIGN RULE, and it is the rule real tactics follow:
    Put the *logic* of your tactic in `MetaM`, operating on an `MVarId`.
    Put only *argument parsing and goal juggling* in `TacticM`.
This makes your tactic reusable by other tactics.  All of Lean's own tactics are
built this way: `Lean/Meta/Tactic/Apply.lean` holds the logic (`MVarId.apply`), and
`Lean/Elab/Tactic/ElabTerm.lean` holds the thin syntactic wrapper (`evalApply`).
-/

/-!
### §0.4  The Lean behind the tactics: a primer

You already write Lean *statements* and `by` blocks.  Meta-code is written in the
*programming* fragment of the same language, which you may never have used.  This
section is a fast, self-contained tour of exactly the constructs the rest of the
file relies on.  Read it once; refer back as needed.  Every snippet runs; put
your cursor on each `#eval`.

────────────────────────────────────────────────────────────────────────────────
(a)  Definitions and functions
────────────────────────────────────────────────────────────────────────────────
`def name : Type := value` introduces a name.  A function type is written with
`→`, and an anonymous function ("lambda") with `fun x => ...`. -/

def twice (n : Nat) : Nat := n + n      -- a function Nat → Nat
#eval twice 21                          -- 42

#eval (fun (n : Nat) => n + 1) 10       -- 11   (apply an anonymous function)

/-! Application is by juxtaposition: `f x`, not `f(x)`.  Several arguments:
`f x y`.  This is why you will see `mkAppM ``Nat.add #[a, b]` and never
`mkAppM(...)`.

────────────────────────────────────────────────────────────────────────────────
(b)  Dot notation and namespaces
────────────────────────────────────────────────────────────────────────────────
A *namespace* groups names: `String.length`, `List.map`, `Nat.succ`.  If `x` has
type `T`, then `x.f a` means `T.f x a`: the value is slotted in as the first
explicit argument of the right type.  This is pure convenience, but it is
everywhere in meta-code. -/

#eval "hello".length                    -- 5    = String.length "hello"
#eval [1, 2, 3].length                  -- 3    = List.length [1, 2, 3]

/-! So when later you read `goal.getType`, that is exactly `MVarId.getType goal`;
`ldecl.type` is `LocalDecl.type ldecl`; `e.getAppFn` is `Expr.getAppFn e`.  Dot
notation and the fully-applied form are interchangeable.

────────────────────────────────────────────────────────────────────────────────
(c)  Pattern matching
────────────────────────────────────────────────────────────────────────────────
`match` inspects which *constructor* built a value and binds its fields.  `_` is
a wildcard that matches anything.  You can also match directly in a `def` by
writing the cases as `| pattern => result`. -/

def describeNat : Nat → String
  | 0     => "zero"
  | 1     => "one"
  | _ + 1 => "many"          -- `_ + 1` matches any successor; here we ignore it

#eval describeNat 0          -- "zero"
#eval describeNat 7          -- "many"

/-! A leading dot, as in `.bvar i`, is *dot notation*: when Lean already knows the
expected type (here `Expr`), it resolves the name in that type's namespace, so you
may write `.bvar i` for `Expr.bvar i`.  You will see this constantly in §1.  (Do
not confuse it with *anonymous-constructor* notation `⟨a, b⟩`, which builds a
structure or inductive value, a different feature that reuses the "anonymous" word.)

────────────────────────────────────────────────────────────────────────────────
(d)  `Option`: a value that might be absent
────────────────────────────────────────────────────────────────────────────────
`Option α` has two constructors: `some a` (a value) and `none` (nothing).  It is
Lean's type-safe replacement for "null".  Meta-code returns `Option` whenever a
lookup might fail. -/

def firstOfList : List Nat → Option Nat
  | []      => none
  | x :: _  => some x        -- `x :: xs` is "head `x`, tail `xs`"

#eval firstOfList [3, 4, 5]  -- some 3
#eval firstOfList []         -- none

/-! A very common idiom "get the value out, or bail out" is written with the
`let pattern := e | fallback` form: if `e` does *not* match `pattern`, the code
after `|` runs instead.  We will use this to say "the goal had better be an
equality; if not, fail." -/

def doubleFirst (xs : List Nat) : Option Nat := do
  -- (`do` blocks are explained in part (h) below.  For now just read the block
  --  top-to-bottom: its final line is the value it produces, and `Option` is
  --  itself one of the "monads" (h) describes.)
  let some x := firstOfList xs | none    -- if `firstOfList xs = none`, stop with `none`
  some (x + x)

#eval doubleFirst [10, 20]   -- some 20
#eval doubleFirst []         -- none

/-!
────────────────────────────────────────────────────────────────────────────────
(e)  `List` and `Array`
────────────────────────────────────────────────────────────────────────────────
`[1, 2, 3]` is a `List` (a linked list).  `#[1, 2, 3]` is an `Array` (a flat,
fast, indexable block).  Meta-code overwhelmingly uses `Array` for arguments,
e.g. `mkAppN f #[a, b, c]`, and `List` for the goal list.  Both support
`.length`/`.size`, `.map`, `.foldl`, and `for` loops. -/

#eval #[10, 20, 30].size     -- 3
#eval #[10, 20, 30][1]!      -- 20   (`[i]!` indexes, trusting `i` is in range)

/-!
────────────────────────────────────────────────────────────────────────────────
(f)  Structures and field access
────────────────────────────────────────────────────────────────────────────────
A `structure` bundles named fields.  You build one with `{ field := value, ... }`
and read a field with dot notation.  Many meta-objects are structures: a
hypothesis (`LocalDecl`) has a `.userName` and a `.type`; a rewrite result has a
`.eNew`; and so on. -/

structure Point where
  x : Nat
  y : Nat

def origin : Point := { x := 0, y := 0 }
#eval origin.x               -- 0

/-!
────────────────────────────────────────────────────────────────────────────────
(g)  Type classes (just enough)
────────────────────────────────────────────────────────────────────────────────
A *type class* is an interface Lean resolves automatically.  You have used them
without naming them: `2 + 2` works because `Nat` has an `Add` instance; `{n}` in
a message works because there is a `ToMessageData` instance.  You rarely define
classes when writing tactics, but you rely on them: e.g. `mkAppM` uses the
environment's instances to fill in a function's implicit and instance arguments
for you.  When you see `[Monad m]` or `[ToString α]` in a signature, that is a
class constraint: "there must be such an instance".

────────────────────────────────────────────────────────────────────────────────
(h)  THE BIG ONE: monads and `do`-notation
────────────────────────────────────────────────────────────────────────────────
This is the concept the rest of the file leans on hardest.  Take it slowly.

A value of type `MetaM α` is *a description of a computation* that, when Lean
runs it, may read and modify Lean's internal state (the environment, the local
context, metavariable assignments…) and finally produces a value of type `α`.
`MetaM Expr` = "a computation that yields an `Expr`".  `MetaM Unit` = "a
computation run only for its effect" (`Unit` is the boring one-element type, the
functional analogue of `void`).

You *assemble* such computations with `do`.  Inside a `do` block:

  • `let x ← step`   runs `step` (a computation) and binds its RESULT to `x`.
                     Use `←` (type it as `\l`, or write the ASCII `<-`) whenever
                     the right-hand side is itself a computation.
  • `let x := value` is ordinary let: `value` is a plain value, not a computation.
  • `step`           on its own runs `step` for its effect and discards the value.
  • `return v` / `pure v`  produces the value `v` with no effect; it is how a
                     `do` block of type `MetaM α` finally delivers its `α`.
  • `(← step)`       is shorthand: it runs `step` right there and substitutes its
                     result.  `foo (← bar)` means `let t ← bar; foo t`.

The single most important distinction, and the source of many beginner errors:

        let x ← step      -- `step : MetaM α`,  and `x : α`      (RUN it)
        let x := value    -- `value : α`,       and `x : α`      (do NOT run it)

Here is a runnable `MetaM` computation with every line annotated.  `logInfo`
prints to the Infoview; `mkAppM`, `inferType`, `whnf` are the real API from §1. -/

#eval show MetaM Unit from do
  let e     ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]  -- run: build `2 + 3`
  let ty    ← inferType e                                  -- run: get its type
  let value ← whnf e                                       -- run: compute it
  let label := "result"                                    -- plain value, no ←
  logInfo m!"{label}: {e} : {ty}  ⇝  {value}"              -- prints:  result: Nat.add 2 3 : Nat  ⇝  5

/-! `show MetaM Unit from do ...` just tells Lean which monad this block lives in
(you need it only for a bare `#eval`; inside a `def` with a declared type, or
inside a tactic, the monad is already known).

The other everyday `do` constructs, all of which you will meet below:

    for x in xs do <body>          -- iterate; `xs` a List/Array/range
    continue  /  break             -- skip to the next iteration  /  leave the loop early
    let mut acc := 0               -- a locally mutable variable (only inside do)
    acc := acc + 1                 -- reassign it
    if c then <a> else <b>         -- `else` optional when the type is `Unit`
    unless c do <a>                -- run `<a>` only when `c` is false
    try <a> catch e => <b>         -- run `<a>`; on error, run `<b>`

A tiny loop, again in `MetaM`: -/

#eval show MetaM Unit from do
  let mut total : Nat := 0                 -- ⚑ annotate `: Nat`; see the note below
  for i in [1, 2, 3, 4] do
    total := total + i
  logInfo m!"sum = {total}"                -- sum = 10

/-! ⚑ TRAP #2 (you will hit this): give a `let mut` counter an explicit type,
`let mut total : Nat := 0`.  Without it, Lean may guess the type from a *later*
use (e.g. inside a `m!"..."` message) and infer something absurd like
`MessageData`, giving a baffling "failed to synthesize OfNat …" error at the
`:= 0`.  When a numeric `let mut` misbehaves, annotate its type first.

Every tactic in this file is a `do` block in one of the four monads.  That is all
`do` is: a readable way to write "run this, then run that, binding results along
the way".  If a line has a `←`, it runs a computation; if it has `:=`, it does
not.  Return to this box whenever a `do` block looks like magic.

────────────────────────────────────────────────────────────────────────────────
(i)  `s!` versus `m!`
────────────────────────────────────────────────────────────────────────────────
`s!"x = {e}"` builds a plain `String`.  `m!"x = {e}"` builds a `MessageData`,
which knows how to pretty-print meta-objects (`Expr`s, goals) *in the right
context*: with notation, bound-variable names, the works.  For anything
meta, always use `m!`; `s!` will print ugly, context-free internal forms. -/

/-! ### §0.5  First contact

Here is a complete, working tactic.  It does nothing but print the goal.
Read it, then hover over every identifier in it. -/

/-- `hello` prints the current goal and changes nothing. -/
elab "hello" : tactic => do
  let goal ← getMainGoal          -- : MVarId (the goal, as a metavariable)
  logInfo m!"Hello!  The main goal is:\n{goal}"

example (n : Nat) : n + 0 = n := by
  hello                            -- ← put your cursor here and read the Infoview
  rfl

/-
Three things to notice, because they generalise:

  1. `elab "hello" : tactic => do ...` declares BOTH a piece of syntax (the
     keyword `hello`, in the syntactic category `tactic`) AND the code that runs
     when it is encountered.  It is sugar; §5.1 shows what it expands to.

  2. `getMainGoal : TacticM MVarId`.  The goal is a *metavariable*.  Internalise
     this now; §2 explains it properly.

  3. `logInfo` + `m!"..."` as introduced in §0.4(i): `m!` builds a `MessageData`
     that pretty-prints the goal correctly.  `s!"..."` would print internal junk.
-/
