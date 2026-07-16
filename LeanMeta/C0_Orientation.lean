import Lean
/-!
# Chapter 0. Orientation: what metaprogramming is, the four monads, and a Lean primer

Part of **Lean 4 Metaprogramming for Mathematicians**.  Read the chapters in
order (C0…C7).  Cross-references like "§5.2" use the section numbers that run
through the whole tutorial: §N lives in Chapter N.  Each chapter has matching
files in `Exercises/` and `Solutions/`.

This chapter is the on-ramp.  It has two jobs.  §0.1 to §0.3 tell you *what a
tactic really is* and the three languages Lean uses internally.  §0.4 is a from-zero
primer on the handful of *programming* ideas the rest of the tutorial needs;
you know the mathematics, so we spend our effort motivating the programming.
Every idea gets a reason for existing and, where we can, an analogy you already
own.  §0.5 shows a complete, working tactic so the goal is concrete.
-/
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
--------------------------------------------------------------------------------
§0.  ORIENTATION
--------------------------------------------------------------------------------

§0.1  What "metaprogramming" means, and why you would want it
-------------------------------------------------------------
You have typed `by ring`, `by simp`, `by linarith` hundreds of times.  Here is
the fact that this whole tutorial rests on: *someone wrote those tactics, in Lean,
and you can too.*  `ring` is not a built-in keyword blessed by the compiler; it is
an ordinary Lean program that someone defined in an ordinary Lean file.  So are
`simp`, the elaborator, and the parser.  None of them is privileged.

    A tactic is a program that builds a proof for you.
    "Metaprogramming" = writing programs whose data is other Lean code
    (proofs, terms, goals).  A tactic is the main example.

Why write your own?  Because every field has a repetitive proof pattern that no
existing tactic captures: discharging a side condition your objects always
satisfy, normalizing an expression in your favourite algebra, closing a family of
goals that all look the same.  A custom tactic turns "twenty tedious lines I keep
retyping" into one word.  By the end of this tutorial you will have written
`mytauto`, a real prover that closes propositional goals on its own (Chapter 6).

Mental model: an ordinary function transforms *data* into *data*.  A tactic is a
function that transforms *the state of an unfinished proof* into *a more finished
one*.  That is the only new idea; everything else is machinery for expressing it.

§0.2  The pipeline: three languages, one referee
------------------------------------------------
When you type `example : 2 + 2 = 4 := by rfl`, your text passes through three
stages.  It helps to see them as three *languages*:

    source text            "2 + 2 = 4"          <- what you TYPED
        │  parser
        ▼
    Syntax          a raw parse tree.  Dumb, untyped, just nested tokens.
        │  elaborator   (this is where tactics run)
        ▼
    Expr            the core language: everything Lean actually MEANS.
        │  kernel       (a tiny, paranoid proof checker)
        ▼
    accepted / rejected

Analogy for a mathematician: `Syntax` is the *notation you wrote on the page*;
`Expr` is the *mathematical object that notation denotes*; the kernel is the
*referee* who checks the finished proof and trusts nobody.  "Elaboration" is the
work of turning notation into meaning, and it is where all the interesting
decisions (what does `+` mean here? which `2`?) get made.

  * `Syntax` is what you *wrote*.
  * `Expr` is what Lean *means*.  Every proof term is an `Expr`.
  * The kernel re-checks every finished `Expr` from scratch, so a buggy tactic can
    never make Lean accept a false theorem: the worst it can do is fail or produce
    a term the kernel rejects.  This is why writing tactics is *safe* to
    experiment with.

Why is a *proof* an `Expr`, the same kind of object as `2 + 2`?  Because of the
principle Lean is built on: **a proof of a proposition `P` is a value whose type
is `P`**.  You already rely on this every time you write `example : a = a := rfl`:
the value `rfl` *is* the proof, and its type is `a = a`.  So "a tactic builds a
proof" means, concretely, "a tactic builds an `Expr` whose type is the goal".
That is the whole game.

A tactic sits in the middle stage: it reads `Syntax` (its own arguments) and
produces `Expr` (a piece of the proof term), a bit at a time.

Why keep two representations at all?  Because text is ambiguous: `2 + 2` does not
record which `+`, over which type, or with which implicit arguments, and the same
notation can mean different things in different contexts.  Resolving all of that is
exactly elaboration's job, and it needs a fully pinned-down target to resolve
*into*, which is `Expr`.  That is why turning `Syntax` into `Expr` is real work,
not relabelling.

⚑ TRAP #1, and the most common beginner confusion: mixing up `Syntax` and `Expr`.
They are different types with different purposes.  `Syntax` is text-shaped (it
knows you wrote a "+"); `Expr` is meaning-shaped (it knows you meant `Nat.add`).
The whole job of elaboration is to turn the first into the second.  Chapter 3 is
about `Syntax`; Chapter 1 is about `Expr`.

§0.3  The four monads (a first look; the word "monad" is defined in §0.4(h))
----------------------------------------------------------------------------
To do its job a tactic must reach into Lean's internals: the list of every known
theorem, the hypotheses of the current goal, the half-built proof.  Different
tasks need different amounts of that machinery, so Lean's API is organized into
four nested layers.  Think of them, for now, as *four levels of access*; §0.4(h)
explains what the "M" and the word "monad" actually mean, and you should re-read
this table after reading it.  Skim it now, do not study it: every term in the
middle column is defined later (`whnf`/`inferType`/`isDefEq` in §2, coercions and
instance synthesis in §4).  Read it only for its shape, four nested layers each
adding power, and hold on to just one row for now: `MetaM`.

    ┌───────────────┬────────────────────────────────┬──────────────────────────┐
    │ Layer         │ Gives you access to            │ You use it for           │
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

They are nested: `CoreM ⊆ MetaM ⊆ TermElabM ⊆ TacticM` (read `⊆` as "lifts into",
not literal set inclusion).  Anything you can do in a smaller layer you can do in a
bigger one (Lean inserts the conversion for you); not the other way round.  Practically you will live in `MetaM` (the real work) and
`TacticM` (the thin outer shell that talks to the goal list).

(`CommandElabM` sits off to the side: it is the layer of top-level commands like
`#check` and `def`, things that run once at the top level rather than inside a
proof.)

DESIGN RULE that every real tactic follows, and that we follow too:
    Put the *logic* of your tactic in `MetaM`, working on one goal.
    Put only *argument parsing and goal bookkeeping* in `TacticM`.
Why: `MetaM` logic is reusable by other tactics, testable in isolation with
`#eval`, and uncluttered by front-end concerns.  Lean's own `apply` is built
exactly this way: the logic (`MVarId.apply`) lives in `Lean/Meta/Tactic/Apply.lean`
and the thin syntactic wrapper (`evalApply`) in `Lean/Elab/Tactic/ElabTerm.lean`.
-/

/-!
### §0.4  The Lean behind the tactics: a primer

You already write Lean *statements* and `by` blocks, so you know functions,
types, and `∀`/`→`.  Meta-code is written in the *programming* fragment of the
same language, which you may never have touched.  Good news: it is small.  This
section is a self-contained tour of every construct the rest of the tutorial
uses.  For each one we say **why it exists** before we say what it does, and we
lean on mathematical analogies wherever one is honest.  Read it once, refer back
freely.  Every snippet runs: put your cursor on each `#eval` and read the
Infoview.

────────────────────────────────────────────────────────────────────────────────
(a)  Definitions and functions
────────────────────────────────────────────────────────────────────────────────
Nothing new conceptually: these are functions, as in mathematics.  `def name :
Type := value` names a value; a function type is written with `→`; and
`fun x => ...` is an anonymous function, exactly the "x ↦ ..." of maths. -/

def twice (n : Nat) : Nat := n + n      -- the function n ↦ n + n, of type Nat → Nat
#eval twice 21                          -- 42

#eval (fun (n : Nat) => n + 1) 10       -- 11   (apply an anonymous function to 10)

/-! One habit to absorb: **application is juxtaposition**.  You write `f x`, not
`f(x)`, and `f x y` for two arguments (this is "currying"; think of `f` as taking
`x` and returning a function of `y`).  That is why throughout this tutorial you
see `mkAppM ``Nat.add #[a, b]` and never `mkAppM(...)`: the parentheses you are
used to are simply not part of the syntax.

────────────────────────────────────────────────────────────────────────────────
(b)  Dot notation and namespaces
────────────────────────────────────────────────────────────────────────────────
Why it exists: purely readability.  A *namespace* groups related names
(`String.length`, `List.map`, `Nat.succ`), and dot notation lets you drop the
namespace when the type is obvious from the value.  If `x : T`, then `x.f a` means
`T.f x a`: Lean slots `x` in as the first explicit argument of type `T`. -/

#eval "hello".length                    -- 5    same as  String.length "hello"
#eval [1, 2, 3].length                  -- 3    same as  List.length [1, 2, 3]

/-! This matters only because meta-code is *drenched* in it.  When you later read
`goal.getType`, that is literally `MVarId.getType goal`; `ldecl.type` is
`LocalDecl.type ldecl`; `e.getAppFn` is `Expr.getAppFn e`.  The two forms are
interchangeable; `x.f` is just the one that reads left-to-right like a sentence.

────────────────────────────────────────────────────────────────────────────────
(c)  Pattern matching = definition by cases
────────────────────────────────────────────────────────────────────────────────
Why it exists: you already define functions by cases in mathematics ("f(n) = this
if n = 0, that otherwise").  `match` is exactly that, except the cases split on
the *constructor* that built the value.  A type is specified by listing the ways to
build its values, its *constructors* (think "generators"): every `Nat` is either
`0` or a successor `n + 1`; every `Option` is either `none` or `some a`.  `match`
asks which constructor produced the value and binds its parts; `_` is a wildcard
matching anything.  You can fold the cases straight into a `def` by listing them as
`| pattern => result`. -/

def describeNat : Nat → String
  | 0     => "zero"
  | 1     => "one"
  | _ + 1 => "many"          -- matches any successor n+1; the `_` ignores which one

#eval describeNat 0          -- "zero"
#eval describeNat 7          -- "many"

/-! This is not a minor convenience: it is *the* tool for taking data apart.  An
`Expr` (Chapter 1) is built by one of twelve constructors, and every function that
inspects a proof works by `match`-ing on which one.  So this small construct is
how all tactic logic reads its input.

A leading dot, as in `.bvar i`, is *dot notation for constructors*: when Lean
already knows the expected type (say `Expr`), it looks the name up in that type's
namespace, so `.bvar i` means `Expr.bvar i`.  You will see this constantly in
Chapter 1.  (It is unrelated to the angle-bracket *anonymous constructor* `⟨a, b⟩`,
which builds a value with several fields at once; same word "constructor",
different notation.)

────────────────────────────────────────────────────────────────────────────────
(d)  `Option`: how a total language expresses a partial function
────────────────────────────────────────────────────────────────────────────────
This is the first genuinely programming-flavoured idea, so here is the full
motivation.

In Lean, every function is **total**: `f : A → B` must return a genuine `B` for
*every* input, with no exceptions, no crash, no "null".  Totality is not a
nuisance; it is what makes the logic sound (a function that could silently fail to
return would let you "prove" nonsense).  But many natural operations are
inherently **partial**: "the first element of a list" is undefined on the empty
list; "the theorem named `n`" fails if no such theorem exists; "the two sides of
the equation `e`" makes no sense if `e` is not an equation.  A tactic does this
kind of partial lookup constantly.

How do you write a *total* function for a *partial* operation?  You enlarge the
codomain.  Instead of `A → B`, you return `A → Option B`, where

    Option B  has exactly two shapes:   some b   (a genuine value b : B)
                                        none     (no value)

For a mathematician this is precise: a partial function `f : A ⇀ B` is the same
data as a total function `A → B ⊔ {⊥}`, sending undefined inputs to the extra
point `⊥`.  `Option B` *is* that `B ⊔ {⊥}`: `some b` is a defined value, `none`
is `⊥`.  So `Option` is simply how Lean makes partiality honest without giving up
totality.  (Algebraic geometers may prefer the picture of a rational map `X ⇢ Y`,
defined on an open set and undefined on its indeterminacy locus; same intuition.) -/

def firstOfList : List Nat → Option Nat
  | []      => none          -- undefined on the empty list
  | x :: _  => some x        -- `x :: xs` is "head x, tail xs"; return the head

#eval firstOfList [3, 4, 5]  -- some 3
#eval firstOfList []         -- none

/-! Why not just use a "null" value or throw an exception, as other languages do?
Because the *type* `Option B` forces the issue: you cannot use an `Option Nat`
where a `Nat` is expected without first saying what to do when it is `none`.  The
compiler will not let you forget the missing case.  "I forgot to handle failure"
becomes a type error you see immediately, instead of a crash you discover later.
That safety is exactly what you want when your program is manufacturing proofs.

To *use* an `Option`, you take it apart with the `match` from (c): -/

def doubleFirst (xs : List Nat) : Option Nat :=
  match firstOfList xs with
  | some x => some (x + x)   -- there was a value: double it, still inside Option
  | none   => none           -- there was none: pass the absence along

#eval doubleFirst [10, 20]   -- some 20
#eval doubleFirst []         -- none

/-! From Chapter 5 on, you will see a one-line shorthand for the "get the value or
bail out" pattern, written `let some x := e | fallback` (if `e` is not `some ...`,
run `fallback` instead).  It does the same thing as the `match` above and lives
inside a `do` block, which we reach in (h).  We will use it to say things like
"the goal had better be an equality; if it is not, fail with an error".

────────────────────────────────────────────────────────────────────────────────
(e)  `List` and `Array`: two kinds of finite sequence
────────────────────────────────────────────────────────────────────────────────
Both are finite sequences; they differ only in machine representation, and you
care about the difference only because the API forces a choice.
  * `[1, 2, 3]` is a `List`: a linked chain of `head :: tail` cells.  It is the
    "inductive sequence" you pattern-match on (as `firstOfList` did with `x :: _`).
  * `#[1, 2, 3]` is an `Array`: a flat contiguous block, fast to index and append.
Meta-code uses `Array` for things like a function's argument list (`mkAppN f
#[a, b, c]`) because it is efficient, and `List` for the goal list because it is
convenient to pattern-match.  Both support `.length`/`.size`, `.map`, `.foldl`,
and `for` loops, so in practice you rarely think about the distinction. -/

#eval #[10, 20, 30].size     -- 3
#eval #[10, 20, 30][1]!      -- 20   (`arr[i]!` indexes; the `!` means "trust i is in range")

/-!
────────────────────────────────────────────────────────────────────────────────
(f)  Structures = tuples with named fields
────────────────────────────────────────────────────────────────────────────────
Why it exists: convenience and readability, nothing deep.  A `structure` is a
labelled tuple.  Where a mathematician writes an element of `ℕ × ℕ` and remembers
"first coordinate, second coordinate", a structure lets you *name* the
coordinates.  You build one with `{ field := value, ... }` and read a field back
with dot notation (b). -/

structure Point where
  x : Nat
  y : Nat

def origin : Point := { x := 0, y := 0 }
#eval origin.x               -- 0

/-! This matters because most of the meta-objects you will handle are structures,
and you read them by their field names.  A hypothesis is a `LocalDecl` with fields
`.userName` and `.type`; the result of a rewrite is a structure with a field
`.eNew` (the rewritten expression); and so on.  When you see `x.someField`, it is
just a projection out of such a record.

────────────────────────────────────────────────────────────────────────────────
(g)  Type classes = "this type comes equipped with ..."
────────────────────────────────────────────────────────────────────────────────
Here the mathematical analogy is exact and worth stating.  In algebra you say "let
`G` be a group", meaning `G` is a type *together with* a distinguished operation,
identity, and inverse satisfying axioms.  A **type class** is precisely the
"together with" part: a bundle of operations a type may be *equipped with*, which
Lean can look up automatically.

You have already been writing them: in `theorem foo (R : Type) [CommRing R] : ...`,
the `[CommRing R]` says "Lean must find a commutative-ring structure on `R`", and
instance search supplies it silently (an *instance* is one specific such
equipment).  You have used them without the brackets too: `2 + 2` works because
`Nat` is equipped with an `Add` instance; the same `+` means a different operation
on `Int`
or on a polynomial ring, resolved by which `Add` instance the type carries, just
as `+` in maths means different things on different structures.  `{n}` inside a
message works because there is a `ToMessageData` instance saying how to display
`n`. -/

#eval (2 : Int) + (3 : Int)  -- 5   (`+` here is Int's `Add` instance)

/-! You will rarely *define* a class when writing tactics, but you constantly rely
on them.  For instance `mkAppM` (Chapter 1) uses the ambient instances to fill in
a function's implicit and typeclass arguments for you.  And when you read a
signature with a square-bracketed argument like `[Monad m]` or `[ToString α]`,
that bracket is a *class constraint*: "this works for any type that is equipped
with the such-and-such structure".  It is the code version of "for any group G".

────────────────────────────────────────────────────────────────────────────────
(h)  THE BIG ONE: monads and `do`-notation
────────────────────────────────────────────────────────────────────────────────
This is the one genuinely new concept, and the whole tutorial leans on it, so we
build it from a monad you have ALREADY met in part (d): `Option`.

START WITH `Option`.  Recall `firstOfList : List Nat → Option Nat`, a partial
function.  Suppose you want to compose it with "double the result".  You cannot
just apply `double`, because the first step might be `none`; you must unwrap the
`some` and pass the `none` through.  That is exactly what `doubleFirst` in (d) did
by hand:

    match firstOfList xs with | some x => some (x + x) | none => none

Compose three such partial steps, or five, and you get a staircase of identical
`... | none => none` boilerplate burying the one line you care about.  A monad's
whole job is to write that boilerplate ONCE.

The operation that does it is `bind`, written `>>=`.  For `Option`, `x >>= f` is
*defined* to be that very match:

    x >>= f   =   match x with | some a => f a | none => none

"if `x` has a value, feed it to `f`; if not, stay `none`".  So `bind` is what lets
you *chain* partial computations: it feeds the value out of one step into the next
partial function `f : α → Option β`, threading the `none` for you.  (To literally
compose two partial functions `g` and `h`, you write `fun a => g a >>= h`.)  With it,
`doubleFirst` becomes a one-liner, no match in sight: -/

def doubleFirst' (xs : List Nat) : Option Nat :=
  firstOfList xs >>= fun x => some (x + x)

#eval doubleFirst' [10, 20]   -- some 20
#eval doubleFirst' []         -- none   (the `none` was threaded for you)

/-! Two more names finish the vocabulary.  `pure a` injects a plain value as a
trivial computation; for `Option`, `pure a = some a` (and `return` is the same).
And `do` with `←` is just readable sugar for chains of `>>=`, by the single rule

    do (let a ← x; rest)   ≡   x >>= (fun a => rest)

so `let x ← firstOfList xs` reads "run `firstOfList xs`; if `some x`, bind `x` and
continue; if `none`, the whole block is `none`".  Here is the same function a third
time, now with neither `>>=` nor `match`: -/

def doubleFirst'' (xs : List Nat) : Option Nat := do
  let x ← firstOfList xs        -- unwraps the `some`, threads the `none`
  pure (x + x)

#eval doubleFirst'' [10, 20]  -- some 20

/-! THE PATTERN, once and for all.  A *monad* is any type constructor `m` (an operation
on types, sending `α` to a new type `m α`, just as `Option` sends `Nat` to
`Option Nat`) equipped with

    pure : α → m α                       -- inject a plain value
    bind : m α → (α → m β) → m β          -- written `>>=`; compose two steps

(obeying a couple of common-sense laws).  What changes from one monad to the next
is the *invisible plumbing* that `bind` threads for you:

    Option   threads "might be absent"          (bind short-circuits on `none`)
    MetaM    threads "read/write Lean's state, and may fail"   (the one we need)
    IO       threads "the outside world",   and so on.

The good news: `do`, `←`, `pure`, `return` mean the SAME thing in every monad; only
what `bind` threads underneath changes.  So once you can read a `do` block over
`Option`, you can read one over `MetaM`.  (If you know "monad" from category theory,
yes it is that, but you need none of the theory here.)

`MetaM`, THE ONE YOU WILL USE.  A tactic is not a pure `input → output` function: to
work it must READ Lean's hidden state (the environment of all definitions, the
goal's hypotheses, the current metavariable assignments), MODIFY some of it
(assigning a metavariable fills in part of the proof), and it may FAIL.  Written
with plain functions, even `inferType e` would have to take the whole state and
return any part it touched, and you would thread the versions by hand:

    -- the nightmare a monad saves you from (pseudocode):
    --   inferType : Env → LCtx → MCtx → Expr → (Expr × Env × LCtx × MCtx)
    --   let (a, s1) := step1 s0
    --   let (b, s2) := step2 s1   -- must pass s1 (not s0), and short-circuit on failure
    --   ...

`MetaM` is `Option`'s trick with a richer effect: `MetaM α` is a recipe that, run
against Lean's current state, yields an `α` (or fails), possibly updating that
state, and `bind` threads that state (and the failure) for you.  Concretely,
`let a ← step` is the same `>>=` as before, except now `>>=` also hands the updated
state (the `s1` of the pseudocode above) to the next step, exactly the plumbing you
would otherwise thread by hand.  A clean picture: think of `MetaM α` as a function
`LeanState → (α × LeanState)` that might throw; `do`
composes such functions, feeding each one's output state to the next.  You never
write `LeanState`.  This demystifies §0.3: `CoreM ⊆ MetaM ⊆ TermElabM ⊆ TacticM` are
the same idea with progressively more state in that `LeanState`.  (`Unit` is the
one-element type, the analogue of "void"; a `MetaM Unit` is run only for its effect.)

THE MECHANICS.  Inside a `do` block there are exactly two kinds of "let", and
telling them apart is the single most important skill:

    let x ← step      -- step : m α.  RUN it (this is `bind`); x : α.       (effectful)
    let x := value    -- value : α already.  Just name it; nothing runs.    (pure)

The arrow `←` (type it `\l`, or ASCII `<-`) is "run this computation and give me its
result".  A few more forms:

    step              -- run `step`, ignore its result (used for its effect)
    return v / pure v -- the trivial recipe that just yields v
    (← step)          -- run `step` right here and drop in its result;
                      --   `foo (← bar)` is short for `let t ← bar; foo t`

Here is a real `MetaM` computation, every line annotated.  `logInfo` prints to the
Infoview; `mkAppM`, `inferType`, `whnf` are the real API you meet in Chapter 1. -/

#eval show MetaM Unit from do
  let e     ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]  -- RUN: build the term `2 + 3`
  let ty    ← inferType e                                  -- RUN: ask Lean its type
  let value ← whnf e                                       -- RUN: compute it to a normal form
  let label := "result"                                    -- pure: just a String, no ←
  logInfo m!"{label}: {e} : {ty}  ⇝  {value}"              -- result: Nat.add 2 3 : Nat  ⇝  5

/-! `show MetaM Unit from do ...` only tells Lean which monad this bare `#eval`
block lives in; inside a `def` with a declared return type, or inside a tactic,
Lean already knows, and you just write `do`.

(The `let some x := e | fallback` shorthand promised in (d) is just this Option-`do`
short-circuit with a custom `none` branch: if `e` is not `some ...`, run `fallback`.)

The remaining `do` constructs, all of which appear later:

    for x in xs do <body>     -- iterate; xs a List/Array/range
    continue  /  break        -- next iteration / leave the loop early
    let mut acc := 0          -- a locally mutable variable (only inside do)
    acc := acc + 1            -- reassign it
    if c then <a> else <b>    -- `else` optional when the block's type is Unit
    unless c do <a>           -- run <a> only when c is false
    try <a> catch e => <b>    -- run <a>; if it fails, run <b>

⚑ One reflex to unlearn: a `let mut` name is a *storage cell*, not a mathematical
variable.  `total := total + i` is not a (false) equation; it *overwrites* the
cell with a new value each pass of the loop.  Such cells exist only inside a `do`
block.

A tiny loop, again in `MetaM`: -/

#eval show MetaM Unit from do
  let mut total : Nat := 0                 -- ⚑ annotate `: Nat`; see the note below
  for i in [1, 2, 3, 4] do
    total := total + i
  logInfo m!"sum = {total}"                -- sum = 10

/-! ⚑ TRAP #2 (you will hit this): give a `let mut` counter an explicit type, as in
`let mut total : Nat := 0`.  Without it, Lean may guess the type from a *later* use
(for instance from a `m!"..."` message) and infer something absurd like
`MessageData`, producing a baffling "failed to synthesize OfNat …" error pointing
at the `:= 0`.  When a numeric `let mut` misbehaves, annotate its type first.

That is the whole of it.  Every tactic in this tutorial is a `do` block in one of
the four monads.  `do` is nothing more than "run this, then that, naming results
as we go", with the state threaded for you.  The one reflex to build: **a line
with `←` runs a computation; a line with `:=` binds a plain value.**  Come back to
this box any time a `do` block starts to look like magic.

FOR READERS WHO ALREADY KNOW THE WORD "monad" (everyone else: skip this paragraph,
you need none of it).  Yes, this is the category-theorists' monad.  If the bridge
helps: `MetaM` is the endofunctor `α ↦ MetaM α`; `pure` / `return` is the unit η;
`x ← step` desugars to bind (`>>=`), the Kleisli extension; a whole `do` block is
composition in the Kleisli category; `join` is μ.  The unit and associativity laws
you know are exactly what make `do` blocks compose without surprises.

────────────────────────────────────────────────────────────────────────────────
(i)  `s!` versus `m!`: printing strings vs printing meaning
────────────────────────────────────────────────────────────────────────────────
Why two: a meta-object like an `Expr` or a goal only makes sense *in a context*
(which notation is in scope, what the bound variables are called).  `s!"x = {e}"`
builds a plain `String` and prints `e` in a raw, context-free internal form (ugly,
often unreadable).  `m!"x = {e}"` builds a `MessageData`, which defers rendering
until it can pretty-print `e` in the right context, with real notation and names.
Rule of thumb with no exceptions in this tutorial: for anything meta, use `m!`. -/

/-! ### §0.5  First contact

You now have every ingredient.  Here is a complete, working tactic.  It does
nothing useful (it just prints the goal and leaves it untouched), but it is a
*real* tactic, and you can read every part of it.  Notice the `do`, the `←`, and
the `m!` from §0.4. -/

/-- `hello` prints the current goal and changes nothing. -/
elab "hello" : tactic => do
  let goal ← getMainGoal          -- RUN: fetch the goal; `goal : MVarId` (a metavariable)
  logInfo m!"Hello!  The main goal is:\n{goal}"

example (n : Nat) : n + 0 = n := by
  hello                            -- ← put your cursor here and read the Infoview
  rfl

/-
Three things to notice, because they recur everywhere:

  1. `elab "hello" : tactic => do ...` declares, in one stroke, BOTH a new piece
     of syntax (the keyword `hello`, in the `tactic` category) AND the code that
     runs when Lean sees it.  It is convenient sugar; §5.1 shows the longer form
     it expands to, which is what you will meet when reading Lean's own source.

  2. `getMainGoal : TacticM MVarId`.  The goal comes back as a *metavariable*.
     This is the crucial identification of the subject ("a goal IS a hole to be
     filled"); §2 explains it in full.  For now: a goal is a value you can inspect.

  3. `logInfo m!"..."` (from §0.4(i)) prints the goal pretty.  Swap in `s!"..."`
     and you would see raw internal junk instead; that is the whole reason `m!`
     exists.

Next stop: Chapter 1, where we open up `Expr`, the language every proof is
written in.
-/
