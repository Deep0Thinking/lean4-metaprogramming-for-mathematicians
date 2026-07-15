import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-! # Solutions for Chapter 4 (Elaboration)

Compare with `Exercises/C4.lean`. -/

-- E1.  A term elaborator that computes at elaboration time.
elab "double% " n:num : term => return mkNatLit (2 * n.getNat)
#eval double% 21                 -- 42
example : double% 3 = 6 := rfl   -- the elaborator really doubled it

-- E2.  Like `sum%` (§4), but returns the LENGTH of the bracket list.
elab "len% " "[" xs:term,* "]" : term => return mkNatLit xs.getElems.size
#eval len% [10, 20, 30]          -- 3
#eval len% []                    -- 0

-- E3.  A command that reports whether a term is a proposition.
elab "#isProp " t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    logInfo m!"{e} : isProp = {← Meta.isProp e}"
#isProp True                     -- True : isProp = true
#isProp Nat                      -- Nat : isProp = false
