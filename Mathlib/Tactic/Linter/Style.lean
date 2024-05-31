/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## Style linters

This file contains (currently one, eventually more) linters about stylistic aspects:
these are only about coding style, but do not affect correctness nor global coherence of mathlib.

Historically, these were ported from the `lint-style.py` Python script.
-/

open Lean Elab Command

namespace Mathlib.Linter.Style

/-- The `setOption` linter emits a warning on a `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option. -/
register_option linter.setOption : Bool := {
  defValue := true
  descr := "enable the `setOption` linter"
}

/-- The `lambdaFunction` linter emits a warning upon any use of the syntax `λ x => x` to define
anonymous functions. -/
register_option linter.lambdaFunction : Bool := {
  defValue := true
  descr := "enable the `lambdaFunction` linter"
}

namespace SetOption

/-- Whether a syntax element is a `set_option` command, tactic or term:
Return the name of the option being set, if any. -/
def parse_set_option : Syntax → Option (Ident)
  -- This handles all four possibilities of `_val`: a string, number, `true` and `false`.
  | `(command|set_option $name:ident $_val) => some name
  | `(set_option $name:ident $_val in $_x) => some name
  | `(tactic|set_option $name:ident $_val in $_x) => some name
  | _ => none

/-- Whether a given piece of syntax is a `set_option` command, tactic or term. -/
def is_set_option : Syntax → Bool :=
  fun stx ↦ parse_set_option stx matches some _name

/-- Gets the value of the `linter.setOption` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.setOption o

/-- The `setOption` linter: this lints any `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.

**Why is this bad?** These options are good for debugging, but should not be
used in production code.
**How to fix this?** Remove these options: usually, they are not necessary for production code.
(Some tests will intentionally use one of these options; in this case, simply allow the linter.)
-/
def setOptionLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some (head) := stx.find? is_set_option then
      if let some (name) := parse_set_option head then
        -- Drop a leading backtick.
        let name := (toString name).drop 1
        if name.startsWith "pp." || name.startsWith "profiler." || name.startsWith "trace." then
          Linter.logLint linter.setOption head m!"Forbidden set_option `{name}`; please remove"

initialize addLinter setOptionLinter

end SetOption

namespace AnonymousFunctions

/-- Whether a syntax element is an anonymous function. -/
def isAnonymousFunctionWithLambda : Syntax → Bool --:=
  | `(fun $_binders => $_body) => true
  -- | `(λ $_x => _) => true
  | _ => false--fun stx ↦ stx matches `(λ $_x => _) -- matches ↦ as well

/-- Gets the value of the `linter.lambdaFunction` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.lambdaFunction o

/-- The `lambdaFunction` linter: this lints any `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.

**Why is this bad?** These options are good for debugging, but should not be
used in production code.
**How to fix this?** Remove these options: usually, they are not necessary for production code.
(Some tests will intentionally use one of these options; in this case, simply allow the linter.)
-/
def lambdaFunctionLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some (head) := stx.find? isAnonymousFunctionWithLambda then
      Linter.logLint linter.lambdaFunction head m!"Anonymous function syntax with λ is deprecated\
                                                   Please use the `fun` keyword instead"

initialize addLinter lambdaFunctionLinter

end AnonymousFunctions

end Mathlib.Linter.Style
