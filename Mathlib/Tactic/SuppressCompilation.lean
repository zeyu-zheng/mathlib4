/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Mac Malone
-/
import Mathlib.Init
import Lean.Elab.Declaration
import Lean.Elab.Notation

/-!
# Suppressing compilation to executable code in a file or in a section

Currently, the compiler may spend a lot of time trying to produce executable code for complicated
definitions. This is a waste of resources for definitions in area of mathematics that will never
lead to executable code. The command `suppress_compilation` is a hack to disable code generation
on all definitions (in a section or in a whole file). See the issue https://github.com/leanprover-community/mathlib4/issues/7103

To compile a definition even when `suppress_compilation` is active, use
`unsuppress_compilation in def foo : ...`. This is activated by default on notations to make
sure that they work properly.

Note that `suppress_compilation` does not work with `notation3`. You need to prefix such a notation
declaration with `unsuppress_compilation` if `suppress_compilation` is active.
-/

open Lean Parser Elab Command

private def setDeclModifiersNoncomputable :
    TSyntax ``declModifiers → CommandElabM (TSyntax ``declModifiers)
  | `(declModifiers| $[$doc?:docComment]? $(attrs?)? $(vis?)? $[noncomputable]? $(unsafe?)?
      $(recKind?)?) =>
    `(declModifiers| $[$doc?:docComment]? $(attrs?)? $(vis?)? noncomputable $(unsafe?)?
      $(recKind?)?)
  | _ => throwUnsupportedSyntax

/-- Replacing `def` and `instance` by `noncomputable def` and `noncomputable instance`, designed
to disable the compiler in a given file or a given section.
This is a hack to work around https://github.com/leanprover-community/mathlib4/issues/7103. -/
def elabSuppressCompilationDecl : CommandElab := fun
| `($m:declModifiers $d:definition) => do
  let m ← setDeclModifiersNoncomputable m
  elabDeclaration <| ← `($m:declModifiers $d:definition)
| `($m:declModifiers $i:instance) => do
  let m ← setDeclModifiersNoncomputable m
  elabDeclaration <| ← `($m:declModifiers $i:instance)
| `($m:declModifiers $e:example) => do
  let m ← setDeclModifiersNoncomputable m
  elabDeclaration <| ← `($m:declModifiers $e:example)
| `($m:declModifiers $a:abbrev) => do
  let m ← setDeclModifiersNoncomputable m
  elabDeclaration <| ← `($m:declModifiers $a:abbrev)
| _ => throwUnsupportedSyntax

/-- The command `unsuppress_compilation in def foo : ...` makes sure that the definition is
compiled to executable code, even if `suppress_compilation` is active. -/
syntax "unsuppress_compilation" (" in " command)? : command

/-- Make sure that notations are compiled, even if `suppress_compilation` is active, by prepending
them with `unsuppress_compilation`. -/
def expandSuppressCompilationNotation : Macro := fun
| `($n:notation) => do
  let defn ← expandNotation <| ← `($n:notation)
  `(unsuppress_compilation in $(⟨defn⟩):command)
| _ => Macro.throwUnsupported

/-- Replacing `def` and `instance` by `noncomputable def` and `noncomputable instance`, designed
to disable the compiler in a given file or a given section.
This is a hack to work around https://github.com/leanprover-community/mathlib4/issues/7103.
Note that it does not work with `notation3`. You need to prefix such a notation declaration with
`unsuppress_compilation` if `suppress_compilation` is active. -/
macro "suppress_compilation" : command => do
  let declKind := mkIdent ``declaration
  let notaKind := mkIdent ``«notation»
  let declElab := mkCIdent ``elabSuppressCompilationDecl
  let notaMacro := mkCIdent ``expandSuppressCompilationNotation
  `(
  attribute [local command_elab $declKind] $declElab
  attribute [local macro $notaKind] $notaMacro
  )

/-- The command `unsuppress_compilation in def foo : ...` makes sure that the definition is
compiled to executable code, even if `suppress_compilation` is active. -/
macro_rules
| `(unsuppress_compilation $[in $cmd?]?) => do
  let declElab := mkCIdent ``elabSuppressCompilationDecl
  let notaMacro := mkCIdent ``expandSuppressCompilationNotation
  let attrCmds ← `(
    attribute [-command_elab] $declElab
    attribute [-macro] $notaMacro
  )
  if let some cmd := cmd? then
    `($attrCmds:command $cmd:command suppress_compilation)
  else
    return attrCmds
