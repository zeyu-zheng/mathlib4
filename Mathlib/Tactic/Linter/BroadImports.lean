/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Init

/-! # docstrings

todo!
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The `broadImports` linter flags ... TODO!. -/
register_option linter.broadImports : Bool := {
  defValue := false
  descr := "enable the `broadImports` linter"
}

namespace broadImports

--@[inherit_doc linter.cdot]
def broadImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.broadImports (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let imports := (← getEnv).header.imports
    -- TODO: do all the analysis I wanted...

    for s in unwanted_cdot stx do
      Linter.logLint linter.cdot s m!"Please, use '·' (typed as `\\.`) instead of '{s}' as 'cdot'."
    -- We also check for isolated cdot's, i.e. when the cdot is on its own line.
    for cdot in Mathlib.Linter.findCDot stx do
      match cdot.find? (·.isOfKind `token.«· ») with
      | some (.node _ _ #[.atom (.original _ _ afterCDot _) _]) =>
        if (afterCDot.takeWhile (·.isWhitespace)).contains '\n' then
          logWarningAt cdot m!"This central dot `·` is isolated; please merge it with the next line."
      | _ => return

initialize addLinter broadImportsLinter

end broadImports

end Mathlib.Linter.broadImports
