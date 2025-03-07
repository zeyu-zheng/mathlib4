import Lean

open Lean

def toUserNameSet (env : Environment) : NameSet :=
  env.constants.fold (init := ∅) (fun tot nm _ =>
    if nm.isInternalDetail then tot else tot.insert nm)

def declsFromImports (imports : Array Import) : IO NameSet := do
  let env1 ← importModules (leakEnv := false) imports {}
  pure <| toUserNameSet env1

elab "ddiff" : command => withoutModifyingEnv do
  let modA : Import := `Mathlib.Algebra.Quandle
  let fnameA : System.FilePath := "Mathlib" / "Algebra" / "Quandle.lean"

  let m1 ← IO.Process.run {cmd := "lake", args := #["build", toString modA]}
  dbg_trace "m1: '{m1}'"

  let e1 ← declsFromImports #[modA]
  dbg_trace "Found {e1.size} declarations"

  dbg_trace "git checkout master {fnameA}"
  let m2 ← IO.Process.run {cmd := "git", args := #["checkout", "master", fnameA.toString]}
  dbg_trace "m2: '{m2}'"

  dbg_trace "lake exe cache get {modA}"
  let m3 ← IO.Process.run {cmd := "lake", args := #["exe", "cache", "get", fnameA.toString]}
  dbg_trace "m3: '{m3}'"

  let e2 ← declsFromImports #[modA]
  dbg_trace "Found {e2.size} declarations"
  logInfo m!"{(e1.diff e2).toArray}, {(e2.diff e1).toArray}"
