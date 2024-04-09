import Lean
import Std.Tactic.PermuteGoals
--import Mathlib.Algebra.Group.Units
import Mathlib.Tactic.MoveAdd
import Mathlib.Tactic.Use
--import Mathlib.Tactic.Congrm
--import Mathlib.Tactic.Abel
--import Mathlib.Tactic.Ring
--import Mathlib.Tactic.Convert
import Mathlib.adomaniLeanUtils.inspect_syntax
--import Mathlib.adomaniLeanUtils.inspect
--import Mathlib.Tactic.FlexibleLinter
--import Mathlib.Tactic.SyntaxDataLinter
--import Mathlib.Tactic.TerminalRefineLinter
--import Mathlib.Tactic.RefineLinter
--import Mathlib.Tactic.SwapVar
--import Mathlib.Tactic.Common
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Nat.Parity
--import Mathlib.Tactic.FunProp
--import Mathlib.Tactic.UnusedTactic
import Mathlib.adomaniLeanUtils.tips
--import Mathlib.Tactic
--import Lake
--set_option linter.generic false
--inspect
/- notation for `True` -/

#check Lean.Parser.Tactic.tacticSeq
#check Array.insertAt!

instance : ToString Ordering where
  toString | .lt => "<" | .eq => "=" | .gt => ">"

open Lean Parser Elab Command Tactic
def Lean.Syntax.insertAt (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
  -- we check if `t1` is a `tacticSeq` and further split on whether it ends in `;` or not
  match t1 with
    | .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null args]] =>
      let (noOfTacs, trail?) := ((args.size + 1) / 2, args.size % 2 == 0)
      let nargs := match compare n noOfTacs, trail? with
        | .lt, _     => (args.insertAt! (2 * n - 1) mkNullNode).insertAt! (2 * n) t2
        | _,   true  => args.push t2
        | _,   false => (args.push mkNullNode).push t2
      .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null nargs]]
    | _ => t1

def Lean.Syntax.insertRight (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
  match t1 with
    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
      t1.insertAt (((args.size + 1)/ 2) - n) t2
    | _ => t1

elab "insert " t1:tactic " in " tac:tacticSeq : tactic => do
  let fin : TSyntax ``tacticSeq := ⟨(tac.raw.insertAt 0 t1).insertRight 0 (← `(tactic| done))⟩
  evalTactic fin

elab "test_mdata " tac:tacticSeq : tactic => do
  let fin : TSyntax ``tacticSeq :=
    ⟨(tac.raw.insertAt 0 (← `(tactic| have := 0))).insertRight 0 (← `(tactic| done))⟩
  logInfo fin
  evalTactic fin <|> logWarning "is mdata correctly handled?"

def test_fvs (tac : TSyntax ``tacticSeq) : TacticM String := do
  let ctx ← getLCtx
  for d in ctx.fvarIdToDecl do
    if  (d.2.kind == .default) then
      let nid := mkIdent d.2.userName
      evalTactic (← `(tactic| set $nid := $nid))
  (do evalTactic tac; return "") <|> pure "missing withContext?"


elab "test_fvs " tac:tacticSeq : tactic => do
--  let gs ← getGoals
--  let s ← saveState
  let ctx ← getLCtx
--  let fvs := ctx.fvarIdToDecl --.toArray --.filter (·.2.kind == .default)
  for d in ctx.fvarIdToDecl do
    if  (d.2.kind == .default) then
      let nid := mkIdent d.2.userName
      evalTactic (← `(tactic| set $nid := $nid))
  evalTactic tac <|> logWarning "missing withContext?"
  evalTactic (← `(tactic| repeat sorry))

elab "test_all" tac:tacticSeq : tactic => do
  let s ← saveState
  --liftCommandElabM do
  let mut msgs := {}
  for test in [← `(tactic| test_fvs $tac)] do
--  for test in [← `(tactic| test_mdata $tac), ← `(tactic| test_fvs $tac)] do
    dbg_trace "testing {test}\n"
    evalTactic test
    msgs := msgs.append (← get).messages
    restoreState s
  restoreState s
  evalTactic tac

example {a b : Nat} : 9 + a + b = b + a + 9 := by
  test_fvs
    move_add [← 9]
    move_add [← a]
    rfl


---  dbg_trace fvs.map (·.2.userName)


elab "buggy_exact " h:ident : tactic => do
  let ctx ← getLCtx
  dbg_trace ctx.fvarIdToDecl.toArray.map (·.2.userName)
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      -- warning: syntactic matching of the target
      if (← getMainTarget) == h1.type then
--        replaceMainGoal (← (← getMainGoal).apply r)
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

#check Expr.applyFVarSubst
#check FVarIdSet
#check Expr.hasFVarEx
#check Expr.hasFVar



#check CollectFVars.State.fvarSet
example {a b : Nat} : 9 + a + b = b + a + 9 := by
  test_all
    move_add [← 9]
    move_add [← a]
    rfl
  done
#exit
  set f := a
  test_fvs
    move_add [← 9]
    move_add [← a]
    rfl

#exit
  run_tac do
    let fvs := (← getThe Lean.CollectFVars.State).fvarSet
    let tgt ← getMainTarget
    dbg_trace tgt.hasFVar
  --apply congr_arg id ?_
  suffices 9 + a + b = b + a + 9 by
     stop
     have := this false
     rw [false_eq_true]
     simpa
  suffices ∀ t : Bool, (t ∨ 9 + a + b = b + a + 9) by
     stop
     have := this false
     rw [false_eq_true]
     simpa
  intro t
  induction t
  right
--  rw [true_and]
  --intro x
  --induction x
  move_add [← 9]
  move_add [← a]
  rfl
  --stop
  apply Or.inr
  move_add [← 9]
  move_add [← a]
  rfl
  stop
  induction b
  · --repeat
    move_add [← 9]
    move_add [← a]
    rfl
  · --repeat
    move_add [← 9]
    move_add [← a]
    rfl


example {h : True} {_j : False} : True := by
  test_mdata exact h

example {h : True} {_j : False} : True := by
  test_mdata buggy_exact h

example {h : True} {_j : False} : True := by
  insert have := 0 in buggy_exact h

example {h : True} {_j : False} : True := by
  insert apply _ in buggy_exact h

example {h : True} {_j : False} : True := by
--  have := 0
--  simp at this
--  apply _
  buggy_exact h
--  exact h


      --evalTactic (← `(exact h1))

elab "insr " n:num tac:tacticSeq : tactic => do
  let t2 ← `(tactic| assumption)
  let t2 ← `(tactic| refine ?_)
  let t2 ← `(tactic| skip)
  let fin : TSyntax ``tacticSeq := ⟨tac.raw.insertRight n.getNat t2⟩
  logInfo fin
--  dbg_trace fin
  evalTactic fin

example {h : True} {k : ¬ ¬ True} : True := by
  insr 2
    refine ?_
    rw [← Classical.not_not (a := True)]
    simp
    done
    done

#check numLit

elab "ins " n:num tac:tacticSeq : tactic => do
  let t2 ← `(tactic| refine ?_)
  let t2 ← `(tactic| assumption)
  let fin : TSyntax ``tacticSeq := ⟨tac.raw.insertAt n.getNat t2⟩
  logInfo fin
--  dbg_trace fin
  evalTactic fin

example {h : True} {k : ¬ ¬ True} : True := by
  ins 0
    refine ?_
    rw [← Classical.not_not (a := True)]
    simp
    done
    done;

#exit
