import Lean
import Std.Tactic.PermuteGoals
--import Mathlib.Algebra.Group.Units
import Mathlib.Tactic.MoveAdd
import Mathlib.Tactic.Use
--import Mathlib.Tactic.Congrm
--import Mathlib.Tactic.Abel
--import Mathlib.Tactic.Ring
--import Mathlib.Tactic.Convert
--import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect
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

elab "buggy_exact " h:ident : tactic => do
  let ctx ← getLCtx
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      -- warning: syntactic matching of the target
      if (← getMainTarget) == h1.type then
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

elab "less_buggy_exact " h:ident : tactic => withMainContext do
  let ctx ← getLCtx
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      -- warning: syntactic matching of the target
      if (← getMainTarget) == h1.type then
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

elab "md_exact " h:ident : tactic => withMainContext do
  let ctx ← getLCtx
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      -- warning: syntactic matching of the target
      if (← getMainTarget).consumeMData == h1.type then
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

def testTactic (tac : TSyntax ``tacticSeq) (test : MessageData) (fail success : Option MessageData := none) :
    TacticM (Option MessageData) := withoutModifyingState do
  let str ← (do evalTactic tac
                trace[Tactic.tests] (checkEmoji ++ m!" {test}")
                return success) <|>
            (do trace[Tactic.tests] (crossEmoji ++ m!" {test}")
                return fail)
  return str

elab "tryme " tac:tacticSeq : tactic => do
  logInfo m!"{(← testTactic tac "testing me" "i failed" "i succeeded")}"
#check Meta.getLevelMVarDepth
set_option trace.Tactic.tests true
example : True := by
  tryme assumption
  tryme exact 0
  tryme exact .intro
  exact .intro

def testMData (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := do
  let fin : TSyntax ``tacticSeq :=
    ⟨(tac.raw.insertAt 0 (← `(tactic| have := 0))).insertRight 0 (← `(tactic| done))⟩
  testTactic fin "add 'have := 0'" m!"is mdata correctly handled? {fin}"

open Meta in
def testFVs (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := --Meta.withNewMCtxDepth do
withoutModifyingState do withMainContext do
  let ctx ← getLCtx
  let mut repls := #[]
  let carr := ctx.fvarIdToDecl.toArray
  let Typ ← inferType (.const ``Nat [])
  let mut typs : HashSet Expr := HashSet.empty.insert Typ
  for (_, d) in carr do
    typs := typs.insert (d.type)
  let nonSort ← carr.filterM fun (_, d) =>
    return d.binderInfo != .instImplicit &&
      d.kind == .default && d.type.ctorName != "sort" && !(← inferType d.type).isProp
--  dbg_trace "nonSort: '{nonSort.map (·.2.userName)}'"
  let mut (ntac, con) := (tac.raw, 0)
  for (_, d) in nonSort do
    let typ ← inferType d.type
    if true || ((d.kind == .default) && (typ == Typ || !typ.isProp)) then
--      dbg_trace (← ppExpr d.type, ← ppExpr typ)
      let nid := mkIdent d.userName
      repls := repls.push (← `(tactic| set $nid := $nid))
      ntac := ntac.insertAt con (← `(tactic| set $nid := $nid))
      con := con + 1
  testTactic ⟨ntac⟩ m!"{repls}" m!"missing withContext? {ntac}"

open Meta in
def testInstMVs (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) :=
withoutModifyingState do withMainContext do
  let mut ctx ← getLCtx
--  let mut repls := #[]
  let carr := ctx.fvarIdToDecl.toArray
  let props ← carr.filterM fun d => return d.2.kind == .default && ((← inferType d.2.type).isProp)
  let ids ← props.mapM fun _ => return mkIdent (← mkFreshId)
  dbg_trace ids
  dbg_trace ← props.mapM fun (_, d) => ppExpr d.type
  let mut t1 := tac.raw
  let mut repls := #[]
  for (newId, (_, decl)) in ids.zip props do
    let oldId := mkIdent decl.userName
--    let newId := mkIdent `hello
    t1 ← t1.replaceM fun s => do return if s == oldId then some newId else none
    repls := repls.push (← `(tactic| have $newId := $oldId ))
    t1 := t1.insertAt 0 (← `(tactic| have $newId := $oldId ))
    ctx ← getLCtx
--    t1 := t1.insertAt 0 (← `(tactic| clear $oldId ))
  t1 := t1.insertRight 0 (← `(tactic| done))
  dbg_trace t1
--  dbg_trace t1
  --withMainContext do
  testTactic ⟨t1⟩ m!"{indentD t1}" m!"missing instantiateMVars? {t1}"
--  evalTactic t1
--  return default
/-
  let mut typs : HashSet Expr := HashSet.empty
  for (_, d) in carr do
    typs := typs.insert (d.type)
  let nonSort ← carr.filterM fun (_, d) =>
    return d.binderInfo != .instImplicit &&
      d.kind == .default && d.type.ctorName != "sort" && !(← inferType d.type).isProp
--  dbg_trace "nonSort: '{nonSort.map (·.2.userName)}'"
  let mut (ntac, con) := (tac.raw, 0)
  for (_, d) in nonSort do
    let typ ← inferType d.type
    if true || ((d.kind == .default) && (typ == Typ || !typ.isProp)) then
--      dbg_trace (← ppExpr d.type, ← ppExpr typ)
      let nid := mkIdent d.userName
      repls := repls.push (← `(tactic| set $nid := $nid))
      ntac := ntac.insertAt con (← `(tactic| set $nid := $nid))
      con := con + 1
  testTactic ⟨ntac⟩ m!"{repls}" m!"missing withContext? {ntac}"
-/

elab "now " tac:tacticSeq : tactic => do
  logInfo m!"{← testInstMVs tac}"
  evalTactic tac

example {a : Nat} (h : a + 0 = a) : a + 0 = a := by
  have := 0
  have h' := h
  buggy_exact h        -- mdata
  buggy_exact h'       -- missing context
  less_buggy_exact h'  -- mvars not instantiated
  md_exact h'          -- further evidence of mvars
  md_exact h           -- dealing with mdata


example {a : Nat} (ha : a = 0) : a = 0 := by
now
--  have h := ha  -- `h` is a metavariable
--  clear ha
  md_exact ha


elab "tests " tk:"!"? tac:tacticSeq : tactic => do
  let _ ← for test in [testMData, testFVs, testInstMVs] do
    if let some str := ← test tac then
      logWarningAt (← getRef) str
  match tk with
    | none => evalTactic tac
    | some _ => return

macro "tests! " tac:tacticSeq : tactic => `(tactic| tests ! $tac)

set_option trace.Tactic.tests true
example {j : Bool} {h : True} : True := by
  tests buggy_exact h

example {h : True} : True := by
  tests less_buggy_exact h

example {h : True} : True := by
  tests md_exact h

set_option trace.Tactic.tests true
example {a b : Nat} : 9 + a + b = b + a + 9 := by
  tests
    move_add [← 9]
    move_add [← a]
    rfl

/-- converts
* `theorem x ...` to  `some (example ... , x)`,
* `lemma x ...`   to  `some (example ... , x)`,
* `example ...`   to ``some (example ... , `example)``,
*  everything else goes to `none`.
-/
def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers lemma $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers example $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | _ => return none

elab "test " cmd:command : command => do
  if let some (_, id) ← toExample cmd then
    trace[Tactic.tests] m!"testing {id}"
  let ncmd ← cmd.replaceM fun x => do
    if x.getKind == ``tacticSeq then
      let xs := ⟨x⟩
      return some (x.insertAt 0 (← `(tactic| tests! $xs))) else return none
--  logInfo ncmd
  elabCommand ncmd

def linterTest : Linter where run := withSetOptionIn fun cmd => do
  if let some (cmd, _) ← toExample cmd then
    let cmd := ⟨cmd⟩
    elabCommand (← `(test $cmd))
--    let ncmd ← cmd.replaceM fun x => do
--      if x.getKind == ``tacticSeq then
--        let xs := ⟨x⟩  -- convert `x` to a `tacticSeq`
--        return some (x.insertAt 0 (← `(tactic| tests! $xs))) else return none
--    if ncmd != cmd then elabCommand cmd
  --else logInfo "skipped"
initialize addLinter linterTest

/-
node Lean.Parser.Command.declaration, none
|-node Lean.Parser.Command.declModifiers, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|-node Lean.Parser.Command.theorem, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'theorem'
                                            |   |-node Lean.Parser.Command.declId, none
                                            |   |   |-ident original: ⟨⟩⟨ ⟩-- (hif,hif)
                                            |   |   |-node null, none
|   |-node Lean.Parser.Command.declSig, none
|   |   |-node null, none
|   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |-ident original: ⟨⟩⟨ ⟩-- (True,True)


node Lean.Parser.Command.declaration, none
|-node Lean.Parser.Command.declModifiers, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|   |-node null, none
|-node Lean.Parser.Command.example, none
|   |-atom original: ⟨⟩⟨ ⟩-- 'example'
|   |-node Lean.Parser.Command.optDeclSig, none
|   |   |-node null, none
|   |   |-node null, none
|   |   |   |-node Lean.Parser.Term.typeSpec, none
|   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
|   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (True,True)
-/


test
--inspect
theorem hif {n m : Nat} {n m : Int} : True := .intro

test
--inspect
lemma f {n m : Nat} {n m : Int} : True := .intro

inspect
example {n : Nat} := True.intro

test
example : True := by
  exact .intro
  skip

-- `goal does not match` --> not dealing with `mdata`?
example {a : Nat} (h : a = 0) : a = 0 := by
  have := 0
  buggy_exact h

-- `goal does not match` --> missing `instantiateMVars`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  have h := ha  -- `h` is a metavariable
  clear ha
  inspect h
  md_exact h

-- `hypothesis 'h' not found` --> missing `withMainContext`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  --have := 0
  have h := ha
  clear ha
  inspect h
  buggy_exact h

set_option trace.Tactic.tests true
test
example {j : Bool} {h : True} : True := by
  buggy_exact h

test
example {a b : Nat} : 9 + a + b = b + a + 9 := by
  move_add [← 9]
  move_add [← a]
  rfl


open Classical in
example {p q : Prop} (h : 1 = 1) (h1 : False) (hp : p) (hq : q) : (if p ∧ q then 1 else 0) = 1 := by
  -- split_ifs creates a hypothesis with a type that's a metavariable
  split_ifs
  · buggy_exact h
  · buggy_exact h1




#exit

elab "insert " t1:tactic " in " tac:tacticSeq : tactic => do
  let fin : TSyntax ``tacticSeq := ⟨(tac.raw.insertAt 0 t1).insertRight 0 (← `(tactic| done))⟩
  evalTactic fin

def test_mdata (tac : TSyntax ``tacticSeq) : TacticM (Option String) := do
  let fin : TSyntax ``tacticSeq :=
    ⟨(tac.raw.insertAt 0 (← `(tactic| have := 0))).insertRight 0 (← `(tactic| done))⟩
  let tst := "add 'have := 0'"
  (do evalTactic fin
      trace[Tactic.tests] "unsuccessful {tst}"
      return none) <|>
  (do trace[Tactic.tests] "successful {tst}"
      return some "is mdata correctly handled?")

elab "test_mdata " tac:tacticSeq : tactic => do
  let fin : TSyntax ``tacticSeq :=
    ⟨(tac.raw.insertAt 0 (← `(tactic| have := 0))).insertRight 0 (← `(tactic| done))⟩
  logInfo fin
  evalTactic fin <|> logWarning "is mdata correctly handled?"

def test_fvs (tac : TSyntax ``tacticSeq) : TacticM (Option String) := do
  let ctx ← getLCtx
  let mut repls := #[]
  for d in ctx.fvarIdToDecl do
    if (d.2.kind == .default) then
      let nid := mkIdent d.2.userName
      repls := repls.push d.2.userName
      evalTactic (← `(tactic| set $nid := $nid))
  trace[Tactic.tests] "{repls.map fun v => m!"set {v} = {v}"}"
  (do evalTactic tac; return none) <|> pure "missing withContext?"


elab "tests " tac:tacticSeq : tactic => do
  let s ← saveState
  let mut strs := #[]
  for test in [test_fvs, test_mdata] do
    strs := strs.push (← test tac)
  restoreState s
  let msgs := strs.reduceOption
  for m in msgs do logWarning m!"{m}"
  evalTactic tac

set_option trace.Tactic.tests true
example {a b : Nat} : 9 + a + b = b + a + 9 := by
  tests
    move_add [← 9]
    move_add [← a]
    rfl




elab "test_fvs " tac:tacticSeq : tactic => do
  let s ← saveState
  let str ← test_fvs tac
  restoreState s
  if h : str.isSome then logWarning m!"{str.get h}"
  evalTactic tac

--  let gs ← getGoals
/-
  let ctx ← getLCtx

--  let fvs := ctx.fvarIdToDecl --.toArray --.filter (·.2.kind == .default)
  for d in ctx.fvarIdToDecl do
    if  (d.2.kind == .default) then
      let nid := mkIdent d.2.userName
      evalTactic (← `(tactic| set $nid := $nid))
  evalTactic tac <|> logWarning "missing withContext?"
  evalTactic (← `(tactic| repeat sorry))
-/

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
set_option trace.Tactic.tests true
example {a b : Nat} : 9 + a + b = b + a + 9 := by
  test_fvs
    move_add [← 9]
    move_add [← a]
    rfl


---  dbg_trace fvs.map (·.2.userName)


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
