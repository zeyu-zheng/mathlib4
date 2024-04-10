import Mathlib.Tactic.Set
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.MoveAdd
import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.adomaniLeanUtils.inspect
import Mathlib.adomaniLeanUtils.tips  -- initialize the trace


instance : ToString Ordering where
  toString | .lt => "<" | .eq => "=" | .gt => ">"

open Lean Parser Elab Command Tactic
section low_level_syntax

namespace Lean

namespace Syntax

/-- assumes that `t1` is a tactic sequence and that `t2` is a single tactic.
Inserts `t2` as the `n`-th tactic of the sequence, defaulting to the last position
if `n` is larger than the number of tactics in the sequence `t1`. -/
def insertAt (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
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

/-- assumes that `t1` is a tactic sequence and that `t2` is a single tactic.
Inserts `t2` as the `n`-th tactic of the sequence from the bottom, defaulting to the first position
if `n` is larger than the number of tactics in the sequence `t1`. -/
def insertRight (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
  match t1 with
    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
      t1.insertAt (((args.size + 1)/ 2) - n) t2
    | _ => t1

/-- inserts all the tactics in the array `ts` at the beginning of the tactic sequence `tac`. -/
def insertMany (tac : Syntax) (ts : Array Syntax) : Syntax :=
  (Array.range ts.size).foldl (fun l r => l.insertAt r ts[r]!) tac

end Syntax

/-- inserts all the tactics in the array `ts` at the beginning of the tactic sequence `tac`. -/
def TSyntax.insertMany (tac : TSyntax ``tacticSeq) (ts : Array (TSyntax `tactic)) :
    TSyntax ``tacticSeq :=
  ⟨tac.raw.insertMany ts⟩

/-- inserts the tactic `ts` at the end of the tactic sequence `tac`. -/
def TSyntax.insertBack (tac : TSyntax ``tacticSeq) (ts : TSyntax `tactic) :
    TSyntax ``tacticSeq :=
  ⟨tac.raw.insertRight 0 ts⟩

end Lean

end low_level_syntax

/-
inspect
#check 3

def haves {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] (tac : TSyntax ``tacticSeq) (n : Nat) :
    m Syntax := do
  let ts ← (Array.range n).mapM fun i => do
    let j := Syntax.mkNumLit (toString i)
    `(tactic| have := $j)
  return (tac.raw.insertMany ts)

elab "h " n:num : command => do
  let tac ← `(tacticSeq| simp; done)
  let tac := (← `(tacticSeq| simp)).raw.insertAt 1 (← `(tactic| done))
  logInfo <| ← haves ⟨tac⟩ n.getNat

h 3

#eval show CoreM _ from do
--  let tac ← `(tacticSeq| simp; done)
  let tac := (← `(tacticSeq| simp)).raw.insertAt 1 (← `(done))
  logInfo <| ← haves ⟨tac⟩ 3
-/

elab "buggy_exact " md:"clearMD"? h:ident : tactic => do
  let ctx ← getLCtx
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      let tgt := if md.isNone then ← getMainTarget else (← getMainTarget).consumeMData
      -- warning: syntactic matching of the target
      if tgt == h1.type then
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

elab "ctx_buggy_exact " md:"clearMD"? h:ident : tactic => withMainContext do
  if md.isSome then evalTactic (← `(tactic| buggy_exact clearMD $h))
  else              evalTactic (← `(tactic| buggy_exact $h))

elab "less_buggy_exact " h:ident : tactic => withMainContext do
  evalTactic (← `(tactic| buggy_exact $h))

elab "md_exact " h:ident : tactic => withMainContext do
  evalTactic (← `(tactic| buggy_exact clearMD $h))

/--
warning: goal does not match
---
warning: hypothesis 'h'' not found
---
warning: goal does not match
---
warning: goal does not match
-/
#guard_msgs in
example {a : Nat} (h : a + 0 = a) : a + 0 = a := by
  have := 0
  have h' := h
  buggy_exact h        -- mdata  `goal does not match`
  buggy_exact h'       -- missing context  `hypothesis 'h'' not found`
  less_buggy_exact h'  -- mvars not instantiated  `goal does not match`
  md_exact h'          -- further evidence of mvars  `goal does not match`
  md_exact h           -- dealing with mdata

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

set_option trace.Tactic.tests true
/--
info: some (i failed)
---
info: some (i failed)
---
info: some (i succeeded)
---
info: [Tactic.tests] ❌ testing me
---
info: [Tactic.tests] ❌ testing me
---
info: [Tactic.tests] ✅ testing me
-/
#guard_msgs in
example : True := by
  tryme assumption
  tryme exact 0
  tryme exact .intro
  exact .intro

section tactic_modifications
variable {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m]

/-- adds `done` at the end of the given tactic sequence. -/
def addDone (tac : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) :=
  return tac.insertBack (← `(tactic| done))
  --return ⟨tac.raw.insertRight 0 (← `(tactic| done))⟩

/-- adds `have := 0` at the beginning and `done` at the end of the input tactic sequence.
When evaluating the resulting tactic, the goal acquires `mdata`
as a consequence of the `have := 0`. -/
def addHaveDone (tac : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) := do
  addDone (tac.insertMany #[(← `(tactic| have := 0))])

/-- adds at the beginning of the tactic sequence `tac` lines like `set x := x`,
where `x` is the username of each local declaration in `toSet`.
These `set`s introduce a layer of separation between the original names of the declarations
and the current ones.  This may help detect missing `withContext`s. -/
def addSets (tac : TSyntax ``tacticSeq) (toSet : Array LocalDecl) :
    m (TSyntax ``tacticSeq × Array (TSyntax `tactic)) := do
  let mut repls := #[]
  for d in toSet do
    let nid := mkIdent d.userName
    repls := repls.push (← `(tactic| set $nid := $nid))
  return (tac.insertMany repls, repls)

/-- adds at the beginning of the tactic sequence `tac` lines like `have new := old`,
where `old` is the username of each local declaration in `toHave`.
It also replaces all `old` names with the `new` ones in `tac`.
These `have`s introduce the "same" local declarations, but inside a metavariable,
creating a layer of separation between the original names of the declarations
and the current ones.  This may help detect missing `instantiateMVars`. -/
def addPropHaves (tac : TSyntax ``tacticSeq) (toHave : Array LocalDecl) :
    m (TSyntax ``tacticSeq × Array (TSyntax `tactic)) := do
  let mut (t1, repls) := (tac, #[])
  for i in [:toHave.size] do
    let decl := toHave[i]!
    let oldId := mkIdent decl.userName
    let str := decl.userName.toString ++ "__"++ decl.userName.toString ++ "__" ++ (toString i)
    -- prefer to `let newId := mkIdent (← mkFreshId)` that also requires `[MonadNameGenerator m]`
    -- just for easier copy/pasting
    let newId : Ident := ⟨.ident .none str str []⟩
    t1 ← t1.replaceM fun s => return if s == oldId then some newId else none
    repls := repls.push (← `(tactic| have $newId := $oldId ))
  t1 ← addDone (t1.insertMany repls)
  return (t1, repls)

end tactic_modifications

def testMData (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := do
  let fin ← addHaveDone tac
  testTactic fin "add 'have := 0'" m!"is mdata correctly handled? {fin}"

open Meta in
def testFVs (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := --Meta.withNewMCtxDepth do
withoutModifyingState do withMainContext do
  let ctx ← getLCtx
  let carr := ctx.fvarIdToDecl.toArray.qsort (·.1.name.toString < ·.1.name.toString)
  let Typ ← inferType (.const ``Nat [])
  let mut typs : HashSet Expr := HashSet.empty.insert Typ
  for (_, d) in carr do
    typs := typs.insert (d.type)
  let nonSort ← carr.filterM fun (_, d) =>
    return d.binderInfo != .instImplicit &&
      d.kind == .default && d.type.ctorName != "sort" && !(← inferType d.type).isProp
--  dbg_trace "nonSort: '{nonSort.map (·.2.userName)}'"
  let toSet := nonSort.map Prod.snd
  let (ntac, repls) ← addSets tac toSet
  testTactic ntac m!"{repls}" m!"missing withContext? {ntac}"

open Meta in
def testInstMVs (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) :=
withoutModifyingState do withMainContext do
  let mut ctx ← getLCtx
--  let mut repls := #[]
  let carr := ctx.fvarIdToDecl.toArray.qsort (·.1.name.toString < ·.1.name.toString)
  let props ← carr.filterM fun d => return d.2.kind == .default && ((← inferType d.2.type).isProp)
  let (t1, _repls) ← addPropHaves tac (props.map Prod.snd)
  testTactic ⟨t1⟩ m!"{indentD t1}" m!"missing instantiateMVars? {t1}"

elab "now " tac:tacticSeq : tactic => do
  logInfo m!"{← testInstMVs tac}"
  evalTactic tac

/--
info: some (missing instantiateMVars?

  have ha__ha__0 := ha
  md_exact ha__ha__0
  done)
---
info: [Tactic.tests] ❌

        have ha__ha__0 := ha
        md_exact ha__ha__0
        done
-/
#guard_msgs in
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
/--
warning: is mdata correctly handled?

  have := 0
  buggy_exact h
  done
---
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact h__h__0
  done
---
info: [Tactic.tests] ❌ add 'have := 0'
[Tactic.tests] ✅ [set j := j]
[Tactic.tests] ❌

        have h__h__0 := h
        buggy_exact h__h__0
        done
-/
#guard_msgs in
example {j : Bool} {h : True} : True := by
  tests buggy_exact h

/--
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact clearMD h__h__0
  done
---
info: [Tactic.tests] ✅ add 'have := 0'
[Tactic.tests] ✅ []
[Tactic.tests] ❌

        have h__h__0 := h
        buggy_exact clearMD h__h__0
        done
-/
#guard_msgs in
example {h : True} : True := by
  tests buggy_exact clearMD h

/--
warning: is mdata correctly handled?

  have := 0
  less_buggy_exact h
  done
---
warning: missing instantiateMVars?

  have h__h__0 := h
  less_buggy_exact h__h__0
  done
---
info: [Tactic.tests] ❌ add 'have := 0'
[Tactic.tests] ✅ []
[Tactic.tests] ❌

        have h__h__0 := h
        less_buggy_exact h__h__0
        done
-/
#guard_msgs in
example {h : True} : True := by
  tests less_buggy_exact h

/--
warning: missing instantiateMVars?

  have h__h__0 := h
  md_exact h__h__0
  done
---
info: [Tactic.tests] ✅ add 'have := 0'
[Tactic.tests] ✅ []
[Tactic.tests] ❌

        have h__h__0 := h
        md_exact h__h__0
        done
-/
#guard_msgs in
example {h : True} : True := by
  tests md_exact h

/--
info: [Tactic.tests] ✅ add 'have := 0'
[Tactic.tests] ✅ [set a := a, set b := b]
[Tactic.tests] ✅

        move_add [← 9]
        move_add [← a]
        rfl
        done
-/
#guard_msgs in
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


/--
info: [Tactic.tests] testing hif
[Tactic.tests] ✅ add 'have := 0'
[Tactic.tests] ✅ [set _n := _n, set _m := _m, set _n := _n, set _m := _m]
[Tactic.tests] ✅

        have _hn___hn__0 := _hn
        exact .intro
        done
-/
#guard_msgs in
test
theorem hif {_n _m : Nat} {_n _m : Int} (_hn : _n + _m = 0) : True := by
  exact .intro

/--
info: [Tactic.tests] testing example
[Tactic.tests] ✅ add 'have := 0'
[Tactic.tests] ✅ []
[Tactic.tests] ✅

        exact .intro
        skip
        done
-/
#guard_msgs in
test
example : True := by
  exact .intro
  skip

/--
warning: goal does not match
-/
-- `goal does not match` --> not dealing with `mdata`?
#guard_msgs in
example {a : Nat} (h : a = 0) : a = 0 := by
  have := 0
  buggy_exact h
  assumption

/--
warning: goal does not match
-/
#guard_msgs in
-- `goal does not match` --> missing `instantiateMVars`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  have h := ha  -- `h` is a metavariable
  clear ha
--  inspect h
  md_exact h
  assumption

/--
warning: hypothesis 'h' not found
-/
#guard_msgs in
-- `hypothesis 'h' not found` --> missing `withMainContext`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  --have := 0
  have h := ha
  clear ha
--  inspect h
  buggy_exact h
  assumption

/--
warning: is mdata correctly handled?

  have := 0
  buggy_exact h
  done
---
warning: missing instantiateMVars?

  have _h2___h2__0 := _h2
  have h__h__1 := h
  buggy_exact h__h__1
  done
---
info: [Tactic.tests] testing example
[Tactic.tests] ❌ add 'have := 0'
[Tactic.tests] ✅ [set j := j]
[Tactic.tests] ❌

        have _h2___h2__0 := _h2
        have h__h__1 := h
        buggy_exact h__h__1
        done
-/
#guard_msgs in
test
example {j : Bool} {_h2 : True} {h : True} : True := by
  buggy_exact h

open Classical in
example {p q : Prop} (h : 1 = 1) (h1 : False) (_hp : p) (_hq : q) : (if p ∧ q then 1 else 0) = 1 := by
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
