/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Data.Int.ModEq

/-! # `fin_cases'` tactic

The `fin_cases'` tactic does case disjunction on `e`, where `e : Fin n`, to yield a number of
subgoals in which `e = 0`, ..., `e = n - 1` are assumed.
-/

set_option autoImplicit true

namespace Mathlib.Tactic.FinCases2
open Lean Meta Elab Tactic Term Qq Int

/--
`OnFinCases n a lb p` represents a partial proof by cases that
there exists `0 ≤ z < n` such that `a = z` .
It asserts that if `∃ z, lb ≤ z < n ∧ a = z` holds, then `p`
(where `p` is the current goal).
-/
def OnFinCases' (n : ℕ) (a : Fin n) (lb : ℕ) (p : Sort*) :=
∀ z, lb ≤ z ∧ z < n ∧ a = z → p

/--
The first theorem we apply says that `∃ z, 0 ≤ z < n ∧ a = n`.
The actual mathematical content of the proof is here.
-/
@[inline] def onFinCases_start' (p : Sort*) (n : ℕ) (a : Fin n) (hn : Nat.ble 1 n = true)
    (H : OnFinCases' n a (nat_lit 0) p) : p :=
  H a <| by
    have := ofNat_pos.2 <| Nat.le_of_ble_eq_true hn
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · exact a.2
    · rfl

/--
The end point is that once we have reduced to `∃ z, n ≤ z < n ∧ a = z`
there are no more cases to consider.
-/
@[inline] def onFinCases_stop' (p : Sort*) (n : ℕ) (a : Fin n) : OnFinCases' n a n p :=
  fun _ h => (Nat.not_lt.2 h.1 h.2.1).elim

/--
The successor case decomposes `∃ z, b ≤ z < n ∧ a = z` into
`a = b ∨ ∃ z, b + 1 ≤ z < n ∧ a = z`,
and the `a = b → p` case becomes a subgoal.
-/
@[inline] def onFinCases_succ' {p : Sort*} {n : ℕ} {a : Fin n} (b : ℕ)
    (h : a = b → p) (H : OnFinCases' n a (Nat.add b 1) p) :
    OnFinCases' n a b p :=
  fun z ⟨h₁, h₂⟩ => if e : b = z then h (e ▸ h₂.2) else H _ ⟨Nat.lt_of_le_of_ne h₁ e, h₂⟩

/--
Proves an expression of the form `OnFinCases' n a b p` where `n` and `b` are raw nat literals
and `b ≤ n`. Returns the list of subgoals `?gi : a = i → p`.
-/
partial def proveOnFinCases' (n : Q(ℕ)) (a : Q(Fin $n)) (b : Q(ℕ)) (p : Q(Sort u)) :
    MetaM (Q(OnFinCases' $n $a $b $p) × List MVarId) := do
  if n.natLit! ≤ b.natLit! then
    haveI' : $b =Q $n := ⟨⟩
    pure (q(onFinCases_stop' $p $n $a), [])
  else
    let ty := q($a = $b → $p)
    let g ← mkFreshExprMVarQ ty
    have b1 : Q(ℕ) := mkRawNatLit (b.natLit! + 1)
    haveI' : $b1 =Q ($b).succ := ⟨⟩
    let (pr, acc) ← proveOnFinCases' n a b1 p
    pure (q(onFinCases_succ' $b $g $pr), g.mvarId! :: acc)

/--
* The tactic `fin_cases' h : e` will perform a case disjunction on `e : Fin 3` and yield subgoals
  containing the assumptions `h : e = 0`, `h : e = 1`, `h : e = 2`
  respectively.
* In general, `fin_cases' h : e` works
  when `n` is a positive numeral and `e` is an expression of type `Fin n`.
* If `h` is omitted as in `fin_cases' e`, it will be default-named `h`.
-/
syntax "fin_cases' " (atomic(binderIdent " : "))? term:71 " inFin " num : tactic

elab_rules : tactic
  | `(tactic| fin_cases' $[$h :]? $e inFin $n) => do
    let n := n.getNat
    if n == 0 then Elab.throwUnsupportedSyntax
    let g ← getMainGoal
    g.withContext do
    let ⟨u, p, g⟩ ← inferTypeQ (.mvar g)
    have lit : Q(ℕ) := mkRawNatLit n
    let e : Q(Fin $lit) ← Tactic.elabTermEnsuringType e q(Fin $lit)
    let h := h.getD (← `(binderIdent| _))
    let p₁ : Nat.ble 1 $lit =Q true := ⟨⟩
    let (p₂, gs) ← proveOnFinCases' lit e (mkRawNatLit 0) p
    let gs ← gs.mapM fun g => do
      let (fvar, g) ← match h with
      | `(binderIdent| $n:ident) => g.intro n.getId
      | _ => g.intro `h
      g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
      pure g
    g.mvarId!.assign q(onFinCases_start' $p $lit $e $p₁ $p₂)
    replaceMainGoal gs
