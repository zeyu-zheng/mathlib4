/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Abel

/-!
# Nimbers

The goal of this file is to define the field of nimbers, constructed as ordinals endowed with new
arithmetical operations. The nim sum `a + b` is recursively defined as the least ordinal not equal
to any `a' + b` or `a + b'` for `a' < a` and `b' < b`. The nim product `a * b` is likewise
recursively defined as the least ordinal not equal to any `a' * b + a * b' + a' * b'` for `a' < a`
and `b' < b`.

Nim addition arises within the context of impartial games. By the Sprague-Grundy theorem, each
impartial game is equivalent to some game of nim. If `x ≈ nim o₁` and `y ≈ nim o₂`, then
`x + y ≈ nim (o₁ + o₂)`, where the ordinals are summed together as nimbers. Unfortunately, the
nim product admits no such characterization.

## Implementation notes

The nimbers inherit the order from the ordinals - this makes working with minimum excluded values
much more convenient. However, the fact that nimbers are of characteristic 2 prevents the order from
interacting with the arithmetic in any nice way.

To reduce API duplication, we opt not to implement operations on `Nimber` on `Ordinal`. The order
isomorphisms `Ordinal.toNimber` and `Nimber.toOrdinal` allow us to cast between them whenever
needed.

## Todo
.
- Show the nimbers are algebraically closed.
-/

universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/


/-- A type synonym for ordinals with natural addition and multiplication. -/
def Nimber : Type _ :=
  Ordinal deriving Zero, Inhabited, One, Nontrivial, WellFoundedRelation

instance Nimber.linearOrder : LinearOrder Nimber := {Ordinal.linearOrder with}
instance Nimber.succOrder : SuccOrder Nimber := {Ordinal.succOrder with}
instance Nimber.orderBot : OrderBot Nimber := {Ordinal.orderBot with}
instance Nimber.noMaxOrder : NoMaxOrder Nimber := {Ordinal.noMaxOrder with}
instance Nimber.zeroLEOneClass : ZeroLEOneClass Nimber := {Ordinal.zeroLEOneClass with}
instance Nimber.NeZero.one : NeZero (1 : Nimber) := Ordinal.NeZero.one

/-- The identity function between `Ordinal` and `Nimber`. -/
@[match_pattern]
def Ordinal.toNimber : Ordinal ≃o Nimber :=
  OrderIso.refl _

/-- The identity function between `Nimber` and `Ordinal`. -/
@[match_pattern]
def Nimber.toOrdinal : Nimber ≃o Ordinal :=
  OrderIso.refl _

namespace Nimber

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : Nimber.toOrdinal.symm = Ordinal.toNimber :=
  rfl

@[simp]
theorem toOrdinal_toNimber (a : Nimber) :
    Ordinal.toNimber (Nimber.toOrdinal a) = a := rfl

theorem lt_wf : @WellFounded Nimber (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT Nimber :=
  Ordinal.wellFoundedLT

instance : IsWellOrder Nimber (· < ·) :=
  { }

instance : ConditionallyCompleteLinearOrderBot Nimber :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
theorem bot_eq_zero : ⊥ = 0 :=
  rfl

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toOrdinal_eq_zero (a) : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toOrdinal_eq_one (a) : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toOrdinal_max {a b : Nimber} : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

@[simp]
theorem toOrdinal_min {a b : Nimber} : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : Nimber) : succ a = toNimber (toOrdinal a + 1) :=
  rfl

/-- A recursor for `Nimber`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : Nimber → Sort*} (h : ∀ a, β (toNimber a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `Nimber`. -/
theorem induction {p : Nimber → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

variable {a : Nimber}

protected theorem le_zero : a ≤ 0 ↔ a = 0 :=
  Ordinal.le_zero

protected theorem not_lt_zero (a : Nimber) : ¬ a < 0 :=
  Ordinal.not_lt_zero a

protected theorem pos_iff_ne_zero : 0 < a ↔ a ≠ 0 :=
  Ordinal.pos_iff_ne_zero

theorem lt_one_iff_zero : a < 1 ↔ a = 0 :=
  Ordinal.lt_one_iff_zero

theorem one_le_iff_pos : 1 ≤ a ↔ 0 < a :=
  Ordinal.one_le_iff_pos

theorem one_le_iff_ne_zero : 1 ≤ a ↔ a ≠ 0 :=
  Ordinal.one_le_iff_ne_zero

end Nimber

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp]
theorem toNimber_symm_eq : toNimber.symm = Nimber.toOrdinal :=
  rfl

@[simp]
theorem toNimber_toOrdinal (a : Ordinal) :  Nimber.toOrdinal (toNimber a) = a :=
  rfl

@[simp]
theorem toNimber_zero : toNimber 0 = 0 :=
  rfl

@[simp]
theorem toNimber_one : toNimber 1 = 1 :=
  rfl

@[simp]
theorem toNimber_eq_zero (a) : toNimber a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNimber_eq_one (a) : toNimber a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toNimber_max (a b : Ordinal) :
    toNimber (max a b) = max (toNimber a) (toNimber b) :=
  rfl

@[simp]
theorem toNimber_min (a b : Ordinal) :
    toNimber (min a b) = min (toNimber a) (toNimber b) :=
  rfl

end Ordinal

/-! ### Nimber addition -/


namespace Nimber

variable {a b c : Nimber.{u}}

/-- Nimber addition is recursively defined so that `a + b` is the smallest nimber not equal to
`a' + b` or `a + b'` for `a' < a` and `b' < b`. -/
-- We write the binders like this so that the termination checker works.
protected def add (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | (∃ a', ∃ (_ : a' < a), Nimber.add a' b = x) ∨
    ∃ b', ∃ (_ : b' < b), Nimber.add a b' = x}ᶜ
termination_by (a, b)

instance : Add Nimber :=
  ⟨Nimber.add⟩

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.add` is nonempty. -/
theorem add_nonempty (a b : Nimber) :
    {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ.Nonempty := by
  use Ordinal.blsub₂ (succ a) (succ b) @fun x _ y _ => Nimber.add x y
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_exists, not_and]
  constructor <;>
  intro x hx <;>
  apply ne_of_lt <;>
  apply Ordinal.lt_blsub₂
  exacts [hx.trans <| lt_succ _, lt_succ _, lt_succ _, hx.trans <| lt_succ _]

theorem exists_of_lt_add (h : c < a + b) : (∃ a' < a, a' + b = c) ∨ ∃ b' < b, a + b' = c := by
  rw [add_def] at h
  have := not_mem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.not_mem_compl_iff] at this

theorem add_le_of_forall_ne (h₁ : ∀ a' < a, a' + b ≠ c) (h₂ : ∀ b' < b, a + b' ≠ c) :
    a + b ≤ c := by
  by_contra! h
  have := exists_of_lt_add h
  tauto

private theorem add_ne_of_lt (a b : Nimber) :
    (∀ a' < a, a' + b ≠ a + b) ∧ ∀ b' < b, a + b' ≠ a + b := by
  have H := csInf_mem (add_nonempty a b)
  rw [← add_def] at H
  simpa using H

instance : IsCancelAdd Nimber where
  add_left_cancel a b c h := by
    apply le_antisymm <;>
    apply le_of_not_lt
    · exact fun hc => (add_ne_of_lt a b).2 c hc h.symm
    · exact fun hb => (add_ne_of_lt a c).2 b hb h
  add_right_cancel a b c h := by
    apply le_antisymm <;>
    apply le_of_not_lt
    · exact fun hc => (add_ne_of_lt a b).1 c hc h.symm
    · exact fun ha => (add_ne_of_lt c b).1 a ha h

-- Ideally the proof would be an easy induction on `add_def`, but rewriting under binders trips up
-- the termination checker.
protected theorem add_comm (a b : Nimber) : a + b = b + a := by
  apply le_antisymm <;>
  apply add_le_of_forall_ne <;>
  intro x hx
  on_goal 1 => rw [Nimber.add_comm x, add_ne_add_right]
  on_goal 2 => rw [Nimber.add_comm a, add_ne_add_left]
  on_goal 3 => rw [← Nimber.add_comm a, add_ne_add_right]
  on_goal 4 => rw [← Nimber.add_comm x, add_ne_add_left]
  all_goals exact hx.ne
termination_by (a, b)

@[simp]
theorem add_eq_zero_iff {a b : Nimber} : a + b = 0 ↔ a = b := by
  constructor <;>
  intro hab
  · obtain h | rfl | h := lt_trichotomy a b
    · have ha : a + a = 0 := add_eq_zero_iff.2 rfl
      rwa [← ha, add_right_inj, eq_comm] at hab
    · rfl
    · have hb : b + b = 0 := add_eq_zero_iff.2 rfl
      rwa [← hb, add_left_inj] at hab
  · rw [← Nimber.le_zero]
    apply add_le_of_forall_ne <;>
    simp_rw [ne_eq] <;>
    intro x hx
    · rw [add_eq_zero_iff, ← hab]
      exact hx.ne
    · rw [add_eq_zero_iff, hab]
      exact hx.ne'
termination_by (a, b)

theorem add_ne_zero_iff : a + b ≠ 0 ↔ a ≠ b :=
  add_eq_zero_iff.not

@[simp]
theorem add_self (a : Nimber) : a + a = 0 :=
  add_eq_zero_iff.2 rfl

protected theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  apply le_antisymm <;>
  apply add_le_of_forall_ne <;>
  intro x hx <;>
  try obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := exists_of_lt_add hx
  on_goal 1 => rw [Nimber.add_assoc y, add_ne_add_left]
  on_goal 2 => rw [Nimber.add_assoc _ y, add_ne_add_right, add_ne_add_left]
  on_goal 3 => rw [Nimber.add_assoc _ _ x, add_ne_add_right, add_ne_add_right]
  on_goal 4 => rw [← Nimber.add_assoc x, add_ne_add_left, add_ne_add_left]
  on_goal 5 => rw [← Nimber.add_assoc _ y, add_ne_add_left, add_ne_add_right]
  on_goal 6 => rw [← Nimber.add_assoc _ _ y, add_ne_add_right]
  all_goals apply ne_of_lt; assumption
termination_by (a, b, c)

protected theorem add_zero (a : Nimber) : a + 0 = a := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    · intro a' ha
      rw [Nimber.add_zero]
      exact ha.ne
    · intro _ h
      exact (Nimber.not_lt_zero _ h).elim
  · -- by_contra! doesn't work for whatever reason.
    by_contra h
    replace h := lt_of_not_le h
    have := Nimber.add_zero (a + 0)
    rw [add_left_inj] at this
    exact this.not_lt h
termination_by a

protected theorem zero_add (a : Nimber) : 0 + a = a := by
  rw [Nimber.add_comm, Nimber.add_zero]

instance : Neg Nimber :=
  ⟨id⟩

@[simp]
protected theorem neg_eq (a : Nimber) : -a = a :=
  rfl

instance : AddCommGroupWithOne Nimber where
  add_assoc := Nimber.add_assoc
  add_zero := Nimber.add_zero
  zero_add := Nimber.zero_add
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := add_self
  add_comm := Nimber.add_comm

@[simp]
protected theorem sub_eq (a b : Nimber) : a - b = a + b :=
  rfl

-- TODO: add CharP 2 instance

@[simp]
theorem two_nsmul (a : Nimber) : 2 • a = 0 := by
  rw [succ_nsmul, one_nsmul, add_self]

theorem two_zsmul (a : Nimber) : (2 : ℤ) • a = 0 :=
  two_nsmul a

theorem add_cancel_right (a b : Nimber) : a + b + b = a := by
  rw [add_assoc, add_self, add_zero]

theorem add_cancel_left (a b : Nimber) : a + (a + b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem add_eq_iff_eq_add : a + b = c ↔ a = c + b :=
  sub_eq_iff_eq_add

theorem eq_add_iff_add_eq : a = b + c ↔ a + c = b :=
  eq_sub_iff_add_eq

theorem add_trichotomy (h : a ≠ b + c) : b + c < a ∨ a + c < b ∨ a + b < c := by
  rw [← add_ne_zero_iff, ← Nimber.pos_iff_ne_zero] at h
  obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add h <;>
  rw [add_eq_zero_iff] at hx'
  · exact Or.inl (hx' ▸ hx)
  · rw [← hx'] at hx
    obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add hx
    · rw [← hx', add_cancel_right]
      exact Or.inr <| Or.inl hx
    · rw [add_comm] at hx'
      rw [← hx', add_cancel_right]
      exact Or.inr <| Or.inr hx

/-! ### Nimber multiplication -/


/-- Nimber multiplication is recursively defined so that `a * b` is the smallest nimber not equal to
`a' * b + a * b' + a' * b'` for `a' < a` and `b' < b`. -/
-- We write the binders like this so that the termination checker works.
protected def mul (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | ∃ a', ∃ (_ : a' < a), ∃ b', ∃ (_ : b' < b),
    Nimber.mul a' b + Nimber.mul a b' + Nimber.mul a' b' = x}ᶜ
termination_by (a, b)

instance : Mul Nimber :=
  ⟨Nimber.mul⟩

theorem mul_def (a b : Nimber) :
    a * b = sInf {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ := by
  change Nimber.mul a b = _
  rw [Nimber.mul]
  simp_rw [exists_prop]
  rfl

open Ordinal in
/-- The set in the definition of `Nimber.mul` is nonempty. -/
theorem mul_nonempty (a b : Nimber) :
    {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ.Nonempty := by
  use Ordinal.blsub₂ a b @fun x _ y _ =>
    toNimber x * b + a * toNimber y + toNimber x * toNimber y
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and]
  intro x hx y hy
  apply ne_of_lt
  exact lt_blsub₂ _ hx hy

theorem exists_of_lt_mul (h : c < a * b) : ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = c := by
  rw [mul_def] at h
  have := not_mem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.not_mem_compl_iff] at this

theorem mul_le_of_forall_ne (h : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ c) :
    a * b ≤ c := by
  by_contra! h'
  have := exists_of_lt_mul h'
  tauto

instance : MulZeroClass Nimber where
  mul_zero a := by
    rw [← Nimber.le_zero]
    apply mul_le_of_forall_ne
    intro _ _ _ h
    exact (Nimber.not_lt_zero _ h).elim
  zero_mul a := by
    rw [← Nimber.le_zero]
    apply mul_le_of_forall_ne
    intro _ h
    exact (Nimber.not_lt_zero _ h).elim

private theorem mul_ne_of_lt : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ a * b := by
  have H := csInf_mem (mul_nonempty a b)
  rw [← mul_def] at H
  simpa using H

instance : NoZeroDivisors Nimber := by
  constructor
  intro a b h
  by_contra! hab
  iterate 2 rw [← Nimber.pos_iff_ne_zero] at hab
  apply (mul_ne_of_lt _ hab.1 _ hab.2).symm
  simpa only [zero_add, mul_zero, zero_mul]

protected theorem mul_comm (a b : Nimber) : a * b = b * a := by
  apply le_antisymm <;>
  apply mul_le_of_forall_ne <;>
  intro x hx y hy
  on_goal 1 => rw [add_comm (x * _), Nimber.mul_comm a, Nimber.mul_comm x b, Nimber.mul_comm x y]
  on_goal 2 => rw [add_comm (x * _), ← Nimber.mul_comm y b, ← Nimber.mul_comm a x,
    ← Nimber.mul_comm y x]
  all_goals exact mul_ne_of_lt y hy x hx
termination_by (a, b)

protected theorem mul_add (a b c : Nimber) : a * (b + c) = a * b + a * c := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro a' ha x hx
    obtain (⟨b', h, rfl⟩ | ⟨c', h, rfl⟩) := exists_of_lt_add hx <;>
    rw [Nimber.mul_add a', Nimber.mul_add a, Nimber.mul_add a']
    on_goal 1 => rw [← add_ne_add_left (a * c)]
    on_goal 2 => rw [← add_ne_add_left (a * b)]
    all_goals
      abel_nf
      simp only [two_zsmul, zero_add]
      rw [← add_assoc]
      exact mul_ne_of_lt _ ha _ h
  · apply add_le_of_forall_ne <;>
    intro x' hx' <;>
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_lt_mul hx'
    · obtain h | h | h := lt_trichotomy (y + c) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_left_injective _ h).elim
      · obtain ⟨z, hz, hz'⟩ | ⟨c', hc, hc'⟩ := exists_of_lt_add h
        · exact ((hz.trans hy).ne <| add_left_injective _ hz').elim
        · have := add_eq_iff_eq_add.1 hc'
          have H := mul_ne_of_lt _ hx _ hc
          rw [← hc', Nimber.mul_add a y c', ← add_ne_add_left (a * y), ← add_ne_add_left (a * c),
            ← add_ne_add_left (a * c'), ← add_eq_iff_eq_add.2 hc', Nimber.mul_add x,
            Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
    · obtain h | h | h := lt_trichotomy (b + y) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_right_injective _ h).elim
      · obtain ⟨b', hb, hb'⟩ | ⟨z, hz, hz'⟩ := exists_of_lt_add h
        · have H := mul_ne_of_lt _ hx _ hb
          have hb'' := add_eq_iff_eq_add.2 (add_comm b c ▸ hb')
          rw [← hb', Nimber.mul_add a b', ← add_ne_add_left (a * y), ← add_ne_add_left (a * b),
            ← add_ne_add_left (a * b'), ← hb'', Nimber.mul_add x, Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
        · exact ((hz.trans hy).ne <| add_right_injective _ hz').elim
termination_by (a, b, c)

protected theorem add_mul (a b c : Nimber) : (a + b) * c = a * c + b * c := by
  rw [Nimber.mul_comm, Nimber.mul_add, Nimber.mul_comm, Nimber.mul_comm b]

protected theorem mul_assoc (a b c : Nimber) : a * b * c = a * (b * c) := by
  apply le_antisymm <;>
  apply mul_le_of_forall_ne <;>
  intro x hx y hy
  · obtain ⟨a', ha, b', hb, rfl⟩ := exists_of_lt_mul hx
    have H : (a + a') * ((b + b') * (c + y)) ≠ 0 := by
      apply mul_ne_zero _ (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [Nimber.mul_assoc]
    rw [← add_ne_add_left (a * (b * c))]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
  · obtain ⟨b', hb, c', hc, rfl⟩ := exists_of_lt_mul hy
    have H : (a + x) * (b + b') * (c + c') ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [← Nimber.mul_assoc]
    rw [← add_ne_add_left (a * b * c)]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
termination_by (a, b, c)

instance : IsCancelMulZero Nimber where
  mul_left_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero_iff, ← Nimber.mul_add, mul_eq_zero] at h
    exact add_eq_zero_iff.1 (h.resolve_left ha)
  mul_right_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero_iff, ← Nimber.add_mul, mul_eq_zero] at h
    exact add_eq_zero_iff.1 (h.resolve_right ha)

protected theorem one_mul (a : Nimber) : 1 * a = a := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro x hx y hy
    rw [Nimber.lt_one_iff_zero] at hx
    rw [hx, Nimber.one_mul, zero_mul, zero_mul, add_zero, zero_add]
    exact hy.ne
  · -- by_contra! doesn't work for whatever reason.
    by_contra h
    replace h := lt_of_not_le h
    exact (mul_left_cancel₀ one_ne_zero <| Nimber.one_mul _).not_lt h
termination_by a

protected theorem mul_one (a : Nimber) : a * 1 = a := by
  rw [Nimber.mul_comm, Nimber.one_mul]

instance : CommRing Nimber where
  left_distrib := Nimber.mul_add
  right_distrib := Nimber.add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := Nimber.mul_assoc
  mul_comm := Nimber.mul_comm
  one_mul := Nimber.one_mul
  mul_one := Nimber.mul_one
  zsmul := zsmulRec
  neg_add_cancel := add_self

instance : IsDomain Nimber :=
  { }

instance : CancelMonoidWithZero Nimber :=
  { }


/-! ### Nimber division -/


/-- The nimber inverse `a⁻¹` is recursively defined as the smallest nimber not in the set `s`, which
itself is recursively defined as the smallest set with `0 ∈ s` and `(1 + (a + a') * b) / a' ∈ s`
for `0 < a' < a` and `b ∈ s`.

This preliminary definition "accidentally" satisfies `inv' 0 = 1`, which the real inverse corrects.
-/
def inv' (a : Nimber) : Nimber :=
  sInf (⋂₀ {s | 0 ∈ s ∧ ∀ a' < a, a' ≠ 0 → ∀ b ∈ s, inv' a' * (1 + (a + a') * b) ∈ s})ᶜ
termination_by a

/-- The (complement of the) set in the definition of `inv' a`. -/
def inv'_set (a : Nimber) : Set Nimber :=
  ⋂₀ {s | 0 ∈ s ∧ ∀ a' < a, a' ≠ 0 → ∀ b ∈ s, inv' a' * (1 + (a + a') * b) ∈ s}

theorem inv'_def (a : Nimber) : inv' a = sInf (inv'_set a)ᶜ := by
  rw [inv']
  rfl

theorem zero_mem_inv'_set (a : Nimber) : 0 ∈ inv'_set a :=
  Set.mem_sInter.2 fun _ hs => hs.1

/-- "cons" is our operation `(1 + (a + a') * b) / a'` in the definition of the inverse. -/
theorem cons_mem_inv'_set {a' : Nimber} (ha₀ : a' ≠ 0) (ha : a' < a) (hb : b ∈ inv'_set a) :
    inv' a' * (1 + (a + a') * b) ∈ inv'_set a :=
  Set.mem_sInter.2 fun _ hs => hs.2 _ ha ha₀ _ (Set.mem_sInter.1 hb _ hs)

/-- A recursion principle for `inv'_set`. -/
@[elab_as_elim]
theorem inv'_recOn (a : Nimber) {p : Nimber → Prop} (h0 : p 0)
    (hi : ∀ a' < a, a' ≠ 0 → ∀ b, p b → p (inv' a' * (1 + (a + a') * b))) {x : Nimber}
    (hx : x ∈ inv'_set a) : p x := by
  revert x
  change inv'_set a ⊆ setOf p
  exact Set.sInter_subset_of_mem ⟨h0, hi⟩

/--- An auxiliary type for enumerating the elements of `inv'_set`, and proving that its complement
is nonempty. -/
private inductive InvTy (a : Nimber.{u}) : Type u
  | zero : InvTy a
  | cons : (toOrdinal a).out.α → InvTy a → InvTy a

/-- An enumeration of elements in the complement of `inv'_set` by a type in the same universe. -/
private def InvTy.toNimber {a : Nimber} : InvTy a → Nimber
  | zero => 0
  | cons x b => let a' := Ordinal.toNimber (Ordinal.typein (α := a.out.α) (· < ·) x)
      inv' a' * (1 + (a + a') * (toNimber b))

/-- The complement of `inv'_set a` is nonempty. -/
theorem inv'_set_nonempty (a : Nimber.{u}) : (inv'_set a)ᶜ.Nonempty := by
  apply Ordinal.nonempty_compl_of_small
  apply @small_subset.{u, u + 1} _ _ _ _ (small_range (@InvTy.toNimber.{u} a))
  intro x hx
  refine inv'_recOn a ⟨InvTy.zero, rfl⟩ ?_ hx
  rintro a' ha _ _ ⟨b, rfl⟩
  rw [← Ordinal.type_lt a] at ha
  use InvTy.cons (Ordinal.enum (α := a.out.α) (· < ·) a' ha) b
  rw [InvTy.toNimber, Ordinal.typein_enum]
  rfl

theorem inv'_ne_zero (a : Nimber) : inv' a ≠ 0 := by
  rw [inv'_def]
  intro h
  exact h ▸ csInf_mem (inv'_set_nonempty a) <| zero_mem_inv'_set a

theorem mem_inv'_set_of_lt_inv' (h : b < inv' a) : b ∈ inv'_set a := by
  rw [inv'_def] at h
  have := not_mem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.not_mem_compl_iff] at this

theorem inv'_not_mem_inv'_set (a : Nimber) : inv' a ∉ inv'_set a := by
  rw [inv'_def]
  exact csInf_mem (inv'_set_nonempty a)

theorem mem_inv'_set_of_inv'_lt (ha : a ≠ 0) (hb : a < b) : inv' a ∈ inv'_set b := by
  have H := cons_mem_inv'_set ha hb (zero_mem_inv'_set b)
  rwa [mul_zero, add_zero, mul_one] at H

private theorem inv'_ne_of_lt (ha : a ≠ 0) (hb : a < b) : inv' a ≠ inv' b :=
  fun h => inv'_not_mem_inv'_set b (h ▸ mem_inv'_set_of_inv'_lt ha hb)

theorem inv'_injective : Set.InjOn inv' {0}ᶜ := by
  intro a ha b hb h
  obtain hab | rfl | hab := lt_trichotomy a b
  · exact (inv'_ne_of_lt ha hab h).elim
  · rfl
  · exact (inv'_ne_of_lt hb hab h.symm).elim

theorem inv'_inj (ha : a ≠ 0) (hb : b ≠ 0) : inv' a = inv' b ↔ a = b :=
  inv'_injective.eq_iff ha hb

/-- We set up a simultaneous induction to prove that `inv' a` is the inverse of `a`, and no element
in its defining set `inv'_set a` is. -/
private theorem main (a : Nimber) : (∀ b ∈ inv'_set a, a * b ≠ 1) ∧ (a ≠ 0 → a * inv' a = 1) := by
  have H₁ : ∀ b ∈ inv'_set a, a * b ≠ 1 := by
    intro b hb
    refine inv'_recOn a ?_ ?_ hb
    · rw [mul_zero]
      exact zero_ne_one
    · intro a' ha ha' b hb
      rw [ne_eq, mul_comm, ← mul_right_inj' ha', ← mul_assoc, ← mul_assoc, (main a').2 ha',
        one_mul, mul_one, add_mul, one_mul, ← add_left_inj a', add_self, mul_assoc, mul_comm b,
        add_assoc, add_comm _ a', ← add_assoc, ← mul_one_add, ← ne_eq, mul_ne_zero_iff,
        add_ne_zero_iff, add_ne_zero_iff]
      use ha.ne', hb.symm
  refine ⟨H₁, fun ha₀ => le_antisymm ?_ ?_⟩
  · apply mul_le_of_forall_ne
    intro a' ha b hb H
    replace hb := mem_inv'_set_of_lt_inv' hb
    rw [add_assoc, ← add_mul, ← eq_add_iff_add_eq] at H
    obtain rfl | ha' := eq_or_ne a' 0
    · rw [zero_mul, add_zero, ← add_eq_iff_eq_add, zero_add] at H
      exact H₁ _ hb H
    · rw [← mul_right_inj' (inv'_ne_zero a'), ← mul_assoc, mul_comm _ a', (main a').2 ha',
        one_mul] at H
      exact inv'_not_mem_inv'_set a (H ▸ cons_mem_inv'_set ha' ha hb)
  · rw [one_le_iff_ne_zero, mul_ne_zero_iff]
    use ha₀, inv'_ne_zero a
termination_by a

theorem mul_inv'_cancel (h : a ≠ 0) : a * inv' a = 1 :=
  (main a).2 h

instance : Inv Nimber :=
  ⟨fun a => if a = 0 then 0 else inv' a⟩

theorem inv_def (ha : a ≠ 0) : a⁻¹ = inv' a :=
  dif_neg ha

protected theorem mul_inv_cancel (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_def ha, mul_inv'_cancel ha]

instance : Field Nimber where
  mul_inv_cancel := @Nimber.mul_inv_cancel
  inv_zero := dif_pos rfl
  nnqsmul := _
  qsmul := _

end Nimber
