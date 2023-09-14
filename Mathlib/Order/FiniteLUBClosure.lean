/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
eleased under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Order.Closure

/-!
# Finite LUB Closure
-/

variable {α : Type*} [Preorder α]

open Finset

def Closed (s : Set α) : Prop := ∀ ⦃t : Finset α⦄, ↑t ⊆ s → ∀ ⦃a : α⦄, IsLUB t a → a ∈ s

def finiteLUBClosure (s : Set α) : Set α :=
  {a | ∃ (t : Finset α), ↑t ⊆ s ∧ IsLUB t a}

lemma subset_finiteLUBClosure {s : Set α} : s ⊆ finiteLUBClosure s :=
λ a ha ↦ ⟨{a}, (Iff.mpr singleton_subset_set_iff ha), (by
  rw [coe_singleton]
  exact isLUB_singleton)⟩

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem IsLUB.union' {a b c : α} {s t : Set α} (hs : IsLUB s a) (ht : IsLUB t b)
    (hc : IsLUB {a, b} c) : IsLUB (s ∪ t) c :=
  ⟨fun _ h =>
    h.casesOn (fun h => (
      (le_trans (mem_upperBounds.mp hs.1 _ h) (mem_upperBounds.mp hc.1 a (Set.mem_insert a {b})))
      )) fun h => (
      (le_trans (mem_upperBounds.mp ht.1 _ h) (mem_upperBounds.mp hc.1 b
        (Set.mem_insert_of_mem a rfl)))
    ),
    fun _ hu => by
      rw [upperBounds_union] at hu
      apply hc.2
      simp only [Set.mem_singleton_iff, upperBounds_insert, upperBounds_singleton,
        Set.mem_inter_iff, Set.mem_Ici]
      exact ⟨hs.2 hu.1, ht.2 hu.2⟩
    ⟩

lemma inductive_step_n2 {s : Set α} {a₁ a₂ a : α} (ha₁ : a₁ ∈ finiteLUBClosure s)
    (ha₂ : a₂ ∈ finiteLUBClosure s) : IsLUB {a₁, a₂} a → a ∈ finiteLUBClosure s := by
  classical
  intro h
  rcases ha₁ with ⟨t₁,⟨ht₁s,ht₁⟩⟩
  rcases ha₂ with ⟨t₂,⟨ht₂s,ht₂⟩⟩
  unfold finiteLUBClosure
  simp
  use (t₁ ∪ t₂)
  constructor
  · rw [coe_union, Set.union_subset_iff]
    exact ⟨ht₁s,ht₂s⟩
  · rw [coe_union]
    apply IsLUB.union' ht₁ ht₂ h

lemma inductive_step {s : Set α} {u : Finset α} {a₁ a : α} (ha₁ : a₁ ∈ finiteLUBClosure s)
    (hu : ↑u ⊆ finiteLUBClosure s) (ha₁u : a₁ ∉ u) : IsLUB (insert a₁ u) a →
    a ∈ finiteLUBClosure s := sorry

/-
theorem Nonempty.cons_induction {α : Type*} {p : ∀ s : Finset α, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃a⦄ (s) (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (nonempty_cons h))
    {s : Finset α} (hs : s.Nonempty) : p s hs := by
-/



#check Finset.induction_on

#check Finset.induction_on'

variable (s : Set α) {u : Finset α} (hu : ↑u ⊆ finiteLUBClosure s) {a : α} (hua : IsLUB u a)

def p (t : Finset α) (_ : t.Nonempty) := ∀ ⦃b : α⦄, IsLUB t b → b ∈ s

#check (p s : ∀ t : Finset α, t.Nonempty → Prop)

--theorem induction_on' {α : Type*} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
--    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=

lemma test (a : α): IsLUB ∅ a := by
  simp only [isLUB_empty_iff]

lemma p_singleton (b : α) : p s {b} (singleton_nonempty _) := by
  unfold p
  intro c hbc
  apply isLUB_singleton


/-
lemma lub_finset'  : ∀ ⦃t : Finset α⦄, ↑t ⊆ finiteLUBClosure s → ∀ ⦃a : α⦄, IsLUB t a
    → a ∈ finiteLUBClosure s := by
  apply (Finset.induction_on' )
-/

/-
lemma lub_finset {s : Set α} {u : Finset α} {a : α} (hu : ↑u ⊆ finiteLUBClosure s)
    : IsLUB u a → a ∈ finiteLUBClosure s := by
  intro h
  apply (Finset.induction_on' u)
-/

/-
@[simp] lemma Closed_finiteLUBClosure {s : Set α} : Closed (finiteLUBClosure s) := by
  unfold Closed
  intro u hts a hta
  unfold finiteLUBClosure
  simp
  use t
  constructor
  · apply
-/

  /-
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  refine' ⟨_, ⟨_, ht.mono $ subset_union_left _ _, _, sup'_union ht hu _⟩,
    le_sup_left, le_sup_right⟩
  rw [coe_union]
  exact Set.union_subset hts hus
  -/

lemma hmin : ∀ ⦃x y : Set α⦄, x ≤ y → Closed y → finiteLUBClosure x ≤ y := by
  intro s₁ s₂ hs hs₂ a has₂
  rcases has₂ with ⟨t,⟨ht1, hr⟩⟩
  exact hs₂ (Set.Subset.trans ht1 hs) hr

lemma Closed_finiteLUBClosure {s : Set α} : Closed (finiteLUBClosure s) := sorry

def finiteLUBClosure' := ClosureOperator.mk₃ (fun (s : Set α) => finiteLUBClosure s) Closed
  (fun _ => subset_finiteLUBClosure) (fun _ => Closed_finiteLUBClosure) hmin


/-
@[simp] lemma directedOn_finiteLUBClosure {s : Set α} : DirectedOn (. ≤ .)
    (finiteLUBClosure s) := by
  classical
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  refine' ⟨_, ⟨_, ht.mono $ subset_union_left _ _, _, sup'_union ht hu _⟩,
    le_sup_left, le_sup_right⟩
  rw [coe_union]
  exact Set.union_subset hts hus
-/
