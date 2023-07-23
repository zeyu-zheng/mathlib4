/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term
import Std.Classes.SetNotation
import Mathlib.Mathport.Rename

/-!

# Sets

This file sets up the theory of sets whose elements have a given type.

## Main definitions

Given a type `X` and a predicate `p : X → Prop`:

* `Set X` : the type of sets whose elements have type `X`
* `{a : X | p a} : Set X` : the set of all elements of `X` satisfying `p`
* `{a | p a} : Set X` : a more concise notation for `{a : X | p a}`
* `{a ∈ S | p a} : Set X` : given `S : Set X`, the subset of `S` consisting of
   its elements satisfying `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`

I didn't call this file Data.Set.Basic because it contains core Lean 3
stuff which happens before mathlib3's data.set.basic .
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

-/

structure Set (α : Type u) : Type u where
  /-- Membership in a set -/
  protected Mem : α → Prop
#align set Set

/-- Set of elements satisfying a given predicate. -/
def setOf (p : α → Prop) : Set α := ⟨p⟩
#align set_of setOf

namespace Set

#align set.mem Set.Mem

instance : Membership α (Set α) where
  mem a b := Set.Mem b a

instance : CoeFun (Set α) fun _ ↦ α → Prop where
  coe s x := x ∈ s

@[simp] theorem Mem_eq_mem (s : Set α) : s.Mem = (· ∈ s) := rfl

theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b := by
  cases a; cases b; congr; exact funext fun _ ↦ propext (h _)

protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

/-- Porting note: we introduce `≤` before `⊆` to help the unifier when applying lattice theorems
to subset hypotheses. -/
instance : LE (Set α) :=
  ⟨Set.Subset⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance : EmptyCollection (Set α) :=
  ⟨⟨λ _ => False⟩⟩

open Std.ExtendedBinder in
syntax "{" extBinder " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident ↦ $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t ↦ $p)
  | `({ $x:ident $b:binderPred | $p }) =>
    `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)

@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

open Std.ExtendedBinder in
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | ∃ᵉ $bs:extBinders, $t = x})

/-- The universal set that contains all element of a type. -/
def univ : Set α := {_a | True}
#align set.univ Set.univ

protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a : α) : Set α := {b | b = a}

instance : Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}

instance : Union (Set α) := ⟨Set.union⟩

protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) := ⟨Set.inter⟩

protected def compl (s : Set α) : Set α := {a | a ∉ s}

protected def diff (s t : Set α) : Set α := {a ∈ s | a ∉ t}

instance : SDiff (Set α) := ⟨Set.diff⟩

def powerset (s : Set α) : Set (Set α) := {t | t ⊆ s}

prefix:100 "𝒫" => powerset

def image (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixl:80 " '' " => image

theorem image_id (s : Set α) : id '' s = s :=
  ext fun _ ↦ ⟨λ ⟨_, sb, rfl⟩ => sb, λ sb => ⟨_, sb, rfl⟩⟩
#align set.image_id Set.image_id

theorem image_comp (f : β → γ) (g : α → β) (s : Set α) : (f ∘ g) '' s = f '' (g '' s) :=
  ext fun c =>
    ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     fun ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show f (g a) = c from h₂ ▸ h₃⟩⟩⟩
#align set.image_comp Set.image_comp

instance : Functor Set where map := @Set.image

instance : LawfulFunctor Set where
  id_map := image_id
  comp_map _ _ := image_comp _ _
  map_const := rfl

end Set
