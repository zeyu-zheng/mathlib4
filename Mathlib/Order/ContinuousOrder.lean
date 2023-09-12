import Mathlib.Order.Directed
import Mathlib.Tactic

variable (α : Type*) [Preorder α]

variable {α}

def waybelow (U V : α) : Prop := ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d
  → ∀ ⦃a⦄, IsLUB d a → V ≤ a → ∃ W ∈ d, U ≤ W

local infixl:50 " ⟪ " => waybelow

lemma le_of_waybelow (U V : α) (h : U ⟪ V) : U ≤ V := by
  convert (h (Set.singleton_nonempty V) (directedOn_singleton le_refl _) isLUB_singleton
    (le_refl V))
  constructor
  · intro hUV
    use V
    exact { left := rfl, right := hUV }
  · intro hW
    cases' hW with W hW
    rw [Set.mem_singleton_iff] at hW
    rw [← hW.1]
    exact hW.2
