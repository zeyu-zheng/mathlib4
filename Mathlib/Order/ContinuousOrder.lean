import Mathlib.Order.Directed
import Mathlib.Tactic

variable (α : Type*)

variable {α}

def waybelow [Preorder α] (U V : α) : Prop := ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d
  → ∀ ⦃a⦄, IsLUB d a → V ≤ a → ∃ W ∈ d, U ≤ W

local infixl:50 " ❰ " => waybelow

section Preorder

variable [Preorder α]

lemma le_of_waybelow (U V : α) (h : U ❰ V) : U ≤ V := by
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

lemma bot_waybelow [OrderBot α] (U : α) : ⊥ ❰ U := by
  unfold waybelow
  intro d hd₁ _ _ _ _
  cases' hd₁ with W hW
  use W
  constructor
  · exact hW
  · exact bot_le

end Preorder
