/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Directed

/-!
# Continuous Orders
-/

variable (α : Type*)

variable {α}

/--
The waybelow relation
-/
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
    exact ⟨rfl, hUV⟩
  · intro hW
    cases' hW with W hW
    rw [Set.mem_singleton_iff] at hW
    rw [← hW.1]
    exact hW.2

lemma waybelow_of_le_waybelow_le (U V W Y : α) (hUV : U ≤ V) (hVW : V ❰ W) (hWY : W ≤ Y) :
    (U ❰ Y) := by
  unfold waybelow
  intro d hd₁ hd₂ a hda hYa
  cases' (hVW hd₁ hd₂ hda (le_trans hWY hYa)) with W hW
  use W
  exact ⟨hW.1, le_trans hUV hW.2⟩

lemma bot_waybelow [OrderBot α] (U : α) : ⊥ ❰ U := by
  intro d hd₁ _ _ _ _
  cases' hd₁ with W hW
  use W
  exact ⟨hW, bot_le⟩

end Preorder
