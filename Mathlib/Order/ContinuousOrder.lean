/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Directed
import Mathlib.Order.Bounds.Basic

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

lemma le_of_waybelow {U V : α} (h : U ❰ V) : U ≤ V := by
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

lemma waybelow_of_le_waybelow_le {U V W Y : α} (hUV : U ≤ V) (hVW : V ❰ W) (hWY : W ≤ Y) :
    (U ❰ Y) := by
  intro d hd₁ hd₂ a hda hYa
  cases' (hVW hd₁ hd₂ hda (le_trans hWY hYa)) with W hW
  use W
  exact ⟨hW.1, le_trans hUV hW.2⟩

@[trans]
lemma waybelow_trans : ∀ {a b c : α}, a ❰ b → b ❰ c → a ❰ c :=
  fun hab hbc => waybelow_of_le_waybelow_le (le_refl _) hab (le_of_waybelow hbc)

lemma bot_waybelow [OrderBot α] (U : α) : ⊥ ❰ U := by
  intro d hd₁ _ _ _ _
  cases' hd₁ with W hW
  use W
  exact ⟨hW, bot_le⟩



end Preorder

lemma waybelow_antisymm [PartialOrder α] : ∀ {a b : α}, a ❰ b → b ❰ a → a = b :=
  fun hab hba => le_antisymm_iff.mpr ⟨le_of_waybelow hab,le_of_waybelow hba⟩

lemma sup_waybelow_of_waybelow_waybelow [SemilatticeSup α] (U V Y : α) (hUY : U ❰ Y) (hVY : V ❰ Y) :
    U ⊔ V ❰ Y := by
  intro d hd₁ hd₂ a hda hYa
  cases' (hUY hd₁ hd₂ hda hYa) with W₁ hW₁
  cases' (hVY hd₁ hd₂ hda hYa) with W₂ hW₂
  cases' (hd₂ W₁ hW₁.1 W₂ hW₂.1) with W hW
  simp only at hW
  use W
  exact ⟨hW.1, (sup_le (le_trans hW₁.2 hW.2.1) (le_trans hW₂.2 hW.2.2))⟩
